"""Run the prepared browser witness fixture against the loopback development provider."""

import argparse
import functools
import http.server
import json
import queue
import subprocess
import tempfile
import threading
from pathlib import Path

MAX_REQUEST = 12 * 1024 * 1024
MAX_REPLY = 65 * 1024 * 1024


def stop(process):
    if process.poll() is not None:
        return
    process.terminate()
    try:
        process.wait(timeout=5)
    except subprocess.TimeoutExpired:
        process.kill()
        process.wait(timeout=5)


def qualify(web, provider_path, endpoint, parameters, chrome):
    results = queue.Queue(maxsize=1)
    lock = threading.Lock()
    provider = subprocess.Popen(
        [provider_path, endpoint, parameters], stdin=subprocess.PIPE, stdout=subprocess.PIPE,
    )

    class Handler(http.server.SimpleHTTPRequestHandler):
        def log_message(self, *_args):
            pass

        def do_POST(self):
            origin = f"http://127.0.0.1:{self.server.server_port}"
            if (self.headers.get("Origin") != origin
                    or self.headers.get("Content-Type") != "application/json"):
                self.send_error(403)
                return
            limit = MAX_REQUEST if self.path == "/provider" else 16 * 1024
            if self.path not in {"/provider", "/result"}:
                self.send_error(404)
                return
            try:
                length = int(self.headers.get("Content-Length", "0"))
                if not 0 < length <= limit:
                    raise ValueError("invalid request size")
                body = self.rfile.read(length)
                if len(body) != length or b"\n" in body or b"\r" in body:
                    raise ValueError("expected one JSON line")
                if self.path == "/result":
                    results.put_nowait(json.loads(body))
                    reply = b"{}"
                else:
                    with lock:
                        provider.stdin.write(body + b"\n")
                        provider.stdin.flush()
                        reply = provider.stdout.readline(MAX_REPLY + 1)
                    if not reply.endswith(b"\n") or len(reply) > MAX_REPLY:
                        raise ValueError("invalid provider response")
            except (ValueError, OSError, queue.Full):
                self.send_error(502)
                return
            self.send_response(200)
            self.send_header("Content-Type", "application/json")
            self.send_header("Content-Length", str(len(reply)))
            self.end_headers()
            self.wfile.write(reply)

    try:
        handler = functools.partial(Handler, directory=str(web))
        with http.server.ThreadingHTTPServer(("127.0.0.1", 0), handler) as server:
            thread = threading.Thread(target=server.serve_forever, daemon=True)
            thread.start()
            try:
                url = f"http://127.0.0.1:{server.server_port}/witness-smoke.html?localnet=1&report=1"
                with tempfile.TemporaryDirectory(prefix="noctium-chrome-") as profile:
                    browser = subprocess.Popen(
                        [chrome, "--headless", "--no-first-run", "--disable-background-networking",
                         f"--user-data-dir={profile}", url],
                        stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL,
                    )
                    try:
                        result = results.get(timeout=160)
                    finally:
                        stop(browser)
            finally:
                server.shutdown()
                thread.join()
    finally:
        stop(provider)
        provider.stdin.close()
        provider.stdout.close()
    return result


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--web", required=True, type=Path)
    parser.add_argument("--provider", required=True, type=Path)
    parser.add_argument("--endpoint", required=True)
    parser.add_argument("--parameters", required=True, type=Path)
    parser.add_argument("--chrome", required=True, type=Path)
    args = parser.parse_args()
    result = qualify(args.web, args.provider.resolve(), args.endpoint, args.parameters.resolve(), args.chrome.resolve())
    print(json.dumps(result, indent=2))
    if not result.get("passed") or not result.get("workerRestarted"):
        raise SystemExit(1)


if __name__ == "__main__":
    main()
