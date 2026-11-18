#!/usr/bin/env python3
"""Reject retired project names in tracked filenames and content."""

from pathlib import Path
import re
import subprocess
import sys


root = Path(subprocess.check_output(["git", "rev-parse", "--show-toplevel"]).decode().strip())
paths = subprocess.check_output(["git", "ls-files", "-z"], cwd=root).split(b"\0")
retired = re.compile(rb"n[i]ghtlean|n[i]ghtlyn(e)?|k[n]ightlean", re.IGNORECASE)
failures = []
for raw in filter(None, paths):
    path = root / raw.decode()
    if retired.search(raw):
        failures.append(f"Retired project name in filename: {raw.decode()}")
    if path.is_file() and retired.search(path.read_bytes()):
        failures.append(f"Retired project name in content: {raw.decode()}")

if failures:
    print("\n".join(failures), file=sys.stderr)
    sys.exit(1)
print("Tracked filenames and content use current project branding.")
