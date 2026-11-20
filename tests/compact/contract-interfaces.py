from pathlib import Path
import subprocess
import sys
from tempfile import TemporaryDirectory


def main():
    if len(sys.argv) > 2:
        raise SystemExit("usage: python3 contract-interfaces.py [compactc]")
    compiler = sys.argv[1] if len(sys.argv) == 2 else "compactc"
    version = subprocess.check_output([compiler, "--version"], text=True).strip()
    if version.split()[0] != "0.36.1":
        raise SystemExit(f"expected Compact 0.36.1, got {version}")

    fixture = Path(__file__).resolve().with_name("NamedInterface.compact")
    source = fixture.read_text()
    experiments = fixture.parents[2] / "build/experiments"
    experiments.mkdir(parents=True, exist_ok=True)
    cases = [
        ("export circuit readAmount(", "export circuit otherAmount(",
         "does not export a circuit named readAmount"),
        ("readAmount(request: Uint<8>)", "readAmount(request: Uint<16>)",
         "first argument is Uint<8> rather than Uint<16>"),
        ("readPair(payload: [Uint<8>, Boolean])",
         "readPair(amount: Uint<8>, flag: Boolean)",
         "takes 1 arguments rather than 2"),
        ("readPair(payload: [Uint<8>, Boolean]): [Uint<8>, Boolean]",
         "readPair(payload: [Uint<8>, Boolean]): [Boolean, Uint<8>]",
         "return type"),
        ("  circuit readAmount(", "  pure circuit readAmount(",
         "a contract type cannot declare circuit readAmount pure"),
        ("export circuit readAmount(n: Uint<8>): Uint<8> {\n  saved = disclose(n);\n  return saved;",
         "export pure circuit readAmount(n: Uint<8>): Uint<8> {\n  return n;",
         "it is declared pure, and a circuit declared in a contract type must have a proof"),
    ]
    with TemporaryDirectory(prefix="compact-interfaces-", dir=experiments) as scratch:
        scratch = Path(scratch)
        output = scratch / "positive"
        subprocess.run([compiler, "--skip-zk", fixture, output], check=True)
        expected = {"readAmount.zkir", "readPair.zkir"}
        actual = {path.name for path in (output / "zkir").glob("*.zkir")}
        if actual != expected:
            raise SystemExit(f"expected provable scalar and grouped entries, got {sorted(actual)}")

        for i, (original, replacement, diagnostic) in enumerate(cases, start=1):
            if source.count(original) != 1:
                raise SystemExit(f"mutation {i} does not select exactly one interface declaration")
            candidate = scratch / f"case-{i}.compact"
            candidate.write_text(source.replace(original, replacement))
            result = subprocess.run(
                [compiler, "--skip-zk", candidate, scratch / f"negative-{i}"],
                capture_output=True, text=True,
            )
            if result.returncode == 0 or diagnostic not in result.stderr:
                raise SystemExit(f"case {i} expected {diagnostic!r}\n{result.stderr}")

    print(f"Compact {version} emitted two interface relations and rejected {len(cases)} invalid cases")


if __name__ == "__main__":
    main()
