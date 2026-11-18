#!/usr/bin/env bash
set -euo pipefail

cd "$(dirname "$0")/../.."
scratch="$(mktemp -d)"
trap 'rm -rf "$scratch"' EXIT
mkdir -p "$scratch/imports/examples" "$scratch/imports/proofs"

lake build Noctium Noctium.Frontend
# Relative source names preserve stable SourceSpan filenames in the declarations.
lake env lean -o "$scratch/imports/examples/PrivateClaim.olean" examples/PrivateClaim.lean

check_proof() {
  local imports="$1"
  shift
  lake env bash -c 'export LEAN_PATH="$1${LEAN_PATH:+:$LEAN_PATH}"; shift; exec lean "$@"' \
    _ "$imports" "$@"
}

check_proof "$scratch/imports" -o "$scratch/imports/proofs/PrivateClaim.olean" proofs/PrivateClaim.lean

# These valid source edits must invalidate the dependent contract proof package.
# They test source binding, rather than merely checking a disconnected model.
python3 - "$scratch" <<'PY'
from pathlib import Path
import sys

root = Path(sys.argv[1])
source = Path('examples/PrivateClaim.lean').read_text()
changes = {
    'missing-root-guard': (
        '    require eq(storedRoot, root)\n', '', 'wrong_root_effects_rejected'),
    'missing-campaign-guard': (
        '    require eq(storedCampaign, campaign)\n', '', 'wrong_campaign_effects_rejected'),
    'wrong-nullifier-domain': (
        'poseidon2(3, secret, campaign)', 'poseidon2(1, secret, campaign)', 'source_constraints'),
    'missing-nullifier-record': (
        '    insert spent[nullifier] := true\n', '', 'effects_accept_unspent'),
    'missing-absence-check': (
        '    absent spent[nullifier]\n', '', 'effects_reject_recorded'),
    'swapped-first-path-direction': (
        '  let left0 : Native := select(direction0, sibling0, leaf)\n'
        '  let right0 : Native := select(direction0, leaf, sibling0)\n',
        '  let left0 : Native := select(direction0, leaf, sibling0)\n'
        '  let right0 : Native := select(direction0, sibling0, leaf)\n', 'source_constraints'),
}
for name, (before, after, clause) in changes.items():
    if source.count(before) != 1:
        raise SystemExit(f'expected one source mutation site: {name}')
    directory = root / name
    (directory / 'imports/examples').mkdir(parents=True)
    (directory / 'source.lean').write_text(source.replace(before, after, 1))
    (directory / 'expected-clause.txt').write_text(clause)
PY

for mutation in missing-root-guard missing-campaign-guard wrong-nullifier-domain \
  missing-nullifier-record missing-absence-check swapped-first-path-direction; do
  directory="$scratch/$mutation"
  lake env lean -o "$directory/imports/examples/PrivateClaim.olean" --stdin examples/PrivateClaim.lean \
    < "$directory/source.lean"
  if check_proof "$directory/imports" proofs/PrivateClaim.lean > "$directory/rejection.log" 2>&1; then
    echo "proof package accepted changed contract: $mutation" >&2
    exit 1
  fi
  python3 - "$directory" "$mutation" <<'PY'
from pathlib import Path
import re
import sys

directory, mutation = Path(sys.argv[1]), sys.argv[2]
expected = (directory / 'expected-clause.txt').read_text()
lines = Path('proofs/PrivateClaim.lean').read_text().splitlines()
declaration = re.compile(
    r'^(?:@\[[^\]]*\]\s*)?(?:(?:private|protected)\s+)?'
    r'(?:theorem|def|structure|inductive|abbrev)\s+([A-Za-z][\w\']*)')
declarations = [(index, match[1]) for index, line in enumerate(lines, start=1)
                if (match := declaration.match(line))]
start = next(index for index, name in declarations if name == expected)
end = next((index for index, _ in declarations if index > start), len(lines) + 1)
log = (directory / 'rejection.log').read_text()
diagnostics = [int(line) for line in re.findall(
    r'^proofs/PrivateClaim\.lean:(\d+):\d+: error(?:\([^\n)]*\))?:', log, re.MULTILINE)]
if not any(start <= line < end for line in diagnostics):
    print(log, file=sys.stderr)
    raise SystemExit(f'{mutation}: expected a proof failure in semantic clause {expected}')
print(f'{mutation}: proof rejected in {expected}')
PY
done

echo 'Actual PrivateClaim source semantic proofs and six source-binding regressions passed'
