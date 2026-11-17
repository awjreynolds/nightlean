# Typed-witness qualification evidence

`qualification-evidence.json` records the finite witness qualification for source
commit `b1afd9f4afa9525a5031820ab7eeaaddbee7e299`. The four canonical bundle
manifests authenticate freshly generated source artifacts and native keys. Their
payloads are reproduced through the pinned compiler/native toolchain, rather
than duplicated in this directory.

`states/` contains the complete public serialized contract states fetched at the
recorded deployment and CALL blocks. Each state matched the independent
observer's length and SHA-256. These records depend on the isolated node's
finality and state reports. They are not consensus light-client proofs.

The Scalar fixture has native proof, deployment, CALL and private journal commit
evidence on both profiles. Pair has runtime/checker, key and bundle evidence.
Unit and empty nominal results have source/runtime checks. Private writes remain
host storage effects. See the [qualification report](../../docs/development/typed-witness-qualification.md)
for exact proof and implementation limits.

Check the retained public bytes from the repository root:

```sh
python3 - <<'PY'
import hashlib, json
from pathlib import Path
base = Path('tests/witness62-public')
record = json.loads((base / 'qualification-evidence.json').read_text())
for entry in record['bundles'] + record['publicStateFiles']:
    data = (base / entry['file']).read_bytes()
    assert hashlib.sha256(data).hexdigest() == entry['sha256']
    if 'bytes' in entry:
        assert len(data) == entry['bytes']
print('All retained public manifests and states match their recorded hashes.')
PY
```
