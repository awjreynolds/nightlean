#!/usr/bin/env bash
set -euo pipefail

if (( $# != 1 )); then
  echo "usage: bash sdk/web/package.sh NEW_WEB_DIRECTORY" >&2
  exit 2
fi
output=$1
if [[ -e "$output" || -L "$output" ]]; then
  echo "Web package destination already exists: $output" >&2
  exit 1
fi
if [[ $(wasm-bindgen --version) != "wasm-bindgen 0.2.130" ]]; then
  echo "Install wasm-bindgen CLI 0.2.130 to match the locked runtime." >&2
  exit 2
fi
# Use a WebAssembly-capable C toolchain for the pinned BLST dependency.
export CC_wasm32_unknown_unknown="${CC_wasm32_unknown_unknown:-clang}"
export AR_wasm32_unknown_unknown="${AR_wasm32_unknown_unknown:-llvm-ar}"

sdk="$(cd "$(dirname "$0")" && pwd)"
repo="$(cd "$sdk/../.." && pwd)"
parent="$(dirname "$output")"
mkdir -p "$parent"
stage="$(mktemp -d "$parent/.noctium-web.XXXXXX")"
trap 'rm -rf "$stage"' EXIT

wasm="$(cargo +1.100.0 build --locked --profile wasm --lib --manifest-path "$repo/runtime/web/Cargo.toml" \
  --target wasm32-unknown-unknown \
  --message-format=json-render-diagnostics | python3 -c '
import json
import sys

for line in sys.stdin:
    item = json.loads(line)
    if item.get("reason") != "compiler-artifact" or item["target"]["name"] != "noctium_witness_web":
        continue
    for path in item["filenames"]:
        if path.endswith(".wasm"):
            print(path)
')"
[[ -f "$wasm" ]]
wasm-bindgen --target web --out-name noctium_witness --out-dir "$stage" "$wasm"
cp "$repo/LICENSE" "$stage/"
mkdir "$output"
mv "$stage/"* "$output/"
