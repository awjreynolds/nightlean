#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/.."
cli="$PWD/.lake/build/bin/noctium"
scratch="$(mktemp -d)"
trap 'rm -rf "$scratch"' EXIT

reject() {
  local name="$1"
  local fragment="$2"
  if "$cli" compile "$scratch/$name.lean" --output "$scratch/$name-output" > "$scratch/$name-error" 2>&1; then
    echo "unauthorized disclosure compiled: $name" >&2
    exit 1
  fi
  grep -F "$fragment" "$scratch/$name-error" > /dev/null
  test ! -e "$scratch/$name-output"
}

cat > "$scratch/private-data.lean" <<'LEAN'
import Noctium.Frontend
open scoped Noctium
noctium_circuit unauthorized where
  private secret : Native
  output result : Native := secret
end
LEAN
reject private-data "undisclosed private parameter 'secret'"
grep -F 'private-data.lean:4:3' "$scratch/private-data-error" > /dev/null
grep -F 'private-data.lean:5:3' "$scratch/private-data-error" > /dev/null

cat > "$scratch/private-hash.lean" <<'LEAN'
import Noctium.Frontend
open scoped Noctium
noctium_circuit unauthorized where
  private secret : Native
  output digest : Native := poseidon2(1, secret, 0)
end
LEAN
reject private-hash "public output 'digest'"

cat > "$scratch/private-predicate.lean" <<'LEAN'
import Noctium.Frontend
open scoped Noctium
noctium_circuit unauthorized where
  private flag : Bool
  output result : Native := select(flag, 1, 0)
end
LEAN
reject private-predicate "undisclosed private parameter 'flag'"

cat > "$scratch/payload-only.lean" <<'LEAN'
import Noctium.Frontend
open scoped Noctium
noctium_circuit unauthorized where
  private flag : Bool
  output result : Native := select(flag, disclose(1), 0)
end
LEAN
reject payload-only "undisclosed private parameter 'flag'"

cat > "$scratch/unrelated-release.lean" <<'LEAN'
import Noctium.Frontend
open scoped Noctium
noctium_circuit unauthorized where
  private flag : Bool
  let released : Bool := disclose(flag)
  output first : Native := select(released, 1, 0)
  output second : Native := select(flag, 1, 0)
end
LEAN
reject unrelated-release "public output 'second'"

cat > "$scratch/private-query.lean" <<'LEAN'
import Noctium.Frontend
open scoped Noctium
noctium_circuit localRelation where
  private key : Native
end
noctium_contract unauthorized where
  map values : Native => Bool
  entry apply uses localRelation where
    absent values[key]
  end
end
LEAN
reject private-query "public map query path 'values'"

cat > "$scratch/private-write.lean" <<'LEAN'
import Noctium.Frontend
open scoped Noctium
noctium_circuit localRelation where
  private flag : Bool
end
noctium_contract unauthorized where
  cell value : Native
  entry apply uses localRelation where
    write value := select(flag, disclose(1), 0)
  end
end
LEAN
reject private-write "public cell write 'value'"

cat > "$scratch/unsupported-guard.lean" <<'LEAN'
import Noctium.Frontend
open scoped Noctium
noctium_circuit localRelation where
  private flag : Bool
end
noctium_contract unsupported where
  cell value : Native
  entry apply uses localRelation where
    if flag then
      write value := 1
    end
  end
end
LEAN
reject unsupported-guard 'error:'

"$cli" compile examples/Disclosure.lean --output "$scratch/authorized"
node --input-type=module - "$scratch/authorized" <<'JS'
import {readFileSync,readdirSync} from 'node:fs';
import {join} from 'node:path';
import {ok,deepStrictEqual} from 'node:assert/strict';
const directory=process.argv[2];
for(const file of readdirSync(directory))ok(!readFileSync(join(directory,file),'utf8').includes('disclose'));
const metadata=JSON.parse(readFileSync(join(directory,'noctium.json')));
deepStrictEqual(metadata.circuits.length,2);
deepStrictEqual(metadata.circuits[0].outputs[0].expression,{tag:'reference',name:'secret'});
JS
echo 'Disclosure CLI rejection and authorization checks passed'
