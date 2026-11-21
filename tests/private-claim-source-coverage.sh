#!/usr/bin/env bash
set -euo pipefail

repo_root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
scratch="$(mktemp -d)"
trap 'rm -rf "$scratch"' EXIT
imports="$scratch/imports"
mkdir -p "$imports/examples" "$imports/proofs"
cd "$repo_root"

export LEAN_PATH="$imports"
lake env lean -o "$imports/examples/PrivateClaim.olean" examples/PrivateClaim.lean
lake env lean -o "$imports/proofs/PrivateClaim.olean" proofs/PrivateClaim.lean
lake env lean -o "$imports/proofs/PrivateClaimVerification.olean" proofs/PrivateClaimVerification.lean
lake env lean tests/PrivateClaimSourceCoverage.lean
