#!/usr/bin/env bash
# Run with the repository's pinned Lean toolchain already on PATH. All build
# products, manifests and copied inputs go in one private temporary directory.
set -euo pipefail
pack=$(cd "$(dirname "$0")" && pwd)
root=$(cd "$pack/../.." && pwd)
pin=$(<"$root/lean-toolchain")
if [[ $(lean --version) != "Lean (version ${pin##*:v},"* ]]; then
  printf 'Expected %s already installed on PATH\n' "$pin" >&2
  exit 1
fi
scratch=$(mktemp -d)
trap 'rm -rf -- "$scratch"' EXIT
trap 'exit 130' INT
trap 'exit 143' TERM
cd "$scratch"
mkdir -p Lutar/Covenant Lutar/Wave10 Showcase/WitnessQuorum
cp "$root/Lutar/Covenant/ReceiptChain.lean" Lutar/Covenant/
cp "$root/Lutar/Wave10/QuorumIntersection.lean" Lutar/Wave10/
cp "$root/lean-toolchain" .
cp "$pack"/*.lean Showcase/WitnessQuorum/
cat >lakefile.toml <<'TOML'
name = "witness-quorum-core"
defaultTargets = ["WitnessQuorumShowcase"]
[[lean_lib]]
name = "Lutar"
[[lean_lib]]
name = "WitnessQuorumShowcase"
roots = ["Showcase.WitnessQuorum.ReceiptHistory", "Showcase.WitnessQuorum.HonestOverlap", "Showcase.WitnessQuorum.BoundaryChecks"]
TOML
lake --no-cache --wfail build
