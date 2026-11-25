#!/usr/bin/env bash
set -euo pipefail

echo "=== 1. Build Lean 4 formal model, verify all kernel proofs (0 sorry, 0 axioms) ==="
lake build

echo "=== 2. Compile unified Percolator.Program directly to Solana sBPF (.so) ==="
mkdir -p build
lake exe lean-svm build Percolator.Program Percolator.Program.entrypoint -o build/percolator.so

echo "=== 3. Execute full lifecycle & adversarial security suite on LiteSVM (Agave 3.1.3) ==="
cargo run --manifest-path svm-runner/Cargo.toml --release -- build/percolator.so
