#!/usr/bin/env bash
set -euo pipefail

echo "=== 1. Build Lean 4 formal model, verify all kernel proofs (0 sorry, 0 axioms) ==="
lake build
lake build Percolator.EvilMatcher

echo "=== 2. Compile core Percolator + external Matcher, OracleAdapter, RewardModule & test-only EvilMatcher to Solana sBPF (.so) ==="
mkdir -p build
LEAN_PATH=../lean-svm/.lake/build/lib/lean:.lake/build/lib/lean \
  ../lean-svm/.lake/build/bin/lean-svm build Percolator.Program Percolator.Program.entrypoint -o build/percolator.so
LEAN_PATH=../lean-svm/.lake/build/lib/lean:.lake/build/lib/lean \
  ../lean-svm/.lake/build/bin/lean-svm build Percolator.Matcher Percolator.Matcher.entrypoint -o build/matcher.so
LEAN_PATH=../lean-svm/.lake/build/lib/lean:.lake/build/lib/lean \
  ../lean-svm/.lake/build/bin/lean-svm build Percolator.OracleAdapter Percolator.OracleAdapter.entrypoint -o build/oracle_adapter.so
LEAN_PATH=../lean-svm/.lake/build/lib/lean:.lake/build/lib/lean \
  ../lean-svm/.lake/build/bin/lean-svm build Percolator.RewardModule Percolator.RewardModule.entrypoint -o build/reward_module.so
LEAN_PATH=../lean-svm/.lake/build/lib/lean:.lake/build/lib/lean \
  ../lean-svm/.lake/build/bin/lean-svm build Percolator.EvilMatcher Percolator.EvilMatcher.entrypoint -o build/evil_matcher.so

echo "=== 3. Execute all 14 LiteSVM verification, boring exchange, 8-leg CU stress, reward buy-and-burn, adversarial PropAMM & fuzz suites (Agave 3.1.3) ==="
cargo run --manifest-path svm-runner/Cargo.toml --release -- \
  build/percolator.so build/matcher.so build/oracle_adapter.so build/reward_module.so build/evil_matcher.so
