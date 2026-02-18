#!/usr/bin/env bash
set -euo pipefail

# Focused numerical MO stress test on shifted Crabb models.
# From repository root:
#   bash MyProject/Checks/run_mo_break_search.sh

cd "$(dirname "$0")/../.."
echo "[1/4] Symbolic strong-MO counterexample check (n=4)..."
python3 MyProject/Checks/mo_assumption_disproof_n4.py
echo ""

echo "[2/4] Aligned-angle numerical MO stress test..."
python3 MyProject/Checks/mo_shifted_crabb_aligned_search.py \
  --n-values 4 5 \
  --theta-samples 361 \
  --trials 2000 \
  --seed 7 \
  --fd-eps 1e-6
echo ""

echo "[3/4] Near-extremal coefficient search (n=4)..."
python3 MyProject/Checks/mo_shifted_crabb_near_extremal_search.py \
  --n 4 \
  --theta-samples 721 \
  --random-iters 4000 \
  --local-iters 1500 \
  --xi-trials 2500 \
  --seed 19 \
  --fd-eps 1e-6
echo ""

echo "[4/4] Broad shifted-Crabb break search..."
python3 MyProject/Checks/mo_shifted_crabb_break_search.py \
  --n-values 3 4 5 \
  --theta-samples 241 \
  --trials-per-theta 250 \
  --seed 42
