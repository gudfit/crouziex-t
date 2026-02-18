#!/usr/bin/env bash
set -euo pipefail

# Run focused checks without full project build.
# From repository root (where lakefile.toml lives):
#   bash MyProject/Checks/run_crabb_mo3_checks.sh

cd "$(dirname "$0")/../.."
lake env lean MyProject/CrabbShifted.lean
lake env lean MyProject/MO3NonHermitian.lean
lake env lean MyProject/Checks/mo3_nonhermitian_mo_check.lean
