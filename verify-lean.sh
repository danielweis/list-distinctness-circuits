#!/bin/bash
# Builds the Lean proofs of omega = 9/4 and of "Theorem 2.2" (ManyList) from openai/math
# at the commit cited in the note, prints the axioms they depend on, and then
# checks CircuitLowerBound.lean (the formal circuit lower bound) if it sits next to this script.
# Everything except elan (installed to ~/.elan) stays inside ~/lean-work.
set -euo pipefail
HERE="$(cd "$(dirname "$0")" && pwd)"
W="${LEAN_WORK:-$HOME/lean-work}"; mkdir -p "$W"; cd "$W"
LOG="$W/lean-check.log"
exec > >(tee -a "$LOG") 2>&1
echo "== start $(date)"

if [ ! -x "$HOME/.elan/bin/elan" ] && ! command -v elan >/dev/null 2>&1; then
  curl -sSfL https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh \
    | sh -s -- -y --default-toolchain none
fi
export PATH="$HOME/.elan/bin:$PATH"

if [ ! -d openai-math ]; then
  git clone --filter=blob:none --no-checkout https://github.com/openai/math.git openai-math
  git -C openai-math sparse-checkout set lean
fi
git -C openai-math checkout --detach 3344da59991ed94f9ba711217b29c1d760badfa6
cd openai-math/lean

echo "== fetching prebuilt Mathlib $(date)"
lake exe cache get

echo "== building the two proofs $(date)"
time lake build OAI.LinearAlgebra.SpectralBooks.ExactExponent \
                OAI.LinearAlgebra.MatrixExponent.BatchDescent.Hard

cat > "$W/axioms.lean" <<'EOF'
import OAI.LinearAlgebra.SpectralBooks.ExactExponent
import OAI.LinearAlgebra.MatrixExponent.BatchDescent.Hard
#print axioms OAI.LinearAlgebra.SpectralBooks.square_exponent
#print axioms OAI.LinearAlgebra.MatrixExponent.BatchDescent.manyList
#print axioms OAI.LinearAlgebra.MatrixExponent.BatchDescent.manyList_full
#check @OAI.LinearAlgebra.MatrixExponent.BatchDescent.manyList_full
EOF
echo "== axioms $(date)"
lake env lean "$W/axioms.lean"
if [ -f "$HERE/CircuitLowerBound.lean" ]; then
  echo "== circuit lower bound $(date)"
  lake build Cslib.Computability.Circuit.Complexity \
             Cslib.Computability.Circuit.Full \
             Cslib.Computability.Circuit.Boolean.Complexity \
             Complexity.Computability.Circuit.Boolean.ElementDistinctness
  cp "$HERE/CircuitLowerBound.lean" ./CircuitLowerBound.lean
  lake env lean -o .lake/build/lib/lean/CircuitLowerBound.olean CircuitLowerBound.lean
  echo "== leanchecker --fresh $(date)"
  time lake env leanchecker -v --fresh CircuitLowerBound
fi
echo "== done $(date)"
