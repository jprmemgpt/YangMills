/-
PROVENANCE: the audit entry point for the dual-book rungs 4-6 (Bucket B),
following the repo's own acceptance protocol: every headline theorem of
this build rides a `#print axioms` audit entry here, the build carries
zero `sorry` and zero custom axiom declarations, and numeric witnesses
live only in the bench record (never as proof substitutes).

Toolchain: leanprover/lean4:v4.37.0-rc1 with Mathlib pinned at the
repo's own lake-manifest revision (31ce06ea…).

SCOPE NOTE: this audit certifies THIS ARITHMETIC — the theta-constant
foundations, the conditional Θ_σ assembly laws, the C₀ bracket, the
E-assembly, and the Catalan series' absolute convergence. It certifies
nothing about physical four-dimensional Yang–Mills theory and claims no
Clay Millennium result. The named windows (Jacobi anchors A and B, the
Frullani exponential window, the Catalan gate L(2, χ₋₄) = G, the
Epstein closed forms and the Mellin regularizer) are HYPOTHESES or
statements in the modules and are deliberately NOT audited as theorems.
-/
import YangMills.DualBook.ThetaConstants
import YangMills.DualBook.DualBookAssembly
import YangMills.DualBook.FrullaniBook
import YangMills.DualBook.CatalanGate

/-!
# The dual-book audit (rungs 4-6): axiom printouts for every headline theorem
-/

namespace YangMills.DualBook

-- Rung 4 (theta foundations):
#print axioms theta3Core_summable
#print axioms theta4Core_summable
#print axioms theta3_ge_one

-- Rung 5 (conditional assembly laws):
#print axioms theta_1100_of_anchor
#print axioms theta_sum_D1'

-- Rung 6 (Frullani book):
#print axioms c0_bracket
#print axioms E_assembly

-- Rung 6 companion (Catalan gate):
#print axioms leTwoChiMinusFour_summable
#print axioms catalanCore_summable

end YangMills.DualBook
