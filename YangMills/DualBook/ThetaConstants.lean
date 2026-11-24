/-
PROVENANCE: the dual/Z₂-scaffold exact book (Bucket B, rungs 4-6 of the Lean
priority list), formalized for the YangMills chain (v1.4 target).
Statements, conventions, and certified witness digits follow the printed
"Bucket B Handoff — the Dual-Book Spec for Gemini" (the named source
document), whose content is the certified record of the second bench
(the optimization bench's R69 window, machine-certified at 1e-13, with a
second independent referee route to 2.6e-9). Rungs 1-3 (coset pairing,
homology floor, Z₂ transfer matrix) landed in the v1.3 release; this
module carries the FOUNDATIONS of rung 4.

SCOPE NOTE: this module certifies THIS ARITHMETIC — the absolute
convergence and basic positivity of the Jacobi theta constants in the
corrected convention. It proves nothing about physical
four-dimensional Yang–Mills theory and claims no Clay Millennium result.

## Convention (the corrected one)

For a 4-bit shift label σ with |σ| = number of 1s and q = e^{−πt}
(0 < q < 1), the dual book composites are

  Θ_σ(q) = θ₄^{|σ|}(q) · θ₃^{4−|σ|}(q),

with θ₃(q) = Σ_{n∈ℤ} q^{n²} and θ₄(q) = Σ_{n∈ℤ} (−1)^n q^{n²}.
In Lean we use the symmetrized natural-number forms

  theta3 q = 1 + 2 ∑' n : ℕ, q ^ (n + 1)²
  theta4 q = 1 + 2 ∑' n : ℕ, (−1)^(n + 1) * q ^ (n + 1)²

which define the same functions for 0 < q < 1. The tsum convention makes
both definitions total; every identity of this book is asserted on the
domain 0 < q < 1.

HONEST WINDOW NOTE: the pointwise Jacobi doubling identities
θ₃(q)·θ₄(q) = θ₄(q²)² and θ₃(q)² + θ₄(q)² = 2·θ₃(q²)² (the book's
"Jacobi anchors") are NOT proved in this window; they are carried as
named hypotheses by `YangMills.DualBook.DualBookAssembly`, which proves
the composite laws conditionally on them. Mathlib currently carries only
the complex upper-half-plane `jacobiTheta` family and none of the real
theta constants; rebuilding the q-series doubling proofs in Lean is the
named follow-up window.
-/
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Algebra.Order.GroupWithZero.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Ring
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-!
# The theta constants (rung 4 foundations, corrected convention)

This file defines `theta3` and `theta4` in the symmetrized natural form,
proves absolute convergence of both core series for `0 < q < 1`, and
proves `1 ≤ theta3 q` for `q ≥ 0`.
-/

namespace YangMills.DualBook

/-- The Jacobi theta-3 constant, symmetrized natural form:
`theta3 q = 1 + 2 ∑' n : ℕ, q ^ (n + 1)²`. For `0 < q < 1` this equals
`θ₃(q) = Σ_{n ∈ ℤ} q^{n²}`. The `tsum` convention makes the definition
total; identities are asserted on `0 < q < 1`. -/
noncomputable def theta3 (q : ℝ) : ℝ := 1 + 2 * ∑' n : ℕ, q ^ ((n + 1) ^ 2)

/-- The Jacobi theta-4 constant, symmetrized natural form:
`theta4 q = 1 + 2 ∑' n : ℕ, (−1)^(n + 1) * q ^ (n + 1)²`. For `0 < q < 1`
this equals `θ₄(q) = Σ_{n ∈ ℤ} (−1)^n q^{n²}`. -/
noncomputable def theta4 (q : ℝ) : ℝ :=
  1 + 2 * ∑' n : ℕ, (-1 : ℝ) ^ (n + 1) * q ^ ((n + 1) ^ 2)

/-- Exponent domination: `n + 1 ≤ (n + 1)²` for every natural `n`. This is
the finite comparison that lets the geometric tail dominate the theta
tail for `0 < q < 1`. -/
private theorem succ_le_sq (n : ℕ) : n + 1 ≤ (n + 1) ^ 2 := by
  rw [sq]
  exact Nat.le_mul_self (n + 1)

/-- Absolute convergence of the θ₃ core series for `0 < q < 1`: the tail
is dominated by the shifted geometric series `∑' n, q ^ (n + 1)`. -/
theorem theta3Core_summable {q : ℝ} (hq0 : 0 < q) (hq1 : q < 1) :
    Summable fun n : ℕ => q ^ ((n + 1) ^ 2) := by
  have hg : Summable fun n : ℕ => q ^ (n + 1) := by
    have hgeo : Summable fun n : ℕ => q ^ n :=
      summable_geometric_of_lt_one hq0.le hq1
    exact (hgeo.mul_right q).congr fun n => (pow_succ q n).symm
  refine Summable.of_norm_bounded hg fun n => ?_
  rw [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg hq0.le _)]
  exact pow_le_pow_of_le_one hq0.le hq1.le (succ_le_sq n)

/-- Absolute convergence of the θ₄ core series for `0 < q < 1`: the sign
factor carries norm 1, so the θ₃-core domination applies verbatim. -/
theorem theta4Core_summable {q : ℝ} (hq0 : 0 < q) (hq1 : q < 1) :
    Summable fun n : ℕ => (-1 : ℝ) ^ (n + 1) * q ^ ((n + 1) ^ 2) := by
  refine Summable.of_norm_bounded (theta3Core_summable hq0 hq1) fun i => ?_
  rw [Real.norm_eq_abs, abs_mul, abs_neg_one_pow, one_mul,
    abs_of_nonneg (pow_nonneg hq0.le _)]

/-- Positivity of θ₃: every core term is nonnegative, so `1 ≤ theta3 q`
for all `q ≥ 0` (in particular on the book's domain `0 < q < 1`). -/
theorem theta3_ge_one {q : ℝ} (hq0 : 0 ≤ q) : 1 ≤ theta3 q := by
  have h : 0 ≤ ∑' n : ℕ, q ^ ((n + 1) ^ 2) :=
    tsum_nonneg fun n => pow_nonneg hq0 _
  unfold theta3
  linarith

end YangMills.DualBook
