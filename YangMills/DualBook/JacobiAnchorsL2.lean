/-
PROVENANCE: R219 THE-L2-LATTICE (Tue 2026-11-24). The third of the seven
named windows of the R1 route (YangMills v1.4, JacobiAnchors.lean) taken
to the battery: the mixed Cauchy product `routeL2`,
  theta3z q * theta4z q = ∑' p : ℤ × ℤ, latF q p   for 0 < q < 1,
proved through the Mathlib Cauchy lift `Summable.tsum_mul_tsum`
(Topology/Algebra/InfiniteSum/Ring.lean: the product of two summable
families over arbitrary index types equals the sum of the pair family
over the product index), with pair summability by norm domination
through `Summable.of_norm_bounded`, the dominating nonnegative family
q^(|m|²) · q^(|n|²) summable via the Mathlib Fubini twin
`summable_prod_of_nonneg` (InfiniteSum/Real.lean), the sign carrying
norm 1 (`abs_neg_one_pow`, the L1b receipt), and the exponent
normalization `m² + n² ≥ 0 → toNat = the value` (`Int.toNat_of_nonneg`,
with `Int.natAbs_pow_two` matching the cast).

PAPER ROUTE (pre-registered in the R1 candidate, executed here):
  theta3z q * theta4z q
  = (∑' m : ℤ, q^(|m|²)) · (∑' n : ℤ, (−1)^|n| · q^(|n|²))   [definitions]
  = ∑' (m,n) : ℤ×ℤ, q^(|m|²) · ((−1)^|n| · q^(|n|²))          [Summable.tsum_mul_tsum; the pair family summable by norm domination]
  = ∑' (m,n) : ℤ×ℤ, (−1)^|n| · q^(m²+n²)                      [exponent: m²+n² ≥ 0 → toNat = value; q^(|m|²)·q^(|n|²) = q^(|m|²+|n|²); reassociation]
  = ∑' p : ℤ×ℤ, latF q p.                                     [the house lattice summand]

STATUS: compiled green in-sandbox against the pinned triplet (Mathlib
31ce06eaadf4a200c0e1407c5f10953cf606b8f8, lake 5.0.0, lean v4.37.0-rc1).
The shipping machine remains the final notary (runbook step 4).

DROP-IN NOTE: with this window green, the hypothesis `h2 : routeL2` of
`anchorA_of_route` (JacobiAnchors.lean) is discharged by `routeL2_proved`;
with L1a and L1b already paid, the R1 assembly rests on SEVEN named
windows of which THREE are proved (L1a, L1b, L2) and FOUR remain
(L2b, L3a, L3b, L4).

SCOPE NOTE: this module certifies THIS ARITHMETIC — one classical Jacobi
theta identity, the Cauchy product of two one-dimensional theta sums
born as one two-dimensional lattice sum. It proves nothing about physical
four-dimensional Yang–Mills theory and claims no Clay Millennium result.
Bench FROZEN AT 100.0, the crossing never claimed.
-/

import Mathlib.Topology.Algebra.InfiniteSum.Ring
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Analysis.Normed.Group.InfiniteSum
import YangMills.DualBook.JacobiAnchors
import YangMills.DualBook.JacobiAnchorsL1a
import YangMills.DualBook.JacobiAnchorsL1b

/-!
# R219: the mixed Cauchy product (L2)

The two proved bridges meet: the theta-3 integer sum times the theta-4
integer sum is ONE lattice sum over `ℤ × ℤ`, the term carrying the
theta-4 sign in the second coordinate alone,
`latF q (m, n) = (−1)^|n| · q^(m² + n²)`. Summability of both factors is
reused verbatim from the L1a/L1b receipts (`theta3z_summable`,
`theta4z_summable`); the pair family is summable by norm domination,
the sign carrying norm 1; the exponent normalizes because `m² + n²` is
already a nonnegative integer.
-/

namespace YangMills.DualBook

open Filter Topology

/-! ## The exponent normalization -/

/-- The lattice exponent: `m² + n²` is a nonnegative integer, so its
`toNat` is the value; as a natural number it is exactly `|m|² + |n|²`
(the cast of each square is the square of its `natAbs`). -/
private theorem latF_exp (m n : ℤ) :
    (m * m + n * n).toNat = m.natAbs ^ 2 + n.natAbs ^ 2 := by
  have h1 : 0 ≤ m * m + n * n := add_nonneg (mul_self_nonneg m) (mul_self_nonneg n)
  apply Nat.cast_injective (R := ℤ)
  rw [Int.toNat_of_nonneg h1, Nat.cast_add, Nat.cast_pow, Nat.cast_pow,
    Int.natAbs_pow_two, Int.natAbs_pow_two]
  ring

/-- The pointwise congruence: the Cauchy pair summand IS the house
lattice summand once the exponent is normalized
(`q^(|m|²) · q^(|n|²) = q^(|m|²+|n|²)` by `pow_add`). -/
private theorem latF_congr (q : ℝ) (m n : ℤ) :
    latF q (m, n)
      = q ^ (m.natAbs ^ 2) * ((-1 : ℝ) ^ (n.natAbs) * q ^ (n.natAbs ^ 2)) := by
  show (-1 : ℝ) ^ (n.natAbs) * q ^ ((m * m + n * n).toNat)
      = q ^ (m.natAbs ^ 2) * ((-1 : ℝ) ^ (n.natAbs) * q ^ (n.natAbs ^ 2))
  rw [latF_exp m n, pow_add]
  ring

/-! ## Summability of the pair family -/

/-- The dominating nonnegative lattice family `q^(|m|²) · q^(|n|²)` is
summable: the Mathlib Fubini twin `summable_prod_of_nonneg` (each row is
a constant multiple of the summable theta-3 family, and the row sums
reconstitute the theta-3 family scaled by `theta3z q`). -/
private theorem dom_summable {q : ℝ} (hq0 : 0 < q) (hq1 : q < 1) :
    Summable fun p : ℤ × ℤ => q ^ (p.1.natAbs ^ 2) * q ^ (p.2.natAbs ^ 2) := by
  have hF : Summable fun m : ℤ => q ^ (m.natAbs ^ 2) := theta3z_summable hq0 hq1
  have hfib : ∀ m : ℤ, Summable fun n : ℤ =>
      q ^ (m.natAbs ^ 2) * q ^ (n.natAbs ^ 2) :=
    fun m => Summable.mul_left _ hF
  have hrow : Summable fun m : ℤ =>
      ∑' n : ℤ, q ^ (m.natAbs ^ 2) * q ^ (n.natAbs ^ 2) := by
    refine Summable.congr (Summable.mul_right (theta3z q) hF) fun m => ?_
    unfold theta3z
    exact tsum_mul_left.symm
  exact (summable_prod_of_nonneg
    (fun p => mul_nonneg (pow_nonneg hq0.le _) (pow_nonneg hq0.le _))).2 ⟨hfib, hrow⟩

/-- The Cauchy pair family is summable by norm domination: the sign
carries norm 1 (`abs_neg_one_pow`, the L1b receipt), and both power
factors are positive (q > 0), so the norm of each pair term IS the
dominating family. -/
private theorem pair_summable {q : ℝ} (hq0 : 0 < q) (hq1 : q < 1) :
    Summable fun p : ℤ × ℤ =>
      q ^ (p.1.natAbs ^ 2) * ((-1 : ℝ) ^ (p.2.natAbs) * q ^ (p.2.natAbs ^ 2)) := by
  refine (dom_summable hq0 hq1).of_norm_bounded fun p => ?_
  rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_neg_one_pow, one_mul,
    abs_of_pos (pow_pos hq0 _), abs_of_pos (pow_pos hq0 _)]

/-! ## The lattice window itself -/

/-- WINDOW L2, the main identity: the product of the two integer theta
constants is the single lattice sum over `ℤ × ℤ`. -/
theorem theta3z_mul_theta4z {q : ℝ} (hq0 : 0 < q) (hq1 : q < 1) :
    theta3z q * theta4z q = ∑' p : ℤ × ℤ, latF q p := by
  have hF : Summable fun m : ℤ => q ^ (m.natAbs ^ 2) := theta3z_summable hq0 hq1
  have hG : Summable fun n : ℤ =>
      (-1 : ℝ) ^ (n.natAbs) * q ^ (n.natAbs ^ 2) := theta4z_summable hq0 hq1
  have hlift := hF.tsum_mul_tsum hG (pair_summable hq0 hq1)
  refine hlift.trans (tsum_congr fun p => ?_)
  exact (latF_congr q p.1 p.2).symm

/-- WINDOW L2, PROVED: the mixed Cauchy product of the R1 route, now an
unconditional theorem. Feed this to `anchorA_of_route` (with
`routeL1a_proved` and `routeL1b_proved`) to discharge `h1a`, `h1b` and
`h2`: three of the seven named windows paid, four remaining. -/
theorem routeL2_proved : routeL2 :=
  fun _ hq0 hq1 => theta3z_mul_theta4z hq0 hq1

/-- DROP-IN RECEIPT (TYPE-CHECKED HERE): with L1a, L1b and L2 all proved,
`anchorA_of_route` runs on its remaining FOUR named windows (L2b, L3a,
L3b, L4) — three of the seven hypotheses discharged by green modules,
nothing hidden. -/
theorem anchorA_of_route_four_paid (h2b : routeL2b) (h3a : routeL3a)
    (h3b : routeL3b) (h4 : routeL4) : jacobiAnchorA :=
  anchorA_of_route routeL1a_proved routeL1b_proved routeL2_proved h2b h3a h3b h4

end YangMills.DualBook
