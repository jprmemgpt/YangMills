/-
PROVENANCE: R225 the-B2a-WINDOW (Tue 2026-11-24). The first of the five
named windows of the R2 candidate (JacobiAnchorsB.lean) taken to the
battery: the theta-3 square factorization `routeB2a`,
  theta3z q * theta3z q = ∑' p : ℤ × ℤ, latU q p   for 0 < q < 1,
proved through the Mathlib Cauchy lift `Summable.tsum_mul_tsum`
(Topology/Algebra/InfiniteSum/Ring.lean) with pair summability by the
Mathlib Fubini twin `summable_prod_of_nonneg`
(Topology/Algebra/InfiniteSum/Real.lean), and the exponent normalization
`m² + n² ≥ 0 → toNat = the value` (Int.toNat_of_nonneg, with
Int.natAbs_pow_two matching the cast).

THE UNSIGNED TWIN (strictly easier than R219, as pre-registered): the
L2 spine stripped of its sign. In R219 the pair family carried the
theta-4 sign and needed norm domination through Summable.of_norm_bounded;
here NO sign rides, the pair family q^(|m|²) · q^(|n|²) is already
nonnegative, so the Fubini twin admits it DIRECTLY and the norm-domination
layer of the R219 receipt is simply absent — the whole window is the L2
spine with the sign factor deleted and the same explicit exponent chain
(the push_cast-on-natAbs trap that cost R219 a repair avoided by hand,
exactly as the trap record prescribes).

PAPER ROUTE (pre-registered in the R2 candidate, executed here):
  theta3z q * theta3z q
  = (∑' m : ℤ, q^(|m|²)) · (∑' n : ℤ, q^(|n|²))              [definitions; both copies the L1a receipt]
  = ∑' (m,n) : ℤ×ℤ, q^(|m|²) · q^(|n|²)                      [Summable.tsum_mul_tsum; pair family summable, the Fubini twin direct]
  = ∑' p : ℤ × ℤ, latU q p.                                  [pointwise collapse: exponent normalization + pow_add]

DROP-IN NOTE: with this window green, the hypothesis `h2a : routeB2a` of
`anchorB_of_route` (JacobiAnchorsB.lean) is discharged by `routeB2a_proved`;
with the two R1 bridges already paid (L1a, L1b), the R2 assembly rests on
FIVE named windows of which THREE are unconditionally standing (the two
bridges and B2a) and FOUR remain (B2b, B3, B4, B5).

SCOPE NOTE: this module certifies THIS ARITHMETIC — one classical Jacobi
theta identity, the square of the theta-3 integer sum born as the
unsigned two-dimensional lattice sum. It proves nothing about physical
four-dimensional Yang–Mills theory and claims no Clay Millennium result.
Bench FROZEN AT 100.0, the crossing never claimed.
-/

import Mathlib.Topology.Algebra.InfiniteSum.Ring
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Analysis.Normed.Group.InfiniteSum
import YangMills.DualBook.JacobiAnchors
import YangMills.DualBook.JacobiAnchorsL1a
import YangMills.DualBook.JacobiAnchorsL1b
import YangMills.DualBook.JacobiAnchorsB

/-!
# R225: the theta-3 square factorization (B2a)

The first R2 window: the square of the theta-3 integer sum is ONE
lattice sum over `ℤ × ℤ` with no sign anywhere,
`latU q (m, n) = q^(|m² + n²|)`. Summability of both factors is reused
verbatim from the L1a receipt (`theta3z_summable`); the pair family is
summable because it is already the nonnegative dominating family of the
R219 receipt (the Fubini twin needs no norm-domination detour without a
sign to bound); the exponent normalizes because `m² + n²` is already a
nonnegative integer.
-/

namespace YangMills.DualBook

/-! ## The exponent normalization -/

/-- The lattice exponent: `m² + n²` is a nonnegative integer, so its
`toNat` is the value; as a natural number it is exactly `|m|² + |n|²`
(the cast of each square is the square of its `natAbs`). -/
private theorem latU_exp (m n : ℤ) :
    (m * m + n * n).toNat = m.natAbs ^ 2 + n.natAbs ^ 2 := by
  have h1 : 0 ≤ m * m + n * n := add_nonneg (mul_self_nonneg m) (mul_self_nonneg n)
  apply Nat.cast_injective (R := ℤ)
  rw [Int.toNat_of_nonneg h1, Nat.cast_add, Nat.cast_pow, Nat.cast_pow,
    Int.natAbs_pow_two, Int.natAbs_pow_two]
  ring

/-- The pointwise congruence: the Cauchy pair summand IS the house
lattice summand once the exponent is normalized
(`q^(|m|²) · q^(|n|²) = q^(|m|²+|n|²)` by `pow_add`). -/
private theorem latU_congr (q : ℝ) (m n : ℤ) :
    latU q (m, n) = q ^ (m.natAbs ^ 2) * q ^ (n.natAbs ^ 2) := by
  show q ^ ((m * m + n * n).toNat) = q ^ (m.natAbs ^ 2) * q ^ (n.natAbs ^ 2)
  rw [latU_exp m n, pow_add]

/-! ## Summability of the pair family -/

/-- The unsigned pair family `q^(|m|²) · q^(|n|²)` is summable: the
Mathlib Fubini twin `summable_prod_of_nonneg` — each fiber is a constant
multiple of the summable theta-3 family (Summable.mul_left), and the row
sums reconstitute the theta-3 family scaled by `theta3z q` (Summable.congr
with `tsum_mul_left`, which carries NO summability hypothesis). Being
nonnegative, the pair family is its own dominating family and the R219
norm-domination detour is simply absent. -/
private theorem pair_summable {q : ℝ} (hq0 : 0 < q) (hq1 : q < 1) :
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

/-! ## The lattice window itself -/

/-- WINDOW B2a, the main identity: the square of the integer theta
constant is the single unsigned lattice sum over `ℤ × ℤ`. -/
theorem theta3z_mul_theta3z {q : ℝ} (hq0 : 0 < q) (hq1 : q < 1) :
    theta3z q * theta3z q = ∑' p : ℤ × ℤ, latU q p := by
  have hF : Summable fun m : ℤ => q ^ (m.natAbs ^ 2) := theta3z_summable hq0 hq1
  have hlift := hF.tsum_mul_tsum hF (pair_summable hq0 hq1)
  refine hlift.trans (tsum_congr fun p => ?_)
  exact (latU_congr q p.1 p.2).symm

/-- WINDOW B2a, PROVED: the theta-3 square factorization of the R2
route, now an unconditional theorem. Feed this to `anchorB_of_route`
(with `routeL1a_proved` and `routeL1b_proved`) to discharge `h1a`, `h1b`
and `h2a`: three of the seven hypotheses of the anchor-B assembly paid,
four remaining. -/
theorem routeB2a_proved : routeB2a :=
  fun _ hq0 hq1 => theta3z_mul_theta3z hq0 hq1

/-- DROP-IN RECEIPT (TYPE-CHECKED HERE): with the two R1 bridges and B2a
all proved, `anchorB_of_route` runs on its remaining FOUR named windows
(B2b, B3, B4, B5) — three of the seven hypotheses discharged by green
modules, nothing hidden. -/
theorem anchorB_of_route_four_paid (h2b : routeB2b) (h3 : routeB3)
    (h4 : routeB4) (h5 : routeB5) : jacobiAnchorB :=
  anchorB_of_route routeL1a_proved routeL1b_proved routeB2a_proved h2b h3 h4 h5

end YangMills.DualBook
