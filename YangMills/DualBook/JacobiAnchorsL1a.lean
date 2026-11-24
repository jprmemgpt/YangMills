/-
PROVENANCE: R216 THE-L1a-BRIDGE (Tue 2026-11-24). The first of the seven
named windows of the R1 route (YangMills v1.4, JacobiAnchors.lean) taken
to the battery: the theta-3 integer bridge `routeL1a`,
  theta3 q = theta3z q   for 0 < q < 1,
proved through the Mathlib NatInt spine `tsum_int_eq_zero_add_two_mul_tsum_pnat`
(the even-function split of a summable family over ℤ: the value at 0 plus
the doubled positive tail), with summability by geometric domination, the
house pattern of `theta3Core_summable` in ThetaConstants.lean.

PAPER ROUTE (pre-registered in the R1 candidate, executed here):
  theta3z q = ∑' z : ℤ, q ^ (|z|²)
            = 1 + 2 • ∑' n : ℕ+, q ^ (|n|²)      [NatInt even split]
            = 1 + 2 • ∑' n : ℕ, q ^ ((n+1)²)    [PNat ≃ ℕ reindex, |n+1| = n+1]
            = theta3 q.                          [house definition]
Both mirrored tails agree because |−(n+1)|² = (n+1)², which is exactly the
`Function.Even` hypothesis the NatInt split demands.

STATUS: compiled green in-sandbox against the pinned triplet (Mathlib
31ce06eaadf4a200c0e1407c5f10953cf606b8f8, lake 5.0.0, lean v4.37.0-rc1).
The shipping machine remains the final notary (runbook step 4).

DROP-IN NOTE: with this window green, the hypothesis `h1a : routeL1a` of
`anchorA_of_route` (JacobiAnchors.lean) can be discharged by
`routeL1a_proved`; the R1 assembly then rests on SEVEN named windows of
which ONE is proved and six remain.

SCOPE NOTE: this module certifies THIS ARITHMETIC — one classical Jacobi
theta identity, the bridge between two series conventions for the same
function. It proves nothing about physical four-dimensional Yang–Mills
theory and claims no Clay Millennium result.
-/
import YangMills.DualBook.ThetaConstants
import YangMills.DualBook.JacobiAnchors
import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Ring
import Mathlib.Topology.Algebra.InfiniteSum.NatInt
import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-!
# The Jacobi L1a bridge (R216): `theta3 = theta3z` on `0 < q < 1`

This file proves the first named window of the R1 route decomposition:
the theta-3 integer bridge. The house `theta3` is the symmetrized
natural-number form; `theta3z` is the integer form; on the book's domain
`0 < q < 1` they are the same function, and this file is the certificate.

The proof is the pre-registered paper route: geometric domination for
summability of the integer tail, the even-function split over `ℤ`
(Mathlib's `tsum_int_eq_zero_add_two_mul_tsum_pnat`), and the
`ℕ+ ≃ ℕ` reindex onto the house tail.
-/

namespace YangMills.DualBook

/-! ## Summability of the integer form -/

/-- Geometric domination of the natural half of the theta-3 integer tail:
for `0 < q < 1` we have `q ^ n² ≤ q ^ n` because `n ≤ n²` and `0 < q < 1`
(the house pattern of `theta3Core_summable`, with the unshifted geometric
bound). The integer form's natural half is therefore summable. -/
private theorem natTail_summable {q : ℝ} (hq0 : 0 < q) (hq1 : q < 1) :
    Summable fun n : ℕ => q ^ ((n : ℤ).natAbs ^ 2) := by
  have hg : Summable fun n : ℕ => q ^ n := summable_geometric_of_lt_one hq0.le hq1
  refine hg.of_norm_bounded fun n => ?_
  rw [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg hq0.le _), Int.natAbs_natCast]
  -- `q ^ (n ^ 2) ≤ q ^ n` since `n ≤ n ^ 2` (the house `succ_le_sq` pattern).
  exact pow_le_pow_of_le_one hq0.le hq1.le (by rw [sq]; exact Nat.le_mul_self n)

/-- Summability of the full theta-3 integer form on the book's domain:
the natural half dominates by symmetry (`|−n| = |n|`), and the two halves
combine by `Summable.of_nat_of_neg`. -/
theorem theta3z_summable {q : ℝ} (hq0 : 0 < q) (hq1 : q < 1) :
    Summable fun z : ℤ => q ^ (z.natAbs ^ 2) := by
  have hnat := natTail_summable hq0 hq1
  have hneg : Summable fun n : ℕ => q ^ ((-(n : ℤ)).natAbs ^ 2) := by
    refine hnat.congr fun n => ?_
    simp only [Int.natAbs_neg, Int.natAbs_natCast]
  exact Summable.of_nat_of_neg hnat hneg

/-- Evenness of the theta-3 integer summand: `q ^ (|−z|²) = q ^ (|z|²)`. -/
private theorem theta3z_even (q : ℝ) :
    Function.Even (fun z : ℤ => q ^ (z.natAbs ^ 2)) := fun z => by
  simp only [Int.natAbs_neg]

/-! ## The bridge itself -/

/-- THE L1a BRIDGE (the first named window of the R1 route, PROVED):
on the book's domain `0 < q < 1`, the house symmetrized form `theta3`
and the integer form `theta3z` are the same function.

PAPER ROUTE: the Mathlib NatInt spine splits the summable even family over
`ℤ` at `0` and doubles the positive tail;
`∑' z : ℤ, q ^ |z|² = q ^ 0 + 2 • ∑' n : ℕ+, q ^ |n|²`; the `ℕ+ ≃ ℕ`
reindex turns the tail into the house form `∑' n : ℕ, q ^ (n+1)²`,
and `q ^ 0 = 1`. Summability is `theta3z_summable`; evenness is
`theta3z_even`. -/
private theorem theta3_eq_theta3z {q : ℝ} (hq0 : 0 < q) (hq1 : q < 1) :
    theta3 q = theta3z q := by
  have hsumm := theta3z_summable hq0 hq1
  -- The NatInt even-function split: ∑' z, q^|z|² = q^|0|² + 2 • ∑' n:ℕ+, q^|n|².
  have key := tsum_int_eq_zero_add_two_mul_tsum_pnat (theta3z_even q) hsumm
  -- The `ℕ+ ≃ ℕ` tail reindex: the positive tail IS the house tail.
  have htail : ∑' n : ℕ+, q ^ ((n : ℤ).natAbs ^ 2) = ∑' n : ℕ, q ^ ((n + 1) ^ 2) := by
    rw [← Equiv.tsum_eq (Equiv.pnatEquivNat.symm : ℕ ≃ ℕ+)]
    refine tsum_congr fun c => ?_
    simp only [Equiv.pnatEquivNat_symm_apply, Nat.succPNat_coe, Int.natAbs_natCast]
  unfold theta3 theta3z
  rw [key, htail, two_nsmul]
  simp only [Int.natAbs_zero, two_mul]
  ring

/-! ## The window certificate -/

/-- WINDOW L1a, PROVED: the theta-3 bridge of the R1 route, now an
unconditional theorem. Feed this to `anchorA_of_route` to discharge its
`h1a : routeL1a` hypothesis. -/
theorem routeL1a_proved : routeL1a :=
  fun _ hq0 hq1 => theta3_eq_theta3z hq0 hq1

end YangMills.DualBook
