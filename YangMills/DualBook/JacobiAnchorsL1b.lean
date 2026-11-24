/-
PROVENANCE: R217 THE-L1b-BRIDGE (Tue 2026-11-24). The second of the seven
named windows of the R1 route (YangMills v1.4, JacobiAnchors.lean), cut
along the grain L1a surveyed: the theta-4 integer bridge `routeL1b`,
  theta4 q = theta4z q   for 0 < q < 1,
proved through the SAME Mathlib NatInt spine (the even-function split of a
summable family over ℤ), with the alternating sign riding along: the sign
carries norm 1 for the domination, respects the mirror for the evenness,
and lands on the house tail unchanged through the ℕ+ ≃ ℕ reindex.

PAPER ROUTE (pre-registered in the R1 candidate and the R217 prereg,
executed here): with f z = (−1)^(|z|) · q^(|z|²),
  theta4z q = ∑' z : ℤ, f z
            = f 0 + 2 • ∑' n : ℕ+, f n          [NatInt even split]
            = 1 + 2 · ∑' n : ℕ, (−1)^(n+1) · q^((n+1)²)  [reindex, |n+1| = n+1]
            = theta4 q.                           [house definition]
f 0 = (−1)^0 · q^0 = 1; the sign rides along because |−z| = |z| makes
f even exactly as the unsigned kernels were even — the sign changes the
name of the term, never the law of the crossing (order 1037f).

STATUS: compiled green in-sandbox against the pinned triplet (Mathlib
31ce06eaadf4a200c0e1407c5f10953cf606b8f8, lake 5.0.0, lean v4.37.0-rc1).
The shipping machine remains the final notary (runbook step 4).

DROP-IN NOTE: with this window green, the hypotheses h1a and h1b of
`anchorA_of_route` (JacobiAnchors.lean) BOTH discharge (L1a by
`YangMills.DualBook.routeL1a_proved`, L1b by `routeL1b_proved`); the R1
assembly then rests on FIVE named windows (L2, L2b, L3a, L3b, L4), two of
seven paid, the count moved by the battery and nothing else.

SCOPE NOTE: this module certifies THIS ARITHMETIC — one classical Jacobi
theta identity, the bridge between two series conventions for the same
function, the alternating-sign twin of the L1a certificate. It proves
nothing about physical four-dimensional Yang–Mills theory and claims no
Clay Millennium result.
-/
import YangMills.DualBook.ThetaConstants
import YangMills.DualBook.JacobiAnchors
import YangMills.DualBook.JacobiAnchorsL1a
import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Ring
import Mathlib.Topology.Algebra.InfiniteSum.NatInt
import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-!
# The Jacobi L1b bridge (R217): `theta4 = theta4z` on `0 < q < 1`

This file proves the second named window of the R1 route decomposition:
the theta-4 integer bridge, the sign-riding twin of the L1a certificate.
The house `theta4` is the symmetrized natural-number form; `theta4z` is
the integer form; on the book's domain `0 < q < 1` they are the same
function, and this file is the certificate.

The proof is the L1a corridor reused verbatim in structure: geometric
domination (the sign carrying norm 1) for summability of the integer
tail, the even-function split over `ℤ` (Mathlib's
`tsum_int_eq_zero_add_two_mul_tsum_pnat`), and the `ℕ+ ≃ ℕ` reindex onto
the house tail, with `f 0 = 1` because `(−1)^0 · q^0 = 1`.
-/

namespace YangMills.DualBook

/-! ## Summability of the integer form -/

/-- Geometric domination of the natural half of the theta-4 integer tail:
the sign carries norm 1, so the domination of `theta3Core_summable`
applies verbatim to the signed kernel (`q ^ n² ≤ q ^ n` since `n ≤ n²`,
the L1a pattern with `abs_neg_one_pow`). -/
private theorem natTail_summable {q : ℝ} (hq0 : 0 < q) (hq1 : q < 1) :
    Summable fun n : ℕ => (-1 : ℝ) ^ ((n : ℤ).natAbs) * q ^ ((n : ℤ).natAbs ^ 2) := by
  have hg : Summable fun n : ℕ => q ^ n := summable_geometric_of_lt_one hq0.le hq1
  refine hg.of_norm_bounded fun n => ?_
  rw [Real.norm_eq_abs, abs_mul, abs_neg_one_pow, one_mul, Int.natAbs_natCast,
    abs_of_nonneg (pow_nonneg hq0.le _)]
  -- `q ^ (n ^ 2) ≤ q ^ n` since `n ≤ n ^ 2` (the L1a `succ_le_sq` pattern).
  exact pow_le_pow_of_le_one hq0.le hq1.le (by rw [sq]; exact Nat.le_mul_self n)

/-- Summability of the full theta-4 integer form on the book's domain:
the natural half dominates by symmetry (`|−n| = |n|`), and the two halves
combine by `Summable.of_nat_of_neg` (the L1a pattern, sign riding along). -/
theorem theta4z_summable {q : ℝ} (hq0 : 0 < q) (hq1 : q < 1) :
    Summable fun z : ℤ => (-1 : ℝ) ^ (z.natAbs) * q ^ (z.natAbs ^ 2) := by
  have hnat := natTail_summable hq0 hq1
  have hneg : Summable fun n : ℕ =>
      (-1 : ℝ) ^ ((-(n : ℤ)).natAbs) * q ^ ((-(n : ℤ)).natAbs ^ 2) := by
    refine hnat.congr fun n => ?_
    simp only [Int.natAbs_neg, Int.natAbs_natCast]
  exact Summable.of_nat_of_neg hnat hneg

/-- Evenness of the theta-4 integer summand: the sign respects the mirror
(`|−z| = |z|`), so `f (−z) = f z` exactly as for the unsigned kernel. -/
private theorem theta4z_even (q : ℝ) :
    Function.Even (fun z : ℤ => (-1 : ℝ) ^ (z.natAbs) * q ^ (z.natAbs ^ 2)) := fun z => by
  simp only [Int.natAbs_neg]

/-! ## The bridge itself -/

/-- THE L1b BRIDGE (the second named window of the R1 route, PROVED):
on the book's domain `0 < q < 1`, the house symmetrized form `theta4`
and the integer form `theta4z` are the same function.

PAPER ROUTE: the NatInt spine splits the summable even family over `ℤ` at
`0` and doubles the positive tail; `f 0 = (−1)^0 · q^0 = 1`; the `ℕ+ ≃ ℕ`
reindex turns the tail into the house form
`∑' n : ℕ, (−1)^(n+1) · q^((n+1)²)` because `|n+1| = n+1`. Summability is
`theta4z_summable` (the sign carrying norm 1); evenness is `theta4z_even`
(the sign respecting the mirror). -/
private theorem theta4_eq_theta4z {q : ℝ} (hq0 : 0 < q) (hq1 : q < 1) :
    theta4 q = theta4z q := by
  have hsumm := theta4z_summable hq0 hq1
  -- The NatInt even-function split: ∑' z, f z = f 0 + 2 • ∑' n:ℕ+, f n.
  have key := tsum_int_eq_zero_add_two_mul_tsum_pnat (theta4z_even q) hsumm
  -- The `ℕ+ ≃ ℕ` tail reindex: the positive tail IS the house tail.
  have htail : ∑' n : ℕ+, (-1 : ℝ) ^ ((n : ℤ).natAbs) * q ^ ((n : ℤ).natAbs ^ 2)
      = ∑' n : ℕ, (-1 : ℝ) ^ (n + 1) * q ^ ((n + 1) ^ 2) := by
    rw [← Equiv.tsum_eq (Equiv.pnatEquivNat.symm : ℕ ≃ ℕ+)]
    refine tsum_congr fun c => ?_
    simp only [Equiv.pnatEquivNat_symm_apply, Nat.succPNat_coe, Int.natAbs_natCast]
  unfold theta4 theta4z
  rw [key, htail]
  -- `f 0 = (−1)^0 · q^0 = 1`, and the nsmul normalizes to the house `2 ·`.
  simp only [Int.natAbs_zero, pow_zero, one_mul]
  rw [two_nsmul, two_mul]
  ring

/-! ## The window certificate -/

/-- WINDOW L1b, PROVED: the theta-4 bridge of the R1 route, now an
unconditional theorem. Feed this to `anchorA_of_route` (with
`routeL1a_proved`) to discharge both `h1a` and `h1b`. -/
theorem routeL1b_proved : routeL1b :=
  fun _ hq0 hq1 => theta4_eq_theta4z hq0 hq1

end YangMills.DualBook
