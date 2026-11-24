/-
PROVENANCE: R226 THE-B2B-WINDOW (Tue 2026-11-24). The second of the five
named windows of the R2 candidate (JacobiAnchorsB.lean) taken to the
battery: the theta-4 square factorization `routeB2b`,
  theta4z q * theta4z q = ∑' p : ℤ × ℤ, latT q p   for 0 < q < 1,
proved through the Mathlib Cauchy lift `Summable.tsum_mul_tsum`
(Topology/Algebra/InfiniteSum/Ring.lean) with pair summability by norm
domination through `Summable.of_norm_bounded` over the unsigned
dominating family (itself summable by the Mathlib Fubini twin
`summable_prod_of_nonneg`), the sign-carrying norm 1 on BOTH factors
(`abs_mul` splits the fourfold product, `abs_neg_one_pow` kills each
sign factor to 1, `abs_of_pos` strips the two positive powers), and the
exponent normalization `m² + n² ≥ 0 → toNat = the value`
(`Int.toNat_of_nonneg`, `Int.natAbs_pow_two` matching the cast).

THE SIGN-CARRYING TWIN: the R219 L2 spine (JacobiAnchorsL2.lean, the
mixed product with the sign in the SECOND coordinate alone) restored
with the sign in BOTH coordinates, exactly as pre-registered in the R224
candidate doc-string: the pair family is `((-1)^|m| · q^(|m|²)) ·
((-1)^|n| · q^(|n|²))`, its norm is EXACTLY the B2a dominating family
(one more `abs_mul` split and one more `abs_neg_one_pow` kill than the
R219 receipt), and the pointwise collapse carries `pow_add` twice to
join the sign exponents and the q-exponents the same way:
  (-1)^(|m|+|n|) · q^(|m|²+|n|²) = ((-1)^|m| · q^(|m|²)) · ((-1)^|n| · q^(|n|²)).

PAPER ROUTE (pre-registered in the R2 candidate, executed here):
  theta4z q * theta4z q
  = (∑' m : ℤ, (−1)^|m| · q^(|m|²))²                          [definition; the L1b receipt for both factors]
  = ∑' (m,n) : ℤ×ℤ, ((−1)^|m| · q^(|m|²)) · ((−1)^|n| · q^(|n|²))   [Summable.tsum_mul_tsum; pair family summable by norm domination through the Fubini-summable unsigned twin]
  = ∑' (m,n) : ℤ×ℤ, (−1)^(|m|+|n|) · q^(m²+n²)                 [exponent normalization + two pow_adds; reassociation by ring]
  = ∑' p : ℤ × ℤ, latT q p.                                    [the house lattice summand]

DROP-IN NOTE: with this window green, the hypothesis `h2b : routeB2b`
of `anchorB_of_route` (JacobiAnchorsB.lean) is discharged by
`routeB2b_proved`; with the two R1 bridges (L1a, L1b) and B2a already
paid, the R2 assembly rests on FIVE named windows of which FOUR are
unconditionally standing and THREE remain (B3, B4, B5).

SCOPE NOTE: this module certifies THIS ARITHMETIC — one classical
Jacobi theta identity, the square of the theta-4 integer sum born as the
sign-carrying two-dimensional lattice sum. It proves nothing about
physical four-dimensional Yang–Mills theory and claims no Clay
Millennium result. Bench FROZEN AT 100.0, the crossing never claimed.
-/

import Mathlib.Topology.Algebra.InfiniteSum.Ring
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Analysis.Normed.Group.InfiniteSum
import YangMills.DualBook.JacobiAnchors
import YangMills.DualBook.JacobiAnchorsL1a
import YangMills.DualBook.JacobiAnchorsL1b
import YangMills.DualBook.JacobiAnchorsB
import YangMills.DualBook.JacobiAnchorsB2a

/-!
# R226: the theta-4 square factorization (B2b)

The second R2 window: the square of the theta-4 integer sum is ONE
lattice sum over `ℤ × ℤ` with the sign riding in both coordinates,
`latT q (m, n) = (−1)^(|m|+|n|) · q^(|m² + n²|)`. Summability of both
factors is reused verbatim from the L1b receipt (`theta4z_summable`);
the pair family is summable because its norm is EXACTLY the B2a
dominating family (`abs_mul` splits the fourfold product,
`abs_neg_one_pow` kills each sign factor, both powers positive); the
exponent normalizes because `m² + n²` is already a nonnegative integer.
-/

namespace YangMills.DualBook

/-! ## The exponent normalization -/

/-- The lattice exponent: `m² + n²` is a nonnegative integer, so its
`toNat` is the value; as a natural number it is exactly `|m|² + |n|²`
(the cast of each square is the square of its `natAbs`). -/
private theorem latT_exp (m n : ℤ) :
    (m * m + n * n).toNat = m.natAbs ^ 2 + n.natAbs ^ 2 := by
  have h1 : 0 ≤ m * m + n * n := add_nonneg (mul_self_nonneg m) (mul_self_nonneg n)
  apply Nat.cast_injective (R := ℤ)
  rw [Int.toNat_of_nonneg h1, Nat.cast_add, Nat.cast_pow, Nat.cast_pow,
    Int.natAbs_pow_two, Int.natAbs_pow_two]
  ring

/-- The pointwise congruence: the Cauchy pair summand IS the house
lattice summand once the exponent is normalized and BOTH power sums are
joined (`pow_add` on the sign exponent and the q-exponent, then pure
commutative-semiring reassociation). -/
private theorem latT_congr (q : ℝ) (m n : ℤ) :
    latT q (m, n)
      = ((-1 : ℝ) ^ (m.natAbs) * q ^ (m.natAbs ^ 2))
          * ((-1 : ℝ) ^ (n.natAbs) * q ^ (n.natAbs ^ 2)) := by
  show (-1 : ℝ) ^ (m.natAbs + n.natAbs) * q ^ ((m * m + n * n).toNat)
      = ((-1 : ℝ) ^ (m.natAbs) * q ^ (m.natAbs ^ 2))
          * ((-1 : ℝ) ^ (n.natAbs) * q ^ (n.natAbs ^ 2))
  rw [latT_exp m n, pow_add, pow_add]
  ring

/-! ## Summability of the pair family -/

/-- The dominating unsigned lattice family `q^(|m|²) · q^(|n|²)` is
summable: the Mathlib Fubini twin `summable_prod_of_nonneg` — each fiber
is a constant multiple of the summable theta-3 family, and the row sums
reconstitute the theta-3 family scaled by `theta3z q` (the R219/R225
receipt, reused verbatim). -/
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
carries norm 1 on BOTH factors (`abs_neg_one_pow`, the L1b receipt,
twice), and both power factors are positive (q > 0), so the norm of each
pair term is EXACTLY the unsigned dominating family — the R219 receipt
with one more split and one more kill, the pre-registered double-sign
twin. -/
private theorem pair_summable {q : ℝ} (hq0 : 0 < q) (hq1 : q < 1) :
    Summable fun p : ℤ × ℤ =>
      ((-1 : ℝ) ^ (p.1.natAbs) * q ^ (p.1.natAbs ^ 2))
        * ((-1 : ℝ) ^ (p.2.natAbs) * q ^ (p.2.natAbs ^ 2)) := by
  refine (dom_summable hq0 hq1).of_norm_bounded fun p => ?_
  rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_mul, abs_neg_one_pow, abs_neg_one_pow,
    one_mul, one_mul, abs_of_pos (pow_pos hq0 _), abs_of_pos (pow_pos hq0 _)]

/-! ## The lattice window itself -/

/-- WINDOW B2b, the main identity: the square of the theta-4 integer
constant is the single sign-carrying lattice sum over `ℤ × ℤ`. -/
theorem theta4z_mul_theta4z {q : ℝ} (hq0 : 0 < q) (hq1 : q < 1) :
    theta4z q * theta4z q = ∑' p : ℤ × ℤ, latT q p := by
  have hF : Summable fun m : ℤ =>
      (-1 : ℝ) ^ (m.natAbs) * q ^ (m.natAbs ^ 2) := theta4z_summable hq0 hq1
  have hlift := hF.tsum_mul_tsum hF (pair_summable hq0 hq1)
  refine hlift.trans (tsum_congr fun p => ?_)
  exact (latT_congr q p.1 p.2).symm

/-- WINDOW B2b, PROVED: the theta-4 square factorization of the R2
route, now an unconditional theorem. Feed this to `anchorB_of_route`
(with `routeL1a_proved`, `routeL1b_proved` and `routeB2a_proved`) to
discharge `h1a`, `h1b`, `h2a` and `h2b`: four of the seven hypotheses
of the anchor-B assembly paid, three remaining. -/
theorem routeB2b_proved : routeB2b :=
  fun _ hq0 hq1 => theta4z_mul_theta4z hq0 hq1

/-- DROP-IN RECEIPT (TYPE-CHECKED HERE): with the two R1 bridges, B2a
and B2b all proved, `anchorB_of_route` runs on its remaining THREE named
windows (B3, B4, B5) — four of the seven hypotheses discharged by green
modules, nothing hidden. -/
theorem anchorB_of_route_three_paid (h3 : routeB3) (h4 : routeB4)
    (h5 : routeB5) : jacobiAnchorB :=
  anchorB_of_route routeL1a_proved routeL1b_proved routeB2a_proved
    routeB2b_proved h3 h4 h5

end YangMills.DualBook
