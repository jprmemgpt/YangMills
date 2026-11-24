/-
PROVENANCE: R220 THE-L2b-SQUARE-CAUCHY (Tue 2026-11-24). The fourth of
the seven named windows of the R1 route (YangMills v1.4,
JacobiAnchors.lean) taken to the battery: the square Cauchy product
`routeL2b`,
  theta4z (q * q) ^ 2 = ∑' p : ℤ × ℤ, latS q p   for 0 < q < 1,
proved through the same Mathlib Cauchy lift as R219
(`Summable.tsum_mul_tsum`, the R219 receipt reused verbatim with BOTH
factors the theta-4 family at the doubled nome q*q), with pair
summability by norm domination (`Summable.of_norm_bounded`, the
dominating family summable via `summable_prod_of_nonneg`, the Fubini
twin, here re-proved locally in parameterized form r because the L2
privates do not cross modules), and TWO NEW HEARTS:

PAPER ROUTE (pre-registered in the R1 candidate, executed here):
  theta4z (q*q) ^ 2
  = (∑' a, (−1)^|a| (q·q)^(|a|²)) · (∑' b, (−1)^|b| (q·q)^(|b|²))  [definition, square = product]
  = ∑' (a,b), (−1)^(|a|+|b|) · (q·q)^(|a|²+|b|²)                  [Summable.tsum_mul_tsum; pair summability by norm domination at q·q]
  = ∑' (a,b), (−1)^(|(a+b)|) · q^(2(a²+b²))                       [SIGN PARITY: |a+b| ≡ |a|+|b| (mod 2) — negation preserves parity, omega-closed; NOME: (q·q)^k = q^(2k) by mul_pow, exponent (2·(a²+b²)).toNat = 2|a|²+2|b|²]
  = ∑' p : ℤ×ℤ, latS q p.                                         [the house squared-nome lattice summand]

THE SIGN HEART: (-1)^((a+b).natAbs) = (-1)^(a.natAbs) * (-1)^(b.natAbs)
because parities agree (omega) and a sign of ±1 only knows the parity:
(-1)^n = (-1)^(n % 2) via Nat.div_add_mod + neg_one_sq.
THE NOME HEART: the exponent's first factor of two, normalized by
toNat-of-double = double-of-toNat over the R219 exponent receipt, and
carried (q·q)^k = q^(2k) by mul_pow + pow_add + two_mul.

STATUS: compiled green in-sandbox against the pinned triplet (Mathlib
31ce06eaadf4a200c0e1407c5f10953cf606b8f8, lake 5.0.0, lean v4.37.0-rc1),
with the R219 L2 certificate reproduced green (3,534 jobs) against the
fresh cache before any new math crossed it. The shipping machine
remains the final notary (runbook step 4).

DROP-IN NOTE: with this window green, the hypothesis `h2b : routeL2b`
of `anchorA_of_route` (JacobiAnchors.lean) is discharged by
`routeL2b_proved`; with L1a, L1b and L2 already paid the R1 assembly
rests on SEVEN named windows of which FOUR are proved (L1a, L1b, L2,
L2b) and THREE remain (L3a, L3b, L4) — THE MAJORITY HAS FLIPPED.

SCOPE NOTE: this module certifies THIS ARITHMETIC — one classical Jacobi
theta identity, the square of one integer theta sum born as one
two-dimensional lattice sum at the doubled nome. It proves nothing
about physical four-dimensional Yang–Mills theory and claims no Clay
Millennium result. Bench FROZEN AT 100.0, the crossing never claimed.
-/

import Mathlib.Topology.Algebra.InfiniteSum.Ring
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Analysis.Normed.Group.InfiniteSum
import YangMills.DualBook.JacobiAnchors
import YangMills.DualBook.JacobiAnchorsL1a
import YangMills.DualBook.JacobiAnchorsL1b
import YangMills.DualBook.JacobiAnchorsL2

/-!
# R220: the square Cauchy product (L2b)

The theta-4 family squares against itself at the doubled nome: the
lattice summand `latS q (a, b) = (−1)^|(a+b)| · q^(2(a²+b²))`. Both new
hearts are facts about the sign and the nome: the parity invariance of
negation (`|a+b| ≡ |a|+|b| mod 2`, omega-closed) and the first factor
of two in the exponent.
-/

namespace YangMills.DualBook

open Filter Topology

/-! ## The sign heart: parity -/

/-- A sign of ±1 only knows the parity: `(-1)^n = (-1)^(n % 2)`, by
div-mod decomposition and `neg_one_sq`. -/
private theorem neg_one_pow_mod (n : ℕ) :
    (-1 : ℝ) ^ n = (-1 : ℝ) ^ (n % 2) := by
  rcases Nat.even_or_odd n with ⟨k, hk⟩ | ⟨k, hk⟩
  · rw [show n % 2 = 0 by omega, pow_zero, hk]
    first
    | rw [pow_mul, neg_one_sq, one_pow]
    | rw [show k + k = 2 * k by ring, pow_mul, neg_one_sq, one_pow]
  · rw [show n % 2 = 1 by omega, pow_one, hk, pow_add, pow_one]
    first
    | rw [pow_mul, neg_one_sq, one_pow, one_mul]
    | rw [show k + k = 2 * k by ring, pow_mul, neg_one_sq, one_pow, one_mul]

/-- THE SIGN PARITY: `|a+b|` and `|a|+|b|` differ as numbers, never as
signs — negation preserves parity, omega closes the mod-2 agreement. -/
private theorem sign_par (a b : ℤ) :
    (-1 : ℝ) ^ ((a + b).natAbs)
      = (-1 : ℝ) ^ (a.natAbs) * (-1 : ℝ) ^ (b.natAbs) := by
  have hmod : (a + b).natAbs % 2 = (a.natAbs + b.natAbs) % 2 := by omega
  rw [neg_one_pow_mod, hmod, ← neg_one_pow_mod, pow_add]

/-! ## The nome heart: the exponent's first factor of two -/

/-- The R219 exponent receipt, restated here (the L2 original is
private): `toNat` of a sum of squares is the sum of the squared
`natAbs`s. -/
private theorem sq_sum_exp (a b : ℤ) :
    (a * a + b * b).toNat = a.natAbs ^ 2 + b.natAbs ^ 2 := by
  have h1 : 0 ≤ a * a + b * b := add_nonneg (mul_self_nonneg a) (mul_self_nonneg b)
  apply Nat.cast_injective (R := ℤ)
  rw [Int.toNat_of_nonneg h1, Nat.cast_add, Nat.cast_pow, Nat.cast_pow,
    Int.natAbs_pow_two, Int.natAbs_pow_two]
  ring

/-- `toNat` of a double is the double of the `toNat` (both sides
nonnegative), then the R219 receipt splits the squares. -/
private theorem latS_exp (a b : ℤ) :
    (2 * (a * a + b * b)).toNat = 2 * a.natAbs ^ 2 + 2 * b.natAbs ^ 2 := by
  have hz : 0 ≤ a * a + b * b := add_nonneg (mul_self_nonneg a) (mul_self_nonneg b)
  have h1 : 0 ≤ 2 * (a * a + b * b) := mul_nonneg (by norm_num) hz
  have key : (2 * (a * a + b * b)).toNat = 2 * ((a * a + b * b).toNat) := by
    apply Nat.cast_injective (R := ℤ)
    rw [Int.toNat_of_nonneg h1, Nat.cast_mul, Int.toNat_of_nonneg hz]
    norm_num
  rw [key, sq_sum_exp, mul_add]

/-- The doubled nome carries: `(q · q)^k = q^(2k)` by `mul_pow`,
`pow_add`, `two_mul`. -/
private theorem qq_pow (q : ℝ) (k : ℕ) : (q * q) ^ k = q ^ (2 * k) := by
  rw [mul_pow, ← pow_add, two_mul]

/-- The pointwise congruence: the Cauchy pair product at the doubled
nome IS the house `latS` summand, once the sign marries by parity and
the exponent wears its factor of two. -/
private theorem latS_congr (q : ℝ) (a b : ℤ) :
    latS q (a, b)
      = (-1 : ℝ) ^ (a.natAbs) * (q * q) ^ (a.natAbs ^ 2)
        * ((-1 : ℝ) ^ (b.natAbs) * (q * q) ^ (b.natAbs ^ 2)) := by
  show (-1 : ℝ) ^ ((a + b).natAbs) * q ^ ((2 * (a * a + b * b)).toNat)
      = (-1 : ℝ) ^ (a.natAbs) * (q * q) ^ (a.natAbs ^ 2)
        * ((-1 : ℝ) ^ (b.natAbs) * (q * q) ^ (b.natAbs ^ 2))
  rw [sign_par, latS_exp, pow_add, qq_pow, qq_pow]
  ring

/-! ## Summability of the pair family (the parameterized Fubini twin) -/

/-- The dominating nonnegative lattice family at a general positive
nome r < 1 (the L2 `dom_summable` restated with a parameter, its
private twin not crossing modules): fibers are constant multiples of
the theta-3 family, rows reconstitute theta-3 itself. -/
private theorem dom_summable' {r : ℝ} (hr0 : 0 < r) (hr1 : r < 1) :
    Summable fun p : ℤ × ℤ => r ^ (p.1.natAbs ^ 2) * r ^ (p.2.natAbs ^ 2) := by
  have hF : Summable fun m : ℤ => r ^ (m.natAbs ^ 2) := theta3z_summable hr0 hr1
  have hfib : ∀ m : ℤ, Summable fun n : ℤ =>
      r ^ (m.natAbs ^ 2) * r ^ (n.natAbs ^ 2) :=
    fun m => Summable.mul_left _ hF
  have hrow : Summable fun m : ℤ =>
      ∑' n : ℤ, r ^ (m.natAbs ^ 2) * r ^ (n.natAbs ^ 2) := by
    refine Summable.congr (Summable.mul_right (theta3z r) hF) fun m => ?_
    unfold theta3z
    exact tsum_mul_left.symm
  exact (summable_prod_of_nonneg
    (fun p => mul_nonneg (pow_nonneg hr0.le _) (pow_nonneg hr0.le _))).2 ⟨hfib, hrow⟩

/-- The Cauchy pair family at the doubled nome is summable by norm
domination: the sign carries norm 1 (`abs_neg_one_pow`), both power
factors positive. The family is stated in the pair shape the squared
lift produces, sign first in each factor. -/
private theorem pair_summable' {r : ℝ} (hr0 : 0 < r) (hr1 : r < 1) :
    Summable fun p : ℤ × ℤ =>
      (-1 : ℝ) ^ (p.1.natAbs) * r ^ (p.1.natAbs ^ 2)
        * ((-1 : ℝ) ^ (p.2.natAbs) * r ^ (p.2.natAbs ^ 2)) := by
  refine (dom_summable' hr0 hr1).of_norm_bounded fun p => ?_
  rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_mul,
    abs_neg_one_pow, abs_neg_one_pow, one_mul, one_mul,
    abs_of_pos (pow_pos hr0 _), abs_of_pos (pow_pos hr0 _)]

/-! ## The squared-nome window itself -/

/-- WINDOW L2b, the main identity: the square of the theta-4 integer
constant at the doubled nome is the single `latS` lattice sum. -/
theorem theta4z_sq_latS {q : ℝ} (hq0 : 0 < q) (hq1 : q < 1) :
    theta4z (q * q) ^ 2 = ∑' p : ℤ × ℤ, latS q p := by
  have hr0 : 0 < q * q := mul_pos hq0 hq0
  have hr1 : q * q < 1 := by nlinarith
  have hG : Summable fun z : ℤ =>
      (-1 : ℝ) ^ (z.natAbs) * (q * q) ^ (z.natAbs ^ 2) := theta4z_summable hr0 hr1
  rw [pow_two]
  have hlift := hG.tsum_mul_tsum hG (pair_summable' hr0 hr1)
  refine hlift.trans (tsum_congr fun p => ?_)
  exact (latS_congr q p.1 p.2).symm

/-- WINDOW L2b, PROVED: the square Cauchy product of the R1 route, now
an unconditional theorem. Feed this to `anchorA_of_route` (with
`routeL1a_proved`, `routeL1b_proved`, `routeL2_proved`) to discharge
`h1a`, `h1b`, `h2` and `h2b`: four of the seven named windows paid,
three remaining. -/
theorem routeL2b_proved : routeL2b :=
  fun _ hq0 hq1 => theta4z_sq_latS hq0 hq1

/-- DROP-IN RECEIPT (TYPE-CHECKED HERE): with L1a, L1b, L2 and L2b all
proved, `anchorA_of_route` runs on its remaining THREE named windows
(L3a, L3b, L4) — four of the seven hypotheses discharged by green
modules, the majority flipped, nothing hidden. -/
theorem anchorA_of_route_three_paid (h3a : routeL3a) (h3b : routeL3b)
    (h4 : routeL4) : jacobiAnchorA :=
  anchorA_of_route routeL1a_proved routeL1b_proved routeL2_proved
    routeL2b_proved h3a h3b h4

end YangMills.DualBook
