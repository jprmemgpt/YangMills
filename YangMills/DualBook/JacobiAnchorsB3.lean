/-
PROVENANCE: R227 THE-B3-PARITY-MERGE (Tue 2026-11-24). The third of
the five named windows of the R2 candidate (JacobiAnchorsB.lean) taken
to the battery: the parity merge `routeB3`,
  (∑' p : ℤ × ℤ, latU q p) + ∑' p : ℤ × ℤ, latT q p
    = 2 * ∑' p : SamePar, latU q p.1   for 0 < q < 1,
the second of the theta-square windows: the unsigned lattice (`latU`,
the theta-3 square book of B2a) and the sign-carrying lattice (`latT`,
the theta-4 square book of B2b) merge pointwise into TWICE the
same-parity sublattice sum.

PAPER ROUTE (pre-registered in the R2 candidate, executed here):
  (∑' latU) + (∑' latT)
  = ∑' (latU + latT)              [Summable.tsum_add; both summable —
                                   latU by the B2a pair-family congr,
                                   latT by norm domination, |latT| = latU]
  = even-slice + odd-slice        [the R221 pointwise indicator split
                                   + tsum_subtype mating, rebuilt for
                                   the merged family]
  = (2 * ∑' SamePar latU) + 0     [merged_even: sign +1 on the even
                                   shell, the bracket doubles;
                                   merged_odd: sign −1 on the odd shell
                                   (the natAbs parity bridge, omega),
                                   the bracket dies — NO INVOLUTION this
                                   time, the merge itself kills the odd
                                   shell]

THE MERGE AGAINST THE INVOLUTION: L3b killed the odd shell by the
(u,v) ↔ (v,u) involution; here the two square books ARE the involution —
pointwise addition of the unsigned and signed summands cancels the odd
shell and doubles the even one before any reindex.

SCOPE NOTE: this module certifies THIS ARITHMETIC, one classical
Jacobi theta identity — the parity-merge step of the second anchor's
decomposition. It proves nothing about physical four-dimensional
Yang–Mills theory and claims no Clay Millennium result. Bench FROZEN
AT 100.0, the crossing never claimed.
-/
import Mathlib.Topology.Algebra.InfiniteSum.Ring
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Analysis.Normed.Group.InfiniteSum
import YangMills.DualBook.JacobiAnchors
import YangMills.DualBook.JacobiAnchorsL1a
import YangMills.DualBook.JacobiAnchorsL1b
import YangMills.DualBook.JacobiAnchorsB
import YangMills.DualBook.JacobiAnchorsB2a
import YangMills.DualBook.JacobiAnchorsB2b

/-!
# R227: the parity merge (B3)

The third R2 window: the unsigned and sign-carrying lattice sums add to
TWICE the same-parity sublattice sum. Summability of both families rides
the B2a pair-family receipt; the split rides the R221 indicator split;
the shell verdicts ride the L2b sign-parity receipts.
-/

namespace YangMills.DualBook

/-! ## The exponent normalization (B2a receipts, restated) -/

/-- The lattice exponent: `m² + n²` is a nonnegative integer, so its
`toNat` is the value; as a natural number it is exactly `|m|² + |n|²`. -/
private theorem latU_exp (m n : ℤ) :
    (m * m + n * n).toNat = m.natAbs ^ 2 + n.natAbs ^ 2 := by
  have h1 : 0 ≤ m * m + n * n := add_nonneg (mul_self_nonneg m) (mul_self_nonneg n)
  apply Nat.cast_injective (R := ℤ)
  rw [Int.toNat_of_nonneg h1, Nat.cast_add, Nat.cast_pow, Nat.cast_pow,
    Int.natAbs_pow_two, Int.natAbs_pow_two]
  ring

/-- The pointwise congruence: the Cauchy pair summand IS the house
lattice summand once the exponent is normalized. -/
private theorem latU_congr (q : ℝ) (m n : ℤ) :
    latU q (m, n) = q ^ (m.natAbs ^ 2) * q ^ (n.natAbs ^ 2) := by
  show q ^ ((m * m + n * n).toNat) = q ^ (m.natAbs ^ 2) * q ^ (n.natAbs ^ 2)
  rw [latU_exp m n, pow_add]

/-- The unsigned pair family is summable: the Fubini twin `summable_prod_of_nonneg`,
each fiber a constant multiple of the summable theta-3 family (the B2a receipt). -/
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

/-! ## Summability of the two square books -/

/-- The unsigned lattice family is summable — the B2a pair family in
house dress. -/
private theorem latU_summable {q : ℝ} (hq0 : 0 < q) (hq1 : q < 1) :
    Summable (latU q) :=
  (pair_summable hq0 hq1).congr fun p => (latU_congr q p.1 p.2).symm

/-- The sign carries norm one and the power is nonnegative with it:
in absolute value the signed summand EQUALS the unsigned one. -/
private theorem abs_latT {q : ℝ} (hq0 : 0 < q) (p : ℤ × ℤ) :
    |latT q p| = latU q p := by
  show |(-1 : ℝ) ^ (p.1.natAbs + p.2.natAbs) * q ^ ((p.1 * p.1 + p.2 * p.2).toNat)|
      = q ^ ((p.1 * p.1 + p.2 * p.2).toNat)
  rw [abs_mul, abs_neg_one_pow, one_mul,
    abs_of_nonneg (pow_nonneg hq0.le _)]

/-- The unsigned summand is its own absolute value. -/
private theorem abs_latU {q : ℝ} (hq0 : 0 < q) (p : ℤ × ℤ) :
    |latU q p| = latU q p :=
  abs_of_nonneg (pow_nonneg hq0.le _)

/-- The sign-carrying family is summable BY NORM DOMINATION: `|latT| =
latU` exactly, so the unsigned book certifies its twin. -/
private theorem latT_summable {q : ℝ} (hq0 : 0 < q) (hq1 : q < 1) :
    Summable (latT q) :=
  (latU_summable hq0 hq1).of_norm_bounded fun p => le_of_eq (abs_latT hq0 p)

/-! ## The sign heart (L2b receipts, restated) -/

/-- A sign of ±1 only knows the parity: `(-1)^n = (-1)^(n % 2)`. -/
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

/-- The signed summand IS the sign times the unsigned one. -/
private theorem latT_scale (q : ℝ) (m n : ℤ) :
    latT q (m, n) = (-1 : ℝ) ^ (m.natAbs + n.natAbs) * latU q (m, n) := rfl

/-! ## The pointwise shell verdicts -/

/-- On the same-parity shell the sign is +1: the two books add to
TWICE the unsigned summand. -/
private theorem merged_even (q : ℝ) (x : SamePar) :
    latU q x.1 + latT q x.1 = 2 * latU q x.1 := by
  have h0 : (x.1.1 + x.1.2) % 2 = 0 := x.2
  show latU q (x.1.1, x.1.2) + latT q (x.1.1, x.1.2)
      = 2 * latU q (x.1.1, x.1.2)
  have hp : (x.1.1.natAbs + x.1.2.natAbs) % 2 = 0 := by omega
  have hs : (-1 : ℝ) ^ (x.1.1.natAbs + x.1.2.natAbs) = 1 := by
    rw [neg_one_pow_mod, hp, pow_zero]
  rw [latT_scale q x.1.1 x.1.2, hs]
  ring

/-- On the odd-parity shell the sign is −1: the two books CANCEL
pointwise, no involution needed. -/
private theorem merged_odd (q : ℝ) (x : OddPar) :
    latU q x.1 + latT q x.1 = 0 := by
  have h1 : (x.1.1 + x.1.2) % 2 = 1 := x.2
  show latU q (x.1.1, x.1.2) + latT q (x.1.1, x.1.2) = 0
  have hp : (x.1.1.natAbs + x.1.2.natAbs) % 2 = 1 := by omega
  have hs : (-1 : ℝ) ^ (x.1.1.natAbs + x.1.2.natAbs) = -1 := by
    rw [neg_one_pow_mod, hp, pow_one]
  rw [latT_scale q x.1.1 x.1.2, hs]
  ring

/-! ## Slice summability (the R221 receipt, rebuilt for the merge) -/

/-- ANY indicator slice of the merged family is summable by norm
domination over `latU + latU`: the triangle inequality splits the
merged summand, `|latT| = latU` pays the second half, and a zero
indicator asks only nonnegativity of the dominating norm. -/
private theorem slice_summable {q : ℝ} (hq0 : 0 < q) (hq1 : q < 1)
    (s : Set (ℤ × ℤ)) :
    Summable fun p : ℤ × ℤ => s.indicator (fun x => latU q x + latT q x) p := by
  have hU : Summable (latU q) := latU_summable hq0 hq1
  refine (hU.add hU).of_norm_bounded fun p => ?_
  by_cases hp : p ∈ s
  · have hm : ‖s.indicator (fun x => latU q x + latT q x) p‖
        = ‖latU q p + latT q p‖ := by rw [Set.indicator_of_mem hp]
    rw [hm]
    have hnu : ‖latU q p‖ = latU q p := abs_latU hq0 p
    have hnt : ‖latT q p‖ = latU q p := abs_latT hq0 p
    calc ‖latU q p + latT q p‖ ≤ ‖latU q p‖ + ‖latT q p‖ := norm_add_le _ _
    _ = latU q p + latU q p := by rw [hnu, hnt]
  · have hm : ‖s.indicator (fun x => latU q x + latT q x) p‖ = 0 := by
      rw [Set.indicator_of_notMem hp, norm_zero]
    rw [hm]
    exact add_nonneg (pow_nonneg hq0.le _) (pow_nonneg hq0.le _)

/-! ## The pointwise split: every point is in exactly one book -/

/-- Each lattice point speaks exactly one parity dialect: the two
indicator slices of the merged summand add back to the summand
(case by case, omega closing the mod-2 clash). -/
private theorem merged_split_apply (q : ℝ) (p : ℤ × ℤ) :
    latU q p + latT q p
      = {p : ℤ × ℤ | (p.1 + p.2) % 2 = 0}.indicator (fun x => latU q x + latT q x) p
      + {p : ℤ × ℤ | (p.1 + p.2) % 2 = 1}.indicator (fun x => latU q x + latT q x) p := by
  by_cases h : (p.1 + p.2) % 2 = 0
  · have hnO : p ∉ {x : ℤ × ℤ | (x.1 + x.2) % 2 = 1} := by
      intro hm
      have h1 : (p.1 + p.2) % 2 = 1 := hm
      omega
    rw [Set.indicator_of_mem h, Set.indicator_of_notMem hnO, add_zero]
  · have h1 : (p.1 + p.2) % 2 = 1 := by omega
    have hnE : p ∉ {x : ℤ × ℤ | (x.1 + x.2) % 2 = 0} := by
      intro hm
      have h0 : (p.1 + p.2) % 2 = 0 := hm
      omega
    rw [Set.indicator_of_notMem hnE, Set.indicator_of_mem h1, zero_add]

/-! ## The parity merge window itself -/

/-- WINDOW B3, the main identity: the unsigned and sign-carrying
lattice books add to TWICE the same-parity sublattice book. -/
theorem lat_merge {q : ℝ} (hq0 : 0 < q) (hq1 : q < 1) :
    (∑' p : ℤ × ℤ, latU q p) + ∑' p : ℤ × ℤ, latT q p
      = 2 * ∑' p : SamePar, latU q p.1 := by
  have hU : Summable (latU q) := latU_summable hq0 hq1
  have hT : Summable (latT q) := latT_summable hq0 hq1
  have hE' := slice_summable hq0 hq1 {p : ℤ × ℤ | (p.1 + p.2) % 2 = 0}
  have hO' := slice_summable hq0 hq1 {p : ℤ × ℤ | (p.1 + p.2) % 2 = 1}
  -- SamePar/OddPar (anonymous subtypes) and Set.Elem of the parity sets
  -- unfold to the same Subtype: `tsum_subtype` closes the ascription by
  -- defeq (a type-level rw would break the summation filter's instances).
  have hE : (∑' p : SamePar, (latU q p.1 + latT q p.1))
      = ∑' p : ℤ × ℤ, {p : ℤ × ℤ | (p.1 + p.2) % 2 = 0}.indicator
          (fun x => latU q x + latT q x) p :=
    tsum_subtype {p : ℤ × ℤ | (p.1 + p.2) % 2 = 0} (fun x => latU q x + latT q x)
  have hO : (∑' p : OddPar, (latU q p.1 + latT q p.1))
      = ∑' p : ℤ × ℤ, {p : ℤ × ℤ | (p.1 + p.2) % 2 = 1}.indicator
          (fun x => latU q x + latT q x) p :=
    tsum_subtype {p : ℤ × ℤ | (p.1 + p.2) % 2 = 1} (fun x => latU q x + latT q x)
  have hE2 : ∑' p : SamePar, (latU q p.1 + latT q p.1)
      = 2 * ∑' p : SamePar, latU q p.1 := by
    rw [tsum_congr fun x => merged_even q x]
    exact tsum_mul_left
  have hO2 : ∑' p : OddPar, (latU q p.1 + latT q p.1) = 0 := by
    rw [tsum_congr fun x => merged_odd q x, tsum_zero]
  calc (∑' p : ℤ × ℤ, latU q p) + ∑' p : ℤ × ℤ, latT q p
      = ∑' p : ℤ × ℤ, (latU q p + latT q p) := (Summable.tsum_add hU hT).symm
    _ = ∑' p : ℤ × ℤ, ({p : ℤ × ℤ | (p.1 + p.2) % 2 = 0}.indicator
          (fun x => latU q x + latT q x) p
        + {p : ℤ × ℤ | (p.1 + p.2) % 2 = 1}.indicator
          (fun x => latU q x + latT q x) p) :=
        tsum_congr fun p => merged_split_apply q p
    _ = (∑' p : ℤ × ℤ, {p : ℤ × ℤ | (p.1 + p.2) % 2 = 0}.indicator
          (fun x => latU q x + latT q x) p)
        + ∑' p : ℤ × ℤ, {p : ℤ × ℤ | (p.1 + p.2) % 2 = 1}.indicator
          (fun x => latU q x + latT q x) p :=
        Summable.tsum_add hE' hO'
    _ = (∑' p : SamePar, (latU q p.1 + latT q p.1))
        + ∑' p : OddPar, (latU q p.1 + latT q p.1) := by rw [hE, hO]
    _ = 2 * ∑' p : SamePar, latU q p.1 := by rw [hE2, hO2, add_zero]

/-- WINDOW B3, PROVED: the parity merge of the R2 route, now an
unconditional theorem. Feed this to `anchorB_of_route_three_paid` to
discharge `h3`: five of the seven hypotheses of the anchor-B assembly
paid (the two R1 bridges, B2a, B2b, B3), two remaining (B4, B5). -/
theorem routeB3_proved : routeB3 :=
  fun _ hq0 hq1 => lat_merge hq0 hq1

/-- DROP-IN RECEIPT (TYPE-CHECKED HERE): with the two R1 bridges, B2a,
B2b and B3 all proved, `anchorB_of_route` runs on its remaining TWO
named windows (B4, B5) — five of the seven hypotheses discharged by
green modules, nothing hidden. -/
theorem anchorB_of_route_two_paid (h4 : routeB4) (h5 : routeB5) :
    jacobiAnchorB :=
  anchorB_of_route_three_paid routeB3_proved h4 h5

end YangMills.DualBook
