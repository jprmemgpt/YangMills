/-
PROVENANCE: R221 THE-L3a-PARITY-SPLIT (Tue 2026-11-24). The fifth of
the seven named windows of the R1 route (YangMills v1.4,
JacobiAnchors.lean) taken to the battery: the parity split
`routeL3a`,
  ∑' p : ℤ × ℤ, latF q p
    = (∑' p : SamePar, latF q p.1) + ∑' p : OddPar, latF q p.1   for 0 < q < 1,
proved by sorting the mixed lattice sum by the parity of its
coordinate sum: even-sum points in the SamePar ledger, odd-sum points
in the OddPar ledger, and the two books add back to the first census.

PAPER ROUTE (pre-registered in the R1 candidate, executed here):
  ∑' p : ℤ × ℤ, latF q p
  = ∑' p, (E.indicator (latF q) p + O.indicator (latF q) p)   [pointwise parity split: each p ∈ E xor p ∈ O, Set.indicator_of_mem / Set.indicator_of_notMem, omega on the mod-2 clash]
  = (∑' p, E.indicator (latF q) p) + (∑' p, O.indicator (latF q) p)   [Summable.tsum_add, both slices summable]
  = (∑' p : SamePar, latF q p.1) + ∑' p : OddPar, latF q p.1   [tsum_subtype twice: the sublattice sum IS the indicator slice]

THE SLICE HEART: every indicator slice is dominated by the same
Fubini-twin family r^(|m|²)·r^(|n|²) that paid for L2 and L2b, because
|latF q p| = q^(|m|²+|n|²) by abs_neg_one_pow (the sign carries norm
1) and the exponent receipt toNat = sum of squared natAbs's (R219).
Convergence is inherited from the whole: splitting a ledger never
splits the credit.
THE TYPE HEART: the house sublattices SamePar, OddPar are anonymous
subtypes, tsum_subtype speaks through Set.Elem, and the two are the
SAME TYPE up to a type-level rfl — a partition IS a coproduct.

STATUS: compiled green in-sandbox against the pinned triplet (Mathlib
31ce06eaadf4a200c0e1407c5f10953cf606b8f8, lake 5.0.0, lean v4.37.0-rc1),
with the R220 L2b certificate reproduced green (3,536 jobs) against
the fresh cache before any new math crossed it. The shipping machine
remains the final notary (runbook step 4).

DROP-IN NOTE: with this window green, the hypothesis `h3a : routeL3a`
of `anchorA_of_route` (JacobiAnchors.lean) is discharged by
`routeL3a_proved`; with L1a, L1b, L2 and L2b already paid the R1
assembly rests on SEVEN named windows of which FIVE are proved and
TWO remain (L3b, L4).

SCOPE NOTE: this module certifies THIS ARITHMETIC — one classical
Jacobi theta bookkeeping identity, the mixed lattice sum partitioned
by parity. It proves nothing about physical four-dimensional
Yang–Mills theory and claims no Clay Millennium result. Bench FROZEN
AT 100.0, the crossing never claimed.
-/

import Mathlib.Topology.Algebra.InfiniteSum.Ring
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Analysis.Normed.Group.InfiniteSum
import YangMills.DualBook.JacobiAnchors
import YangMills.DualBook.JacobiAnchorsL1a
import YangMills.DualBook.JacobiAnchorsL1b
import YangMills.DualBook.JacobiAnchorsL2
import YangMills.DualBook.JacobiAnchorsL2b

/-!
# R221: the parity split (L3a)

The mixed lattice sum `∑' p : ℤ × ℤ, latF q p` is asked to sort its
points by the parity of their coordinate sum: the SamePar book
(`(p.1 + p.2) % 2 = 0`) and the OddPar book (`(p.1 + p.2) % 2 = 1`).
Three receipts carry it: every point is in exactly one book (parity,
omega-closed), every book's sum converges by inherited domination (the
L2/L2b Fubini-twin family), and each book's sum is an indicator slice
of the whole (`tsum_subtype`).
-/

namespace YangMills.DualBook

open Filter Topology

/-! ## The exponent receipt, restated private (the L2b original does not cross modules) -/

/-- The R219 exponent receipt: `toNat` of a sum of squares is the sum
of the squared `natAbs`s. -/
private theorem sq_sum_exp (a b : ℤ) :
    (a * a + b * b).toNat = a.natAbs ^ 2 + b.natAbs ^ 2 := by
  have h1 : 0 ≤ a * a + b * b := add_nonneg (mul_self_nonneg a) (mul_self_nonneg b)
  apply Nat.cast_injective (R := ℤ)
  rw [Int.toNat_of_nonneg h1, Nat.cast_add, Nat.cast_pow, Nat.cast_pow,
    Int.natAbs_pow_two, Int.natAbs_pow_two]
  ring

/-- The absolute value of a lattice summand is the nome alone: the
sign carries norm 1 (`abs_neg_one_pow`, the L1b receipt), the power
factor is positive, and the exponent is the sum of squared natAbs's
(the R219 receipt). -/
private theorem abs_latF {q : ℝ} (hq0 : 0 < q) (p : ℤ × ℤ) :
    |latF q p| = q ^ (p.1.natAbs ^ 2 + p.2.natAbs ^ 2) := by
  unfold latF
  rw [abs_mul, abs_neg_one_pow, one_mul, abs_of_pos (pow_pos hq0 _), sq_sum_exp]

/-! ## The dominating family (the parameterized Fubini twin, L2b's receipt restated) -/

/-- The dominating nonnegative lattice family at a general positive
nome r < 1, summable because fibers are constant multiples of the
theta-3 family and rows reconstitute theta-3 itself. -/
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

/-! ## Slice summability: convergence inherited from the whole -/

/-- ANY indicator slice of the lattice family is summable by norm
domination over the Fubini-twin family: the slice either carries a
summand (then `abs_latF` and `pow_add` show the norm IS one factor of
the dominating product) or carries zero (then only nonnegativity is
needed). Splitting a ledger never splits the credit. -/
private theorem slice_summable' {q : ℝ} (hq0 : 0 < q) (hq1 : q < 1) (s : Set (ℤ × ℤ)) :
    Summable fun p : ℤ × ℤ => s.indicator (latF q) p := by
  refine (dom_summable' hq0 hq1).of_norm_bounded fun p => ?_
  by_cases hp : p ∈ s
  · rw [Real.norm_eq_abs, Set.indicator_of_mem hp (latF q), abs_latF hq0 p, pow_add]
  · rw [Real.norm_eq_abs, Set.indicator_of_notMem hp (latF q), abs_zero]
    exact mul_nonneg (pow_nonneg hq0.le _) (pow_nonneg hq0.le _)

/-! ## The pointwise split: every point is in exactly one book -/

/-- Each lattice point speaks exactly one parity dialect: the two
indicator slices of a summand add back to the summand, case by case,
with omega closing the mod-2 clash. -/
private theorem latF_split_apply (q : ℝ) (p : ℤ × ℤ) :
    latF q p = {p : ℤ × ℤ | (p.1 + p.2) % 2 = 0}.indicator (latF q) p
      + {p : ℤ × ℤ | (p.1 + p.2) % 2 = 1}.indicator (latF q) p := by
  by_cases h : (p.1 + p.2) % 2 = 0
  · have hnO : p ∉ {x : ℤ × ℤ | (x.1 + x.2) % 2 = 1} := by
      intro hm
      have h1 : (p.1 + p.2) % 2 = 1 := hm
      omega
    rw [Set.indicator_of_mem h (latF q), Set.indicator_of_notMem hnO (latF q), add_zero]
  · have h1 : (p.1 + p.2) % 2 = 1 := by omega
    have hnE : p ∉ {x : ℤ × ℤ | (x.1 + x.2) % 2 = 0} := by
      intro hm
      have h0 : (p.1 + p.2) % 2 = 0 := hm
      omega
    rw [Set.indicator_of_notMem hnE (latF q), Set.indicator_of_mem h1 (latF q), zero_add]

/-! ## The parity split window itself -/

/-- WINDOW L3a, the main identity: the mixed lattice sum splits into
its even-parity and odd-parity books, and the two books add back to
the first census. -/
theorem latF_parity_split {q : ℝ} (hq0 : 0 < q) (hq1 : q < 1) :
    ∑' p : ℤ × ℤ, latF q p
      = (∑' p : SamePar, latF q p.1) + ∑' p : OddPar, latF q p.1 := by
  have hE' := slice_summable' hq0 hq1 {p : ℤ × ℤ | (p.1 + p.2) % 2 = 0}
  have hO' := slice_summable' hq0 hq1 {p : ℤ × ℤ | (p.1 + p.2) % 2 = 1}
  -- The sublattice sums ARE the indicator slices, up to a type-level
  -- rfl: SamePar/OddPar (anonymous subtypes) and Set.Elem of the
  -- parity sets unfold to the same Subtype, so `exact` closes the
  -- ascription by defeq without any type rewrite (a type-level `rw`
  -- breaks the summation filter's instances, motive not type correct).
  have hE : (∑' p : SamePar, latF q p.1)
      = ∑' p : ℤ × ℤ, {p : ℤ × ℤ | (p.1 + p.2) % 2 = 0}.indicator (latF q) p :=
    tsum_subtype {p : ℤ × ℤ | (p.1 + p.2) % 2 = 0} (latF q)
  have hO : (∑' p : OddPar, latF q p.1)
      = ∑' p : ℤ × ℤ, {p : ℤ × ℤ | (p.1 + p.2) % 2 = 1}.indicator (latF q) p :=
    tsum_subtype {p : ℤ × ℤ | (p.1 + p.2) % 2 = 1} (latF q)
  calc ∑' p : ℤ × ℤ, latF q p
      = ∑' p : ℤ × ℤ, ({p : ℤ × ℤ | (p.1 + p.2) % 2 = 0}.indicator (latF q) p
          + {p : ℤ × ℤ | (p.1 + p.2) % 2 = 1}.indicator (latF q) p) :=
        tsum_congr fun p => latF_split_apply q p
    _ = (∑' p : ℤ × ℤ, {p : ℤ × ℤ | (p.1 + p.2) % 2 = 0}.indicator (latF q) p)
        + ∑' p : ℤ × ℤ, {p : ℤ × ℤ | (p.1 + p.2) % 2 = 1}.indicator (latF q) p :=
        Summable.tsum_add hE' hO'
    _ = (∑' p : SamePar, latF q p.1) + ∑' p : OddPar, latF q p.1 := by
        rw [hE, hO]

/-- WINDOW L3a, PROVED: the parity split of the R1 route, now an
unconditional theorem. Feed this to `anchorA_of_route` (with
`routeL1a_proved`, `routeL1b_proved`, `routeL2_proved`,
`routeL2b_proved`) to discharge `h1a`, `h1b`, `h2`, `h2b` and `h3a`:
five of the seven named windows paid, two remaining. -/
theorem routeL3a_proved : routeL3a :=
  fun _ hq0 hq1 => latF_parity_split hq0 hq1

/-- DROP-IN RECEIPT (TYPE-CHECKED HERE): with L1a, L1b, L2, L2b and
L3a all proved, `anchorA_of_route` runs on its remaining TWO named
windows (L3b, L4) — five of the seven hypotheses discharged by green
modules, the unpaid down to the last pair, nothing hidden. -/
theorem anchorA_of_route_five_paid (h3b : routeL3b) (h4 : routeL4) : jacobiAnchorA :=
  anchorA_of_route routeL1a_proved routeL1b_proved routeL2_proved
    routeL2b_proved routeL3a_proved h3b h4
