/-
PROVENANCE: the Catalan gate of the dual/Z₂-scaffold exact book (Bucket B
part 4), following the printed "Bucket B Handoff — the Dual-Book Spec for
Gemini". The book's Gaussian arm (Theorem B) ends at
Z_1000(2) = π·G − (π²/24)·log 2 and Z_1110(2) = −π·G − (π²/24)·log 2,
where G is Catalan's constant; the bench certified G three ways at 1e-14
and the difference law D2′–D3′ passes through L(s, χ₋₄) with L(1, χ₋₄) =
π/4 (Leibniz) and G = L(2, χ₋₄). This module gives G its honest Lean
definition, proves absolute convergence from first principles, and
STATES the gate (the χ₋₄ L-value identity) as a named window.

SCOPE NOTE: this module certifies THIS ARITHMETIC — the definition and
absolute convergence of Catalan's constant. It proves nothing about
physical four-dimensional Yang–Mills theory and claims no Clay
Millennium result.

HONEST WINDOW SPLIT:
  PROVEN HERE: `leTwoChiMinusFour_summable`, `catalanCore_summable`.
  NAMED WINDOW (stated, never claimed): `catalanGate` — the identity
  L(2, χ₋₄) = G connecting the Dirichlet L-series over all positive
  integers with the odd-only alternating series. Paying it needs the
  parity vanishing reindex (evens contribute 0 in the L-series), a
  named follow-up window.
  MATHLIB GAP (verified on the v4.37.0-rc1 tree): Mathlib carries NO
  Catalan constant (only combinatorial Catalan numbers) and no χ₋₄
  L-values; the gate is ours to build.
-/
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Algebra.Order.GroupWithZero.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-!
# The Catalan gate: G defined, summable, and the gate named (rung 6 companion)
-/

namespace YangMills.DualBook

/-! ## The character χ₋₄ -/

/-- The odd Dirichlet character mod 4: χ₋₄(n) = 1 if n ≡ 1 (mod 4),
−1 if n ≡ 3 (mod 4), and 0 otherwise. -/
def chiMinusFour (n : ℤ) : ℝ :=
  if n % 4 = 1 then 1 else if n % 4 = 3 then -1 else 0

/-! ## Catalans constant and its two series -/

/-- Catalans constant, odd-only alternating form:
`G = ∑' n : ℕ, (−1)ⁿ / (2n+1)²`. -/
noncomputable def catalan : ℝ :=
  ∑' n : ℕ, (-1 : ℝ) ^ n / ((2 * n + 1 : ℕ) : ℝ) ^ 2

/-- The Dirichlet L-series value L(2, χ₋₄) over all positive integers:
`∑' k ≥ 1, χ₋₄(k) / k²` indexed as `∑' n : ℕ, χ₋₄(n+1) / (n+1)²`. -/
noncomputable def leTwoChiMinusFour : ℝ :=
  ∑' n : ℕ, chiMinusFour (n + 1) / (((n + 1 : ℕ) : ℝ) ^ 2)

/-- The shifted p-series comparator: `∑' n, 1/(n+1)²` converges. Built
from `summable_one_div_nat_pow` through the positive-natural equivalence
(no shift lemma assumed: `Summable_pnat_iff` carries it honestly). -/
private theorem pseries_succ_summable :
    Summable fun n : ℕ => (1 : ℝ) / (((n + 1 : ℕ) : ℝ) ^ 2) := by
  have hfull : Summable fun m : ℕ => (1 : ℝ) / ((m : ℕ) : ℝ) ^ 2 :=
    (Real.summable_one_div_nat_pow (p := 2)).mpr (by norm_num)
  have hpnat : Summable (fun n : ℕ+ => (1 : ℝ) / ((n : ℕ) : ℝ) ^ 2) :=
    (summable_pnat_iff_summable_nat (f := fun m : ℕ => (1 : ℝ) / ((m : ℕ) : ℝ) ^ 2)).mpr hfull
  exact (summable_pnat_iff_summable_succ
    (f := fun m : ℕ => (1 : ℝ) / ((m : ℕ) : ℝ) ^ 2)).mp hpnat

/-- χ₋₄ takes only the values −1, 0, 1. -/
private theorem chiMinusFour_norm (n : ℤ) :
    ‖chiMinusFour n‖ ≤ 1 := by
  unfold chiMinusFour
  by_cases h1 : n % 4 = 1
  · simp [*]
  · by_cases h2 : n % 4 = 3
    · simp [*]
    · simp [*]

/-- Absolute convergence of the L(2, χ₋₄) series. -/
theorem leTwoChiMinusFour_summable :
    Summable fun n : ℕ => chiMinusFour (n + 1) / (((n + 1 : ℕ) : ℝ) ^ 2) := by
  refine Summable.of_norm_bounded pseries_succ_summable fun n => ?_
  have h1 := chiMinusFour_norm (n + 1)
  have h2 : (0 : ℝ) < (((n + 1 : ℕ) : ℝ) ^ 2) := by
    have : (0 : ℝ) < ((n + 1 : ℕ) : ℝ) := Nat.cast_pos.mpr (by omega : 0 < n + 1)
    exact pow_pos this 2
  rw [Real.norm_eq_abs] at h1 ⊢
  rw [abs_div, abs_of_pos h2, div_le_div_iff₀ h2 h2]
  gcongr

/-- Absolute convergence of Catalans constant series: the term carries
sign `|(-1)ⁿ| = 1` and `2n+1 ≥ n+1`, so the shifted p-series dominates. -/
theorem catalanCore_summable :
    Summable fun n : ℕ => (-1 : ℝ) ^ n / ((2 * n + 1 : ℕ) : ℝ) ^ 2 := by
  refine Summable.of_norm_bounded pseries_succ_summable fun n => ?_
  have hp1 : (0 : ℝ) < (((n + 1 : ℕ) : ℝ) ^ 2) := by
    have : (0 : ℝ) < ((n + 1 : ℕ) : ℝ) := Nat.cast_pos.mpr (by omega : 0 < n + 1)
    exact pow_pos this 2
  have hp2 : (0 : ℝ) < (((2 * n + 1 : ℕ) : ℝ) ^ 2) := by
    have : (0 : ℝ) < ((2 * n + 1 : ℕ) : ℝ) := Nat.cast_pos.mpr (by omega : 0 < 2 * n + 1)
    exact pow_pos this 2
  rw [Real.norm_eq_abs, abs_div, abs_neg_one_pow, abs_of_pos hp2,
    div_le_div_iff₀ hp2 hp1, one_mul, one_mul]
  have hbb : ((n + 1 : ℕ) : ℝ) ≤ ((2 * n + 1 : ℕ) : ℝ) :=
    Nat.cast_le.mpr (by omega : (n + 1 : ℕ) ≤ 2 * n + 1)
  exact pow_le_pow_left₀ (Nat.cast_nonneg _) hbb 2

/-! ## The gate (named window) -/

/-- The Catalan gate (NAMED WINDOW — stated, never claimed here):
the Dirichlet identity `L(2, χ₋₄) = G`, i.e. the series over all positive
integers with the character χ₋₄ equals the odd-only alternating Catalan
series. Paying this window needs the parity-vanishing reindex (the even
terms of the L-series are exactly 0); the book's Theorem B Gaussian arm
and the D2′–D3′ difference law wait on this gate (plus the Epstein
closed forms named in `FrullaniBook`). The bench certified
L(1, χ₋₄) = π/4 (Leibniz) and G = L(2, χ₋₄) numerically three ways to
1e-14; numerics are evidence, never proof. -/
def catalanGate : Prop := leTwoChiMinusFour = catalan

end YangMills.DualBook
