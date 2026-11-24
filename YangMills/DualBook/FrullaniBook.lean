/-
PROVENANCE: rung 6 of the dual/Z₂-scaffold exact book (Bucket B), following
the printed "Bucket B Handoff — the Dual-Book Spec for Gemini". The
certified base counterterm of the book is C₀ = −π²/16 (bench-certified
below 1e-9 on the Frullani route, with the per-class law −π²|δ|⁴/12);
the book's E is E = ½·ln 2 (Theorem A arms, bench-certified at 1e-13).
This module carries: (1) a PROVEN rational bracket witness for C₀ from
Mathlib's own π bounds; (2) the PROVEN conditional E-assembly from the
Theorem A closed forms; (3) the Frullani exponential window STATED as a
named window (Prop), citing Mathlib's `Frullani.integral_Ioi_eq`.

SCOPE NOTE: this module certifies THIS ARITHMETIC — bounds, brackets, and
linear assembly of certified constants. It proves nothing about physical
four-dimensional Yang–Mills theory and claims no Clay Millennium result.

HONEST WINDOW SPLIT:
  PROVEN HERE: `c0_bracket` (a pure rational-arithmetic consequence of
  Mathlib's π bounds: the certified machine value −0.6168502751 sits
  inside (−0.621, −0.616)); `E_assembly` (conditional on the Theorem A
  closed forms stated as hypotheses Z1100 = −(π²/6)·log 2 and
  Z1111 = −4·(π²/6)·log 2, itself never claimed here).
  NAMED WINDOW: `frullaniExpWindow` — the exponential Frullani integral,
  for which Mathlib's `Frullani.integral_Ioi_eq` gives the exact value
  once the near-0 integrability sub-lemma is built; that sub-window is
  NAMED here, not paid. The Mellin normalization's honest regularizer
  (the analytic −T₀^s/s piece) is likewise a NAMED window — the R69
  honest-slips record requires carrying it in any future Mellin build.
-/
import Mathlib.Analysis.SpecialFunctions.FrullaniIntegral
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-!
# The Frullani book: C₀ bracket, E-assembly, and the Frullani window (rung 6)
-/

namespace YangMills.DualBook

open Real Set

/-! ## The C₀ bracket witness (proved) -/

/-- The book's Frullani base C₀ = −π²/16, bracketed between honest
rationals: −0.621 < −π²/16 < −0.616. This is pure arithmetic on
Mathlib's own π bounds (`pi_gt_d4`, `pi_lt_d2`): π² ∈ (3.1415², 3.15²) ⊂
(9.856/1, 9.936/1) is exactly what the two sides need. The bench's
certified machine value −0.6168502751 lies strictly inside; the bracket
is the Lean receipt that the certified constant cannot have slipped a
digit. -/
theorem c0_bracket : -(621 / 1000 : ℝ) < -(π ^ 2 / 16) ∧
    -(π ^ 2 / 16) < -(616 / 1000 : ℝ) := by
  have hlo : (3.1415 : ℝ) ^ 2 < π ^ 2 :=
    pow_lt_pow_left₀ pi_gt_d4 (by norm_num) two_ne_zero
  have hhi : π ^ 2 < (3.15 : ℝ) ^ 2 :=
    pow_lt_pow_left₀ pi_lt_d2 pi_pos.le two_ne_zero
  refine ⟨?_, ?_⟩
  · rw [neg_lt_neg_iff, div_lt_iff₀ (by norm_num : (0 : ℝ) < 16)]
    exact lt_trans hhi (by norm_num : (3.15 : ℝ) ^ 2 < 621 / 1000 * 16)
  · rw [neg_lt_neg_iff, lt_div_iff₀ (by norm_num : (0 : ℝ) < 16)]
    exact lt_trans (by norm_num : (616 / 1000 : ℝ) * 16 < (3.1415 : ℝ) ^ 2) hlo

/-! ## The E-assembly from the Theorem A closed forms (proved, conditional) -/

/-- The E-assembly: CONDITIONAL on the book's Theorem A closed forms at
s = 2 —
  Z_1100(2) = −(π²/6)·log 2,   Z_1111(2) = −4·(π²/6)·log 2,
(the 2-adic arm) — the book's E is exactly half the natural logarithm
of two:
  (Z_1100 − Z_1111)/π² = log 2 / 2.
The two closed forms are HYPOTHESES here (the Epstein zeta evaluation
is a named window of the book, never claimed in this module); the
assembly itself is proved linear algebra, certified a fortiori. The
bench witness E = 0.3465735902799… (1e-13) is evidence, never a proof
substitute. -/
theorem E_assembly {Z1100 Z1111 : ℝ}
    (hZ1100 : Z1100 = -(π ^ 2 / 6) * log 2)
    (hZ1111 : Z1111 = -(4 * (π ^ 2 / 6)) * log 2) :
    (Z1100 - Z1111) / π ^ 2 = log 2 / 2 := by
  have hπ : (π ^ 2 : ℝ) ≠ 0 := pow_ne_zero 2 pi_pos.ne'
  rw [hZ1100, hZ1111, div_eq_div_iff hπ two_ne_zero]
  ring

/-! ## The Frullani exponential window (named) -/

/-- The Frullani exponential window (NAMED WINDOW — a statement, never
a claim in this file): for the kernel f = exp,
`∫ x in Ioi 0, x⁻¹ * (exp (−4x) − exp (−x)) = −log 4`.
Mathlib's `Frullani.integral_Ioi_eq` reduces this to the near-0
integrability sub-lemma (the integrand tends to the finite limit −3 as
x → 0⁺, so locally integrable), which is the NAMED sub-window. The
book's certified Frullani receipts ride the lemniscatic base route
whose rational bracket is `c0_bracket` above; per-class law
−π²|δ|⁴/12 rides the bench record. -/
def frullaniExpWindow : Prop :=
  ∫ x : ℝ in Ioi (0 : ℝ), x⁻¹ * (Real.exp (-4 * x) - Real.exp (-x)) = -Real.log 4

end YangMills.DualBook
