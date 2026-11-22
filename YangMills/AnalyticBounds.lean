import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-!
# Module 3: AnalyticBounds (Lean 4 + Mathlib4)
Replaces the declared rational upper-bound hypotheses in `CorridorConstants.lean`
with machine-checked real-number proofs over ℝ:
1. `-Real.log (1 - 1/567) < 177/100000`
2. `Real.log 16 < 27726/10000`
3. `Real.log (8 * Real.exp 1) < 6159/2000`
4. `(1/567)^2 * (4319/10) < 84/62500`
5. Real-valued five-toll chain: `0.29489277 < Δκ` and `2 ≤ 8 * Δκ`.
-/

namespace YangMills

/-- Analytical resolvent-envelope bound: -ln(1 - 1/567) ≤ 1/566 < 177/100000. -/
theorem envelope_real_bound :
    -Real.log (1 - (1 : ℝ) / 567) < (177 : ℝ) / 100000 := by
  have hpos : (0 : ℝ) < 1 - (1 : ℝ) / 567 := by norm_num
  have hlog : 1 - (1 - (1 : ℝ) / 567)⁻¹ ≤ Real.log (1 - (1 : ℝ) / 567) :=
    Real.one_sub_inv_le_log_of_pos hpos
  have hrat : -(1 - (1 - (1 : ℝ) / 567)⁻¹) < (177 : ℝ) / 100000 := by norm_num
  linarith

/-- Structural 4D fold toll bound: ln 16 = 4 ln 2 < 27726/10000. -/
theorem lnFold_real_bound :
    Real.log (16 : ℝ) < (27726 : ℝ) / 10000 := by
  have h16 : (16 : ℝ) = (2 : ℝ) ^ (4 : ℕ) := by norm_num
  have hlog : Real.log (16 : ℝ) = 4 * Real.log 2 := by
    rw [h16, Real.log_pow]
    norm_num
  have h2 : Real.log 2 < 0.6931471808 := Real.log_two_lt_d9
  linarith

/-- Animal entropy bound: ln(8e) = 3 ln 2 + 1 < 6159/2000. -/
theorem lnC4_real_bound :
    Real.log ((8 : ℝ) * Real.exp 1) < (6159 : ℝ) / 2000 := by
  have h8 : (8 : ℝ) = (2 : ℝ) ^ (3 : ℕ) := by norm_num
  have hlog : Real.log ((8 : ℝ) * Real.exp 1) = 3 * Real.log 2 + 1 := by
    rw [Real.log_mul (by norm_num) (Real.exp_ne_zero 1), Real.log_exp, h8, Real.log_pow]
    norm_num
  have h2 : Real.log 2 < 0.6931471808 := Real.log_two_lt_d9
  linarith

/-- Two-leg bridge overhead bound: (1/567)^2 * 431.9 < 84/62500. -/
theorem bridge_real_bound :
    ((1 : ℝ) / 567) ^ 2 * ((4319 : ℝ) / 10) < (84 : ℝ) / 62500 := by
  norm_num

/-- Real-valued five-toll chain: for any κ₀ ≥ 61516/10000,
    Δκ strictly beats the certified corridor pair margin 0.29489277 and μ₀(8) = 8 Δκ ≥ 2. -/
theorem real_five_toll_surplus (κ₀ : ℝ) (hκ₀ : (61516 : ℝ) / 10000 ≤ κ₀) :
    let Δκ := κ₀ - (-Real.log (1 - (1 : ℝ) / 567)) - Real.log 16
                 - Real.log (8 * Real.exp 1) - ((1 : ℝ) / 567) ^ 2 * ((4319 : ℝ) / 10)
    (29489277 : ℝ) / 100000000 < Δκ ∧ (2 : ℝ) ≤ 8 * Δκ := by
  have hEnv := envelope_real_bound
  have hFold := lnFold_real_bound
  have hC4 := lnC4_real_bound
  have hBr := bridge_real_bound
  constructor <;> linarith

end YangMills
