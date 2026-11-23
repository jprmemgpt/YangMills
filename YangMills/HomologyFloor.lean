import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp

namespace YangMills.DualBook

noncomputable def homologyFloor (x : ℝ) (L : ℕ) : ℝ :=
  (1 - x ^ (L ^ 2)) / (1 + x ^ (L ^ 2))

private theorem one_sub_pow_eq (x : ℝ) : ∀ n : ℕ,
    1 - x ^ n = (1 - x) * ∑ k ∈ Finset.range n, x ^ k
  | 0 => by simp
  | n + 1 => by
      rw [Finset.sum_range_succ, mul_add, ← one_sub_pow_eq x n]
      ring

theorem homologyFloor_num_geom_sum (x : ℝ) (L : ℕ) :
    1 - x ^ (L ^ 2) = (1 - x) * ∑ k ∈ Finset.range (L ^ 2), x ^ k :=
  one_sub_pow_eq x (L ^ 2)

theorem homologyFloor_eq_one_sub (x : ℝ) (L : ℕ) (hden : 1 + x ^ (L ^ 2) ≠ 0) :
    homologyFloor x L = 1 - (2 * x ^ (L ^ 2)) / (1 + x ^ (L ^ 2)) := by
  unfold homologyFloor; field_simp [hden]; ring

theorem homologyFloor_bounds (x : ℝ) (L : ℕ) (hx0 : 0 ≤ x) (hx1 : x < 1) (hL : 1 ≤ L) :
    0 < homologyFloor x L ∧ homologyFloor x L ≤ 1 := by
  have hL2 : 1 ≤ L ^ 2 := by nlinarith
  have hpow_nonneg : 0 ≤ x ^ (L ^ 2) := pow_nonneg hx0 (L ^ 2)
  have hpow_lt_one : x ^ (L ^ 2) < 1 := pow_lt_one₀ hx0 hx1 (by omega)
  have hden_pos : 0 < 1 + x ^ (L ^ 2) := by linarith
  unfold homologyFloor
  exact ⟨div_pos (by linarith) hden_pos, (div_le_one hden_pos).2 (by linarith)⟩

theorem homologyFloor_mono (x : ℝ) {L₁ L₂ : ℕ}
    (hx0 : 0 ≤ x) (hx1 : x ≤ 1) (hL : L₁ ≤ L₂) :
    homologyFloor x L₁ ≤ homologyFloor x L₂ := by
  have hpow : x ^ (L₂ ^ 2) ≤ x ^ (L₁ ^ 2) :=
    pow_le_pow_of_le_one hx0 hx1 (Nat.pow_le_pow_left hL 2)
  have hden1 : 0 < 1 + x ^ (L₁ ^ 2) := by linarith [pow_nonneg hx0 (L₁ ^ 2)]
  have hden2 : 0 < 1 + x ^ (L₂ ^ 2) := by linarith [pow_nonneg hx0 (L₂ ^ 2)]
  unfold homologyFloor; rw [div_le_div_iff₀ hden1 hden2]; nlinarith

#print axioms homologyFloor_num_geom_sum
#print axioms homologyFloor_eq_one_sub
#print axioms homologyFloor_bounds
#print axioms homologyFloor_mono
end YangMills.DualBook
