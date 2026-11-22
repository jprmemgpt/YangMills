import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Module 5: NeumannSpectrum (Lean 4 + Mathlib4)
Formally verifies Lemma 3.2 (Discrete Neumann Projector Spectral Floor) over ℝ:
1. Exact 1D discrete Laplacian eigenvalue equation:
   2 ψ_k(x) - ψ_k(x + 1) - ψ_k(x - 1) = 4 sin²(π k / (2L)) ψ_k(x).
2. Exact zero-flux Neumann boundary reflection symmetry at both cell walls (x = 0 and x = L - 1).
3. Exact 4D spectral gap floor λ_min(L) = 4 sin²(π / (2L)) > 0 for every L ≥ 2 and
   every nonzero mode (k₁, k₂, k₃, k₄) ≠ (0, 0, 0, 0) in {0, ..., L - 1}⁴.
-/

namespace YangMills

/-- 1D discrete Neumann eigenfunction ψ_k(x) = cos(π k (2x + 1) / (2L)). -/
noncomputable def neumannMode1D (L k : ℕ) (x : ℝ) : ℝ :=
  Real.cos (Real.pi * (k : ℝ) * (2 * x + 1) / (2 * (L : ℝ)))

/-- 1D discrete Neumann eigenvalue λ_k(L) = 4 sin²(π k / (2L)). -/
noncomputable def neumannEig1D (L k : ℕ) : ℝ :=
  4 * Real.sin (Real.pi * (k : ℝ) / (2 * (L : ℝ))) ^ 2

/-- 4D cell-Neumann eigenvalue ∑_{μ=1}^4 4 sin²(π k_μ / (2L)). -/
noncomputable def neumannEig4D (L k1 k2 k3 k4 : ℕ) : ℝ :=
  neumannEig1D L k1 + neumannEig1D L k2 + neumannEig1D L k3 + neumannEig1D L k4

/-- Coupling-independent spectral gap floor λ_min(L) = 4 sin²(π / (2L)). -/
noncomputable def neumannGapFloor (L : ℕ) : ℝ :=
  4 * Real.sin (Real.pi / (2 * (L : ℝ))) ^ 2

/-! ## 1. Exact 1D Discrete Laplacian Eigenvalue & Boundary Reflections -/

/-- Universal cosine stencil identity: 2 cos θ - cos(θ + 2δ) - cos(θ - 2δ) = 4 sin²(δ) cos θ. -/
theorem discrete_laplacian_cos_identity (θ δ : ℝ) :
    2 * Real.cos θ - Real.cos (θ + 2 * δ) - Real.cos (θ - 2 * δ) =
      4 * Real.sin δ ^ 2 * Real.cos θ := by
  have hcs : Real.sin δ ^ 2 + Real.cos δ ^ 2 = 1 := Real.sin_sq_add_cos_sq δ
  rw [Real.cos_add, Real.cos_sub, Real.cos_two_mul]
  have h2 : Real.cos δ ^ 2 = 1 - Real.sin δ ^ 2 := by linarith
  rw [h2]
  ring

/-- Exact 1D discrete Laplacian eigenvalue equation for ψ_k(x). -/
theorem neumannMode1D_eigenvalue (L k : ℕ) (x : ℝ) :
    2 * neumannMode1D L k x - neumannMode1D L k (x + 1) - neumannMode1D L k (x - 1) =
      neumannEig1D L k * neumannMode1D L k x := by
  unfold neumannMode1D neumannEig1D
  have hplus : Real.pi * (k : ℝ) * (2 * (x + 1) + 1) / (2 * (L : ℝ)) =
      Real.pi * (k : ℝ) * (2 * x + 1) / (2 * (L : ℝ)) +
        2 * (Real.pi * (k : ℝ) / (2 * (L : ℝ))) := by ring
  have hminus : Real.pi * (k : ℝ) * (2 * (x - 1) + 1) / (2 * (L : ℝ)) =
      Real.pi * (k : ℝ) * (2 * x + 1) / (2 * (L : ℝ)) -
        2 * (Real.pi * (k : ℝ) / (2 * (L : ℝ))) := by ring
  rw [hplus, hminus]
  exact discrete_laplacian_cos_identity _ _

/-- Left-wall Neumann zero-flux reflection: ψ_k(-1) = ψ_k(0). -/
theorem neumannMode1D_left_boundary (L k : ℕ) :
    neumannMode1D L k (-1) = neumannMode1D L k 0 := by
  unfold neumannMode1D
  have hneg : Real.pi * (k : ℝ) * (2 * (-1 : ℝ) + 1) / (2 * (L : ℝ)) =
      -(Real.pi * (k : ℝ) * (2 * (0 : ℝ) + 1) / (2 * (L : ℝ))) := by ring
  rw [hneg, Real.cos_neg]

/-- Right-wall Neumann zero-flux reflection: ψ_k(L) = ψ_k(L - 1) for L ≠ 0. -/
theorem neumannMode1D_right_boundary (L k : ℕ) (hL : L ≠ 0) :
    neumannMode1D L k (L : ℝ) = neumannMode1D L k ((L : ℝ) - 1) := by
  unfold neumannMode1D
  have hL0 : (L : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hL
  have h2L : (2 * (L : ℝ)) ≠ 0 := mul_ne_zero (by norm_num) hL0
  have h1 : Real.pi * (k : ℝ) * (2 * (L : ℝ) + 1) / (2 * (L : ℝ)) =
      (k : ℝ) * Real.pi + Real.pi * (k : ℝ) / (2 * (L : ℝ)) := by
    rw [← mul_div_cancel_right₀ ((k : ℝ) * Real.pi) h2L, ← add_div]
    congr 1
    ring
  have h2 : Real.pi * (k : ℝ) * (2 * ((L : ℝ) - 1) + 1) / (2 * (L : ℝ)) =
      (k : ℝ) * Real.pi - Real.pi * (k : ℝ) / (2 * (L : ℝ)) := by
    rw [← mul_div_cancel_right₀ ((k : ℝ) * Real.pi) h2L, ← sub_div]
    congr 1
    ring
  rw [h1, h2, Real.cos_add, Real.cos_sub, Real.sin_nat_mul_pi]
  ring

/-! ## 2. Exact 4D Spectral Gap Floor λ_min(L) = 4 sin²(π / (2L)) > 0 -/

/-- Every 1D eigenvalue is nonnegative. -/
theorem neumannEig1D_nonneg (L k : ℕ) : 0 ≤ neumannEig1D L k := by
  unfold neumannEig1D
  exact mul_nonneg (by norm_num) (sq_nonneg _)

/-- For every L ≥ 2, the spectral gap floor 4 sin²(π / (2L)) is strictly positive. -/
theorem neumannGapFloor_pos (L : ℕ) (hL : 2 ≤ L) : 0 < neumannGapFloor L := by
  unfold neumannGapFloor
  have hLR : (2 : ℝ) ≤ (L : ℝ) := by exact_mod_cast hL
  have h2L : (0 : ℝ) < 2 * (L : ℝ) := by linarith
  have hx_pos : 0 < Real.pi / (2 * (L : ℝ)) := div_pos Real.pi_pos h2L
  have hx_lt : Real.pi / (2 * (L : ℝ)) < Real.pi := div_lt_self Real.pi_pos (by linarith)
  have hsin_pos : 0 < Real.sin (Real.pi / (2 * (L : ℝ))) :=
    Real.sin_pos_of_pos_of_lt_pi hx_pos hx_lt
  have hsq_pos : 0 < Real.sin (Real.pi / (2 * (L : ℝ))) ^ 2 := sq_pos_of_pos hsin_pos
  linarith

/-- For 1 ≤ k < L (with L ≥ 2), λ_k(L) ≥ λ_min(L) = 4 sin²(π / (2L)). -/
theorem neumannEig1D_ge_floor (L k : ℕ) (hL : 2 ≤ L) (hk1 : 1 ≤ k) (hkL : k < L) :
    neumannGapFloor L ≤ neumannEig1D L k := by
  unfold neumannGapFloor neumannEig1D
  have hLR : (2 : ℝ) ≤ (L : ℝ) := by exact_mod_cast hL
  have hL_pos : (0 : ℝ) < (L : ℝ) := by linarith
  have h2L_pos : (0 : ℝ) < 2 * (L : ℝ) := by linarith
  have hk1R : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk1
  have hkLR : (k : ℝ) ≤ (L : ℝ) := by exact_mod_cast (Nat.le_of_lt hkL)
  have hx_pos : 0 < Real.pi / (2 * (L : ℝ)) := div_pos Real.pi_pos h2L_pos
  have hx_lt : Real.pi / (2 * (L : ℝ)) < Real.pi := div_lt_self Real.pi_pos (by linarith)
  have hsin_pos : 0 < Real.sin (Real.pi / (2 * (L : ℝ))) :=
    Real.sin_pos_of_pos_of_lt_pi hx_pos hx_lt
  have hx_neg : -(Real.pi / 2) ≤ Real.pi / (2 * (L : ℝ)) := by linarith [Real.pi_pos]
  have hxy : Real.pi / (2 * (L : ℝ)) ≤ Real.pi * (k : ℝ) / (2 * (L : ℝ)) := by
    apply div_le_div_of_nonneg_right _ (le_of_lt h2L_pos)
    calc
      Real.pi = Real.pi * 1 := (mul_one Real.pi).symm
      _ ≤ Real.pi * (k : ℝ) := mul_le_mul_of_nonneg_left hk1R (le_of_lt Real.pi_pos)
  have hy_le : Real.pi * (k : ℝ) / (2 * (L : ℝ)) ≤ Real.pi / 2 := by
    have h1 : Real.pi * (k : ℝ) / (2 * (L : ℝ)) ≤ Real.pi * (L : ℝ) / (2 * (L : ℝ)) :=
      div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left hkLR (le_of_lt Real.pi_pos)) (le_of_lt h2L_pos)
    have h2 : Real.pi * (L : ℝ) / (2 * (L : ℝ)) = Real.pi / 2 :=
      mul_div_mul_right Real.pi 2 (ne_of_gt hL_pos)
    linarith
  have hsin_le :
      Real.sin (Real.pi / (2 * (L : ℝ))) ≤ Real.sin (Real.pi * (k : ℝ) / (2 * (L : ℝ))) :=
    Real.sin_le_sin_of_le_of_le_pi_div_two hx_neg hy_le hxy
  have hsq :
      Real.sin (Real.pi / (2 * (L : ℝ))) ^ 2 ≤
        Real.sin (Real.pi * (k : ℝ) / (2 * (L : ℝ))) ^ 2 := by
    rw [sq, sq]
    exact mul_le_mul hsin_le hsin_le (le_of_lt hsin_pos) (le_trans (le_of_lt hsin_pos) hsin_le)
  linarith

/-- Lemma 3.2 (4D Discrete Neumann Spectral Gap Floor):
    For every L ≥ 2 and every nonzero mode (k1, k2, k3, k4) ∈ {0, ..., L-1}⁴ \ {0},
    the 4D cell-Neumann eigenvalue is bounded below by λ_min(L) = 4 sin²(π / (2L)) > 0. -/
theorem neumann_4d_spectral_floor
    (L k1 k2 k3 k4 : ℕ) (hL : 2 ≤ L)
    (hk1 : k1 < L) (hk2 : k2 < L) (hk3 : k3 < L) (hk4 : k4 < L)
    (hne : k1 ≠ 0 ∨ k2 ≠ 0 ∨ k3 ≠ 0 ∨ k4 ≠ 0) :
    neumannGapFloor L ≤ neumannEig4D L k1 k2 k3 k4 ∧ 0 < neumannGapFloor L := by
  refine ⟨?_, neumannGapFloor_pos L hL⟩
  unfold neumannEig4D
  have h1 := neumannEig1D_nonneg L k1
  have h2 := neumannEig1D_nonneg L k2
  have h3 := neumannEig1D_nonneg L k3
  have h4 := neumannEig1D_nonneg L k4
  rcases hne with hne1 | hne2 | hne3 | hne4
  · have hg := neumannEig1D_ge_floor L k1 hL (Nat.pos_of_ne_zero hne1) hk1; linarith
  · have hg := neumannEig1D_ge_floor L k2 hL (Nat.pos_of_ne_zero hne2) hk2; linarith
  · have hg := neumannEig1D_ge_floor L k3 hL (Nat.pos_of_ne_zero hne3) hk3; linarith
  · have hg := neumannEig1D_ge_floor L k4 hL (Nat.pos_of_ne_zero hne4) hk4; linarith

end YangMills
