import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import YangMills.AnalyticBounds
import YangMills.RenewalAndCauchy

/-!
# Module 7: ClusterExpansion (Lean 4 + Mathlib4)
Bridges the certified five-toll polymer decay exponent μ₀(8) ≥ 2 to OS4 exponential clustering:
1. Repaired Theorem BBF unordered-subtree exponential bound under the Kotecký–Preiss criterion.
2. Half-exponent split and exponential clustering extraction |S₂ᵀ(x, y)| ≤ C exp(-m₀ |x - y|)
   with physical mass gap floor m₀ = μ₀ / (2 R_stop).
3. Exact 4D Euclidean L² ≤ L¹ norm comparison.
4. End-to-end chain from `AnalyticBounds` + `RenewalAndCauchy` to m₀ ≥ R_stop⁻¹ > 0
   and the single-line renewal race.
-/

namespace YangMills

/-! ## 1. Kotecký–Preiss Criterion & Unordered-Subtree Bound (Repaired Theorem BBF) -/

/-- Kotecký–Preiss (KP) polymer criterion at root polymer p0 over incompatible set S. -/
def SatisfiesKPCriterion {ι : Type*} (S : Finset ι) (w a : ι → ℝ) (p0 : ι) : Prop :=
  (∑ p ∈ S, |w p| * Real.exp (a p)) ≤ a p0

/-- Repaired Theorem BBF (unordered-subtree induction step):
    if each child subtree sum T(p) satisfies 0 ≤ T(p) ≤ |w(p)| exp(a(p)) and S satisfies KP,
    then every finite unordered-subtree sum ∑_{d<N} (∑ T(p))^d / d! is bounded by exp(a(p0)). -/
theorem bbf_unordered_subtree_bound {ι : Type*}
    (S : Finset ι) (w a T : ι → ℝ) (p0 : ι)
    (hT0 : ∀ p ∈ S, 0 ≤ T p)
    (hTle : ∀ p ∈ S, T p ≤ |w p| * Real.exp (a p))
    (hKP : SatisfiesKPCriterion S w a p0)
    (N : ℕ) :
    (∑ d ∈ Finset.range N, (∑ p ∈ S, T p) ^ d / (d.factorial : ℝ)) ≤ Real.exp (a p0) := by
  have hT_nonneg : 0 ≤ ∑ p ∈ S, T p := Finset.sum_nonneg hT0
  have hT_le_a : (∑ p ∈ S, T p) ≤ a p0 := le_trans (Finset.sum_le_sum hTle) hKP
  calc
    (∑ d ∈ Finset.range N, (∑ p ∈ S, T p) ^ d / (d.factorial : ℝ))
      ≤ Real.exp (∑ p ∈ S, T p) := Real.sum_le_exp_of_nonneg hT_nonneg N
    _ ≤ Real.exp (a p0) := Real.exp_le_exp.mpr hT_le_a

/-! ## 2. Exponential Clustering Extraction (Theorem IV / OS4) -/

/-- Polymer-to-OS4 exponential clustering bound:
    if every connected polymer γ ∈ Γs has volume vol(γ) ≥ distXY / R_stop and weighted KP norm
    ∑ |w(γ)| exp(μ₀ · vol(γ)) ≤ C, then |∑ w(γ)| ≤ C exp(-m₀ · distXY) with m₀ = μ₀/(2 R_stop). -/
theorem polymer_exponential_clustering {ι : Type*}
    (Γs : Finset ι) (w vol : ι → ℝ) (mu0 Rstop distXY C : ℝ)
    (hmu : 0 ≤ mu0) (hR : 0 < Rstop) (hd : 0 ≤ distXY)
    (hvol : ∀ γ ∈ Γs, distXY / Rstop ≤ vol γ)
    (hKPnorm : (∑ γ ∈ Γs, |w γ| * Real.exp (mu0 * vol γ)) ≤ C) :
    |∑ γ ∈ Γs, w γ| ≤ C * Real.exp (-(mu0 / (2 * Rstop)) * distXY) := by
  set m0 : ℝ := mu0 / (2 * Rstop)
  have hterm : ∀ γ ∈ Γs,
      |w γ| ≤ |w γ| * Real.exp (mu0 * vol γ) * Real.exp (-(m0 * distXY)) := by
    intro γ hγ
    have hvol_ge : distXY / Rstop ≤ vol γ := hvol γ hγ
    have hvol_nonneg : 0 ≤ vol γ := le_trans (div_nonneg hd (le_of_lt hR)) hvol_ge
    have hm0d : m0 * distXY = (mu0 / 2) * (distXY / Rstop) := by
      dsimp [m0]
      ring
    have hstep1 : (mu0 / 2) * (distXY / Rstop) ≤ (mu0 / 2) * vol γ :=
      mul_le_mul_of_nonneg_left hvol_ge (by linarith)
    have hstep2 : (mu0 / 2) * vol γ ≤ mu0 * vol γ :=
      mul_le_mul_of_nonneg_right (by linarith) hvol_nonneg
    have hexp_le : Real.exp (m0 * distXY) ≤ Real.exp (mu0 * vol γ) :=
      Real.exp_le_exp.mpr (by linarith)
    have hmul1 : |w γ| * Real.exp (m0 * distXY) ≤ |w γ| * Real.exp (mu0 * vol γ) :=
      mul_le_mul_of_nonneg_left hexp_le (abs_nonneg _)
    have hmul2 := mul_le_mul_of_nonneg_right hmul1 (le_of_lt (Real.exp_pos (-(m0 * distXY))))
    have hcancel : |w γ| * Real.exp (m0 * distXY) * Real.exp (-(m0 * distXY)) = |w γ| := by
      rw [mul_assoc, ← Real.exp_add]
      simp
    rw [hcancel] at hmul2
    exact hmul2
  have hsum1 : |∑ γ ∈ Γs, w γ| ≤ ∑ γ ∈ Γs, |w γ| := Finset.abs_sum_le_sum_abs w Γs
  have hsum2 : (∑ γ ∈ Γs, |w γ|) ≤
      ∑ γ ∈ Γs, |w γ| * Real.exp (mu0 * vol γ) * Real.exp (-(m0 * distXY)) :=
    Finset.sum_le_sum hterm
  have hfact :
      (∑ γ ∈ Γs, |w γ| * Real.exp (mu0 * vol γ) * Real.exp (-(m0 * distXY))) =
        (∑ γ ∈ Γs, |w γ| * Real.exp (mu0 * vol γ)) * Real.exp (-(m0 * distXY)) := by
    rw [Finset.sum_mul]
  have hfinal :
      (∑ γ ∈ Γs, |w γ| * Real.exp (mu0 * vol γ)) * Real.exp (-(m0 * distXY)) ≤
        C * Real.exp (-(m0 * distXY)) :=
    mul_le_mul_of_nonneg_right hKPnorm (le_of_lt (Real.exp_pos (-(m0 * distXY))))
  have harg : -(m0 * distXY) = -m0 * distXY := by ring
  rw [← harg]
  linarith

/-! ## 3. Exact 4D L² ≤ L¹ Comparison -/

/-- In 4D Euclidean space, |x|₂² ≤ |x|₁² identically. -/
theorem l2_sq_le_l1_sq_4d (x0 x1 x2 x3 : ℝ) :
    x0 ^ 2 + x1 ^ 2 + x2 ^ 2 + x3 ^ 2 ≤ (|x0| + |x1| + |x2| + |x3|) ^ 2 := by
  have h0 : 0 ≤ |x0| := abs_nonneg x0
  have h1 : 0 ≤ |x1| := abs_nonneg x1
  have h2 : 0 ≤ |x2| := abs_nonneg x2
  have h3 : 0 ≤ |x3| := abs_nonneg x3
  have hdiff : (|x0| + |x1| + |x2| + |x3|) ^ 2 =
      |x0| ^ 2 + |x1| ^ 2 + |x2| ^ 2 + |x3| ^ 2 +
        2 * (|x0| * |x1| + |x0| * |x2| + |x0| * |x3| +
             |x1| * |x2| + |x1| * |x3| + |x2| * |x3|) := by ring
  rw [hdiff, sq_abs, sq_abs, sq_abs, sq_abs]
  have h01 := mul_nonneg h0 h1
  have h02 := mul_nonneg h0 h2
  have h03 := mul_nonneg h0 h3
  have h12 := mul_nonneg h1 h2
  have h13 := mul_nonneg h1 h3
  have h23 := mul_nonneg h2 h3
  linarith

/-! ## 4. Unified Five-Toll to Mass-Gap Floor Chain (Modules 3 + 4 + 7) -/

/-- End-to-end certified chain: from κ₀ ≥ 61516/10000 and the five-toll real surplus,
    the physical mass floor m₀ = μ₀(8) / (2 R_stop) satisfies m₀ ≥ R_stop⁻¹ > 0
    and wins the single-line renewal race 2 b₀ g_*² ln(m₀ / Λ_RG) ≥ 1. -/
theorem mass_gap_floor_from_five_tolls
    (κ₀ b0 gStarSq LambdaRG : ℝ)
    (hκ₀ : (61516 : ℝ) / 10000 ≤ κ₀)
    (hb0 : 0 < b0) (hg : 0 < gStarSq) (hL : 0 < LambdaRG) :
    let Δκ := κ₀ - (-Real.log (1 - (1 : ℝ) / 567)) - Real.log 16
                 - Real.log (8 * Real.exp 1) - ((1 : ℝ) / 567) ^ 2 * ((4319 : ℝ) / 10)
    let mu0 := 8 * Δκ
    let cMass := mu0 / 2
    let RstopInv := LambdaRG * Real.exp (1 / (2 * b0 * gStarSq))
    let m0 := cMass * RstopInv
    0 < m0 ∧ RstopInv ≤ m0 ∧ 1 ≤ 2 * b0 * gStarSq * Real.log (m0 / LambdaRG) := by
  intro Δκ mu0 cMass RstopInv m0
  have hsurplus := real_five_toll_surplus κ₀ hκ₀
  have hmu0 : (2 : ℝ) ≤ mu0 := hsurplus.2
  have hcm : (1 : ℝ) ≤ cMass := by dsimp [cMass]; linarith
  have hRinv_pos : 0 < RstopInv := mul_pos hL (Real.exp_pos _)
  have hm0_ge : RstopInv ≤ m0 := by
    dsimp [m0]
    have := mul_le_mul_of_nonneg_right hcm (le_of_lt hRinv_pos)
    simpa [one_mul] using this
  have hm0_pos : 0 < m0 := lt_of_lt_of_le hRinv_pos hm0_ge
  have hrace := single_line_renewal_race b0 gStarSq LambdaRG cMass hb0 hg hL hcm
  exact ⟨hm0_pos, hm0_ge, hrace⟩

end YangMills
