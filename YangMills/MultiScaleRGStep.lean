import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import YangMills.RenewalAndCauchy
import YangMills.BalabanBlockSpin
import YangMills.LargeFieldPeierls
import YangMills.SpectralGapBridge

/-!
# Module 22: MultiScaleRGStep (Lean 4 + Mathlib4)
Iterates the Balaban block-spin and small-field/large-field RG step across `k` scales
(`L^k`) and connects multi-scale cumulative polymer control directly to the completed
Hilbert-space spectral gap (`SpectralGapBridge`):
1. Iterated `k`-scale block origin `iterBlockOrigin L k y = L^k · y` and `k`-scale
   blocked gauge field `iterBlockLink L k U := (blockLink L)^[k] U`.
2. Exact multi-scale gauge covariance (`iterBlockLink_gauge_covariant`) and exact
   fine-lattice gauge invariance of the `k`-scale blocked Wilson plaquette action
   (`iterBlockLink_plaquette_gauge_invariant`) for every scale `k : ℕ`.
3. Multi-scale 1-loop running inverse coupling (`runningInvCoupling`) proving strict
   asymptotic-freedom monotonicity toward the UV (`runningInvCoupling_strict_mono_uv`).
4. Cumulative multi-scale polymer activity control (`multiscale_cumulative_activity_le`,
   `multiscale_dyadic_beats_bridge_cap`): any dyadically decaying per-scale activity
   increment `0 ≤ δ j ≤ a0 · (1/4)^j` sums to strictly less than `1/567` across ALL
   scales `K : ℕ` whenever `a0 ≤ (3/4) · exp(-L²) / (1 - exp(-1))` and `L ≥ 3`.
5. Unified multi-scale master theorem (`multiscale_balaban_to_hilbert_spectral_gap`)
   linking `k`-scale Balaban gauge invariance, uniform Neumann fluctuation coercivity,
   cumulative multi-scale KP corridor entry, and completed Hilbert-space spectral gap
   exclusion.
-/

namespace YangMills

/-! ## 1. Iterated k-Scale Balaban Block-Spin Operator -/

/-- Iterated `k`-scale block origin map `y ↦ L^k · y` on `ℤ⁴`. -/
def iterBlockOrigin (L : ℕ) : ℕ → Site → Site
  | 0, y => y
  | k + 1, y => blockOrigin L (iterBlockOrigin L k y)

/-- Closed-form coordinate formula `iterBlockOrigin L k y α = L^k · y α`. -/
theorem iterBlockOrigin_apply (L k : ℕ) (y : Site) (α : Fin 4) :
    iterBlockOrigin L k y α = ((L ^ k : ℕ) : Int) * y α := by
  induction k with
  | zero => simp [iterBlockOrigin]
  | succ n ih =>
    simp only [iterBlockOrigin, blockOrigin, ih, pow_succ, Nat.cast_mul]
    ring

/-- Iterated `k`-scale Balaban block-spin gauge field `U^{(k)}`. -/
def iterBlockLink {G : Type*} [Group G] (L : ℕ) : ℕ → GaugeField G → GaugeField G
  | 0, U => U
  | k + 1, U => blockLink L (iterBlockLink L k U)

/-- Exact multi-scale gauge covariance across `k` Balaban RG steps:
    a fine-lattice gauge transformation `g` acts on `U^{(k)}` by the `L^k`-coarse
    restriction `y ↦ g(L^k y)`. -/
theorem iterBlockLink_gauge_covariant {G : Type*} [Group G]
    (L k : ℕ) (g : GaugeTransform G) (U : GaugeField G) :
    iterBlockLink L k (gaugeAct g U) =
      gaugeAct (fun y => g (iterBlockOrigin L k y)) (iterBlockLink L k U) := by
  induction k generalizing g U with
  | zero => rfl
  | succ n ih =>
    simp only [iterBlockLink]
    rw [ih g U, blockLink_gauge_covariant]
    have hrestrict : (fun y => g (iterBlockOrigin L n (blockOrigin L y))) =
        (fun y => g (iterBlockOrigin L (n + 1) y)) := by
      funext y
      congr 1
      funext α
      rw [iterBlockOrigin_apply, iterBlockOrigin_apply]
      simp only [blockOrigin, pow_succ, Nat.cast_mul]
      ring
    rw [hrestrict]

/-- Exact fine-lattice gauge invariance of the `k`-scale blocked Wilson plaquette action
    at every RG scale `k : ℕ`. -/
theorem iterBlockLink_plaquette_gauge_invariant {G : Type*} [Group G]
    (χ : UnitaryTrace G) (beta : ℝ) (L k : ℕ) (g : GaugeTransform G) (U : GaugeField G)
    (y : Site) (μ ν : Fin 4) :
    wilsonPlaquetteAction χ beta (iterBlockLink L k (gaugeAct g U)) y μ ν =
      wilsonPlaquetteAction χ beta (iterBlockLink L k U) y μ ν := by
  rw [iterBlockLink_gauge_covariant]
  exact wilsonPlaquetteAction_gauge_invariant χ beta
    (fun z => g (iterBlockOrigin L k z)) (iterBlockLink L k U) y μ ν

/-! ## 2. Multi-Scale 1-Loop Running Coupling Trajectory -/

/-- UV-directed 1-loop running inverse coupling `1/g_k² = 1/g_*² + 2 b₀ k ln L`
    after `k` block-refinement steps of scale factor `L`. -/
noncomputable def runningInvCoupling (invGStarSq b0 : ℝ) (L k : ℕ) : ℝ :=
  invGStarSq + (k : ℝ) * (2 * b0 * Real.log (L : ℝ))

/-- Exact one-step recurrence for the running inverse coupling. -/
theorem runningInvCoupling_succ (invGStarSq b0 : ℝ) (L k : ℕ) :
    runningInvCoupling invGStarSq b0 L (k + 1) =
      runningInvCoupling invGStarSq b0 L k + 2 * b0 * Real.log (L : ℝ) := by
  unfold runningInvCoupling
  push_cast
  ring

/-- Strict asymptotic freedom toward the UV: for `b₀ > 0` and block factor `L ≥ 2`,
    each UV refinement step strictly increases `1/g_k²` (strictly decreases `g_k²`). -/
theorem runningInvCoupling_strict_mono_uv (invGStarSq b0 : ℝ) (L k : ℕ)
    (hb0 : 0 < b0) (hL : 2 ≤ L) :
    runningInvCoupling invGStarSq b0 L k < runningInvCoupling invGStarSq b0 L (k + 1) := by
  rw [runningInvCoupling_succ]
  have hL1 : (1 : ℝ) < (L : ℝ) := by
    have : (2 : ℝ) ≤ (L : ℝ) := by exact_mod_cast hL
    linarith
  have hlog : 0 < Real.log (L : ℝ) := Real.log_pos hL1
  have hstep : 0 < 2 * b0 * Real.log (L : ℝ) := by positivity
  linarith

/-! ## 3. Cumulative Multi-Scale Polymer Activity & Cauchy Tower Control -/

/-- Uniform multi-scale cumulative activity bound:
    if each RG scale `j` contributes non-negative polymer activity `δ j ≤ a0 · (1/4)^j`,
    then the cumulative activity across ANY number `K` of RG scales is strictly bounded
    above by `(4 / 3) * a0` (when `a0 > 0`) and bounded by `(4 / 3) * a0` for all `a0 ≥ 0`. -/
theorem multiscale_cumulative_activity_le (δ : ℕ → ℝ) (a0 : ℝ) (ha0 : 0 ≤ a0)
    (hstep : ∀ j : ℕ, δ j ≤ a0 * ((1 : ℝ) / 4) ^ j) (K : ℕ) :
    (∑ j ∈ Finset.range K, δ j) ≤ (4 : ℝ) / 3 * a0 := by
  have h1 : (∑ j ∈ Finset.range K, δ j) ≤
      ∑ j ∈ Finset.range K, a0 * ((1 : ℝ) / 4) ^ j :=
    Finset.sum_le_sum fun j _ => hstep j
  have h2 : (∑ j ∈ Finset.range K, a0 * ((1 : ℝ) / 4) ^ j) =
      a0 * ∑ j ∈ Finset.range K, ((1 : ℝ) / 4) ^ j := by
    rw [Finset.mul_sum]
  have h3 : (∑ j ∈ Finset.range K, ((1 : ℝ) / 4) ^ j) ≤ (4 : ℝ) / 3 :=
    le_of_lt (cauchy_tower_partial_lt_four_thirds K)
  have h4 : a0 * (∑ j ∈ Finset.range K, ((1 : ℝ) / 4) ^ j) ≤ a0 * ((4 : ℝ) / 3) :=
    mul_le_mul_of_nonneg_left h3 ha0
  linarith

/-- Multi-scale Peierls + Cauchy tower beats the `1/567` KP bridge ceiling uniformly in `K`:
    if `L ≥ 3`, `0 ≤ δ j ≤ a0 · (1/4)^j`, and `a0 ≤ (3/4) · exp(-L²) / (1 - exp(-1))`,
    then for EVERY number of RG scales `K : ℕ`, the cumulative activity
    `∑_{j=0}^{K-1} δ_j` is non-negative and strictly less than `1 / 567`. -/
theorem multiscale_dyadic_beats_bridge_cap (L K : ℕ) (hL : 3 ≤ L)
    (δ : ℕ → ℝ) (a0 : ℝ)
    (hδ0 : ∀ j : ℕ, 0 ≤ δ j) (ha0 : 0 ≤ a0)
    (hstep : ∀ j : ℕ, δ j ≤ a0 * ((1 : ℝ) / 4) ^ j)
    (ha0_peierls : a0 ≤ (3 : ℝ) / 4 * (Real.exp (-((L * L : ℕ) : ℝ)) / (1 - Real.exp (-1)))) :
    0 ≤ (∑ j ∈ Finset.range K, δ j) ∧
      (∑ j ∈ Finset.range K, δ j) < (1 : ℝ) / 567 := by
  have hnonneg : 0 ≤ ∑ j ∈ Finset.range K, δ j :=
    Finset.sum_nonneg fun j _ => hδ0 j
  have hcum : (∑ j ∈ Finset.range K, δ j) ≤ (4 : ℝ) / 3 * a0 :=
    multiscale_cumulative_activity_le δ a0 ha0 hstep K
  have hA0 : 7 ≤ L * L := by nlinarith
  have hcap : Real.exp (-((L * L : ℕ) : ℝ)) / (1 - Real.exp (-1)) < (1 : ℝ) / 567 :=
    peierls_envelope_lt_bridge_cap (L * L) hA0
  have hmul : (4 : ℝ) / 3 * a0 ≤ Real.exp (-((L * L : ℕ) : ℝ)) / (1 - Real.exp (-1)) := by
    linarith
  exact ⟨hnonneg, lt_of_le_of_lt (le_trans hcum hmul) hcap⟩

/-! ## 4. Unified Multi-Scale Balaban → Completed Hilbert Spectral Gap Master Theorem -/

/-- End-to-end Multi-Scale Balaban RG to Completed Hilbert-Space Spectral Gap:
    for any block scale `L ≥ 3`, any number of RG scales `K : ℕ`, any dyadic per-scale
    polymer activity increments `0 ≤ δ j ≤ a0 · (1/4)^j` bounded by the `L²`-area Peierls
    envelope, `κ₀ ≥ 6.1516`, and bounded transfer operator `T : E →L[ℝ] E` satisfying the
    corridor squared-norm decay rate `m0 := corridorMassFloor κ₀ b0 gStarSq LambdaRG`:
    1. Strictly positive small-field Neumann fluctuation gap floor `0 < neumannGapFloor L`.
    2. Strict cumulative KP corridor entry `InKPCorridor κ₀ (∑_{j=0}^{K-1} δ j)` uniformly
       in `K`.
    3. Strictly positive mass floor `0 < m0`, `R_stop⁻¹ ≤ m0`, and renewal-race victory.
    4. Iterated Hilbert-space transfer decay `‖T̂^n ψ‖ ≤ exp(-m₀ n) ‖ψ‖` for all `n : ℕ`.
    5. Rayleigh-quotient bound `|⟨ψ, T̂ ψ⟩| ≤ exp(-m₀) ‖ψ‖²`.
    6. Full continuous + point spectral gap exclusion for every energy `E_val < m₀`. -/
theorem multiscale_balaban_to_hilbert_spectral_gap
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (T : E →L[ℝ] E)
    (L K : ℕ) (hL : 3 ≤ L)
    (δ : ℕ → ℝ) (a0 κ₀ b0 gStarSq LambdaRG : ℝ)
    (hκ₀ : (61516 : ℝ) / 10000 ≤ κ₀)
    (hδ0 : ∀ j : ℕ, 0 ≤ δ j) (ha0 : 0 ≤ a0)
    (hstep : ∀ j : ℕ, δ j ≤ a0 * ((1 : ℝ) / 4) ^ j)
    (ha0_peierls : a0 ≤ (3 : ℝ) / 4 * (Real.exp (-((L * L : ℕ) : ℝ)) / (1 - Real.exp (-1))))
    (hb0 : 0 < b0) (hgStar : 0 < gStarSq) (hLambda : 0 < LambdaRG)
    (hsq : ∀ x : E, ‖T x‖ ^ 2 ≤
      Real.exp (-2 * corridorMassFloor κ₀ b0 gStarSq LambdaRG) * ‖x‖ ^ 2) :
    let epsCum := ∑ j ∈ Finset.range K, δ j
    let m0 := corridorMassFloor κ₀ b0 gStarSq LambdaRG
    let RstopInv := LambdaRG * Real.exp (1 / (2 * b0 * gStarSq))
    0 < neumannGapFloor L ∧
    InKPCorridor κ₀ epsCum ∧
    0 < m0 ∧
    RstopInv ≤ m0 ∧
    1 ≤ 2 * b0 * gStarSq * Real.log (m0 / LambdaRG) ∧
    (∀ (n : ℕ) (ψ : UniformSpace.Completion E),
      ‖(liftOperator T)^[n] ψ‖ ≤ Real.exp (-m0 * (n : ℝ)) * ‖ψ‖) ∧
    (∀ ψ : UniformSpace.Completion E,
      |inner ℝ ψ (liftOperator T ψ)| ≤ Real.exp (-m0) * ‖ψ‖ ^ 2) ∧
    (∀ (E_val : ℝ), E_val < m0 → ∀ ψ : UniformSpace.Completion E,
      (Real.exp (-E_val) - Real.exp (-m0)) * ‖ψ‖ ≤
        ‖liftOperator T ψ - Real.exp (-E_val) • ψ‖) := by
  intro epsCum m0 RstopInv
  have hL2 : 2 ≤ L := by omega
  have hcum := multiscale_dyadic_beats_bridge_cap L K hL δ a0 hδ0 ha0 hstep ha0_peierls
  have hcorr : InKPCorridor κ₀ epsCum := ⟨hκ₀, hcum.1, le_of_lt hcum.2⟩
  have hspec := corridor_to_hilbert_spectral_gap T κ₀ epsCum b0 gStarSq LambdaRG
    hcorr hb0 hgStar hLambda hsq
  exact ⟨neumannGapFloor_pos L hL2, hcorr, hspec.1, hspec.2.1, hspec.2.2.1,
    hspec.2.2.2.1, hspec.2.2.2.2.1, hspec.2.2.2.2.2⟩

end YangMills
