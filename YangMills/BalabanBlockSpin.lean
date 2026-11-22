import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import YangMills.GaugeLattice
import YangMills.NeumannSpectrum

/-!
# Module 19: BalabanBlockSpin (Lean 4 + Mathlib4)
Formalizes the foundational geometric and analytic machinery of a single Balaban
block-spin renormalization-group step on the 4D hypercubic lattice `ℤ⁴`:
1. Coarse `L`-block lattice coordinates (`blockOrigin`, `shiftN`) with exact block
   boundary shift identity `shiftN (blockOrigin L y) μ L = blockOrigin L (step y μ)`.
2. Gauge-covariant `L`-link parallel transport (`straightTransport`, `blockLink`) and
   exact fine-to-coarse gauge covariance (`blockLink_gauge_covariant`), yielding exact
   gauge invariance of the coarse Wilson plaquette action (`blockLink_plaquette_gauge_invariant`).
3. Explicit axial-gauge fixing along any lattice ray (`axialRayGauge`,
   `axial_gauge_trivializes_ray`) setting every link along the ray to `1 ∈ G`.
4. Gauge-invariant small-field / large-field plaquette dichotomy (`SmallFieldPlaquette`,
   `LargeFieldPlaquette`, `smallFieldPlaquette_gauge_invariant`).
5. Small-field fluctuation coercivity (`balaban_fluctuation_coercivity`) and Gaussian
   fluctuation weight suppression (`balaban_small_field_fluctuation_decay`) wired directly
   into `NeumannSpectrum.neumann_4d_spectral_floor` (`λ_min(L) = 4 sin²(π / (2L)) > 0`).
-/

namespace YangMills

/-! ## 1. 4D L-Block Lattice Geometry & Multi-Step Shifts -/

/-- Maps a coarse lattice site `y ∈ ℤ⁴` to the origin `L · y ∈ ℤ⁴` of its `L`-block. -/
def blockOrigin (L : ℕ) (y : Site) : Site :=
  fun α => (L : Int) * y α

/-- Iterated unit lattice shift `x ↦ x + n · e_μ`. -/
def shiftN (x : Site) (μ : Fin 4) : ℕ → Site
  | 0 => x
  | n + 1 => step (shiftN x μ n) μ

/-- Closed-form coordinate formula for `shiftN x μ n`. -/
theorem shiftN_apply (x : Site) (μ : Fin 4) (n : ℕ) (α : Fin 4) :
    shiftN x μ n α = if α = μ then x α + (n : Int) else x α := by
  induction n with
  | zero => simp [shiftN]
  | succ k ih =>
    simp only [shiftN, step, ih]
    split_ifs with h
    · push_cast
      omega
    · rfl

/-- Shifting a block origin `L` steps in direction `μ` lands on the adjacent block origin. -/
theorem shiftN_blockOrigin (L : ℕ) (y : Site) (μ : Fin 4) :
    shiftN (blockOrigin L y) μ L = blockOrigin L (step y μ) := by
  funext α
  rw [shiftN_apply]
  unfold blockOrigin step
  split_ifs with h
  · ring
  · rfl

/-! ## 2. Gauge-Covariant Block-Spin Parallel Transport -/

/-- Ordered parallel transport of `n` consecutive gauge links starting at `x` along `μ`. -/
def straightTransport {G : Type*} [Group G] (U : GaugeField G) (x : Site) (μ : Fin 4) : ℕ → G
  | 0 => 1
  | n + 1 => straightTransport U x μ n * U (shiftN x μ n) μ

/-- Coarse `L`-block link field formed by `L`-link parallel transport across each block. -/
def blockLink {G : Type*} [Group G] (L : ℕ) (U : GaugeField G) : GaugeField G :=
  fun y μ => straightTransport U (blockOrigin L y) μ L

/-- Exact local gauge covariance of `n`-link straight parallel transport in any group `G`. -/
theorem straightTransport_gauge_covariant {G : Type*} [Group G]
    (g : GaugeTransform G) (U : GaugeField G) (x : Site) (μ : Fin 4) (n : ℕ) :
    straightTransport (gaugeAct g U) x μ n =
      g x * straightTransport U x μ n * (g (shiftN x μ n))⁻¹ := by
  induction n with
  | zero => simp [straightTransport, shiftN]
  | succ k ih =>
    simp [straightTransport, ih, gaugeAct, shiftN, mul_assoc]

/-- Exact fine-to-coarse gauge covariance of the Balaban block-spin link operator:
    fine gauge transformation `g` acts on `blockLink L U` by the coarse restriction `y ↦ g(L y)`. -/
theorem blockLink_gauge_covariant {G : Type*} [Group G]
    (L : ℕ) (g : GaugeTransform G) (U : GaugeField G) :
    blockLink L (gaugeAct g U) =
      gaugeAct (fun y => g (blockOrigin L y)) (blockLink L U) := by
  funext y μ
  dsimp only [blockLink]
  rw [straightTransport_gauge_covariant, shiftN_blockOrigin]
  rfl

/-- Exact fine-lattice gauge invariance of the coarse block-spin Wilson plaquette action. -/
theorem blockLink_plaquette_gauge_invariant {G : Type*} [Group G]
    (χ : UnitaryTrace G) (beta : ℝ) (L : ℕ) (g : GaugeTransform G) (U : GaugeField G)
    (y : Site) (μ ν : Fin 4) :
    wilsonPlaquetteAction χ beta (blockLink L (gaugeAct g U)) y μ ν =
      wilsonPlaquetteAction χ beta (blockLink L U) y μ ν := by
  rw [blockLink_gauge_covariant]
  exact wilsonPlaquetteAction_gauge_invariant χ beta (fun z => g (blockOrigin L z))
    (blockLink L U) y μ ν

/-! ## 3. Axial-Gauge Fixing Along a Lattice Ray -/

/-- Membership on the positive lattice ray `{x0 + n e_μ | n ∈ ℕ}`. -/
def onRay (x0 : Site) (μ : Fin 4) (x : Site) : Prop :=
  (∀ α : Fin 4, α ≠ μ → x α = x0 α) ∧ x0 μ ≤ x μ

/-- Every point `shiftN x0 μ n` lies on the positive ray from `x0` in direction `μ`. -/
theorem shiftN_onRay (x0 : Site) (μ : Fin 4) (n : ℕ) :
    onRay x0 μ (shiftN x0 μ n) := by
  constructor
  · intro α hα
    rw [shiftN_apply, if_neg hα]
  · rw [shiftN_apply, if_pos rfl]
    omega

/-- Explicit axial-gauge transformation setting all links along the positive ray
    `{x0 + n e_μ | n ∈ ℕ}` to the group identity `1 ∈ G`. -/
noncomputable def axialRayGauge {G : Type*} [Group G]
    (U : GaugeField G) (x0 : Site) (μ : Fin 4) : GaugeTransform G :=
  open Classical in
  fun x => if onRay x0 μ x then straightTransport U x0 μ (x μ - x0 μ).toNat else 1

/-- Value of `axialRayGauge` at every ray site `x0 + n e_μ`. -/
theorem axialRayGauge_at_shiftN {G : Type*} [Group G]
    (U : GaugeField G) (x0 : Site) (μ : Fin 4) (n : ℕ) :
    axialRayGauge U x0 μ (shiftN x0 μ n) = straightTransport U x0 μ n := by
  unfold axialRayGauge
  rw [if_pos (shiftN_onRay x0 μ n)]
  have hdiff : (shiftN x0 μ n μ - x0 μ).toNat = n := by
    rw [shiftN_apply, if_pos rfl]
    omega
  rw [hdiff]

/-- Exact axial-gauge trivialization: after applying `axialRayGauge U x0 μ`, every link
    along the ray `{x0 + n e_μ | n ∈ ℕ}` equals `1 ∈ G`. -/
theorem axial_gauge_trivializes_ray {G : Type*} [Group G]
    (U : GaugeField G) (x0 : Site) (μ : Fin 4) (n : ℕ) :
    gaugeAct (axialRayGauge U x0 μ) U (shiftN x0 μ n) μ = 1 := by
  unfold gaugeAct
  have hstep : step (shiftN x0 μ n) μ = shiftN x0 μ (n + 1) := rfl
  rw [hstep, axialRayGauge_at_shiftN, axialRayGauge_at_shiftN]
  change straightTransport U x0 μ (n + 1) * (straightTransport U x0 μ (n + 1))⁻¹ = 1
  exact mul_inv_cancel _

/-! ## 4. Small-Field / Large-Field Indicator Split -/

/-- Small-field plaquette predicate: normalized plaquette action density is at most `pThresh`. -/
def SmallFieldPlaquette {G : Type*} [Group G]
    (χ : UnitaryTrace G) (U : GaugeField G) (x : Site) (μ ν : Fin 4) (pThresh : ℝ) : Prop :=
  1 - χ.reTrNorm (plaquette U x μ ν) ≤ pThresh

/-- Large-field plaquette predicate: normalized plaquette action density exceeds `pThresh`. -/
def LargeFieldPlaquette {G : Type*} [Group G]
    (χ : UnitaryTrace G) (U : GaugeField G) (x : Site) (μ ν : Fin 4) (pThresh : ℝ) : Prop :=
  pThresh < 1 - χ.reTrNorm (plaquette U x μ ν)

/-- Exact partition of every plaquette into the small-field or large-field region. -/
theorem small_or_large_field_dichotomy {G : Type*} [Group G]
    (χ : UnitaryTrace G) (U : GaugeField G) (x : Site) (μ ν : Fin 4) (pThresh : ℝ) :
    SmallFieldPlaquette χ U x μ ν pThresh ∨ LargeFieldPlaquette χ U x μ ν pThresh :=
  le_or_gt _ _

/-- Exact local gauge invariance of the small-field region. -/
theorem smallFieldPlaquette_gauge_invariant {G : Type*} [Group G]
    (χ : UnitaryTrace G) (g : GaugeTransform G) (U : GaugeField G)
    (x : Site) (μ ν : Fin 4) (pThresh : ℝ) :
    SmallFieldPlaquette χ (gaugeAct g U) x μ ν pThresh ↔
      SmallFieldPlaquette χ U x μ ν pThresh := by
  unfold SmallFieldPlaquette
  rw [plaquette_gauge_covariant, χ.conj_inv]

/-- Exact local gauge invariance of the large-field region. -/
theorem largeFieldPlaquette_gauge_invariant {G : Type*} [Group G]
    (χ : UnitaryTrace G) (g : GaugeTransform G) (U : GaugeField G)
    (x : Site) (μ ν : Fin 4) (pThresh : ℝ) :
    LargeFieldPlaquette χ (gaugeAct g U) x μ ν pThresh ↔
      LargeFieldPlaquette χ U x μ ν pThresh := by
  unfold LargeFieldPlaquette
  rw [plaquette_gauge_covariant, χ.conj_inv]

/-! ## 5. Small-Field Fluctuation Coercivity (Wired to NeumannSpectrum) -/

/-- Squared `ℓ²` norm of a 4D block fluctuation mode table `c : (Fin L)⁴ → ℝ`. -/
def fluctuationNormSq (L : ℕ) (c : Fin L → Fin L → Fin L → Fin L → ℝ) : ℝ :=
  ∑ k1 : Fin L, ∑ k2 : Fin L, ∑ k3 : Fin L, ∑ k4 : Fin L, (c k1 k2 k3 k4) ^ 2

/-- 4D discrete Neumann Dirichlet/kinetic quadratic form `⟨c, (-Δ_N) c⟩` on an `L⁴` block. -/
noncomputable def neumannQuadraticForm (L : ℕ) (c : Fin L → Fin L → Fin L → Fin L → ℝ) : ℝ :=
  ∑ k1 : Fin L, ∑ k2 : Fin L, ∑ k3 : Fin L, ∑ k4 : Fin L,
    neumannEig4D L k1.val k2.val k3.val k4.val * (c k1 k2 k3 k4) ^ 2

/-- Balaban Small-Field Fluctuation Coercivity:
    for any block scale `L ≥ 2` and any zero-block-average fluctuation field (`c(0,0,0,0) = 0`),
    the 4D Neumann quadratic form is uniformly bounded below by
    `λ_min(L) · ‖c‖₂² = 4 sin²(π / (2L)) · ‖c‖₂²` with strictly positive floor `λ_min(L) > 0`. -/
theorem balaban_fluctuation_coercivity (L : ℕ) (hL : 2 ≤ L)
    (c : Fin L → Fin L → Fin L → Fin L → ℝ)
    (hzero : ∀ k1 k2 k3 k4 : Fin L,
      k1.val = 0 → k2.val = 0 → k3.val = 0 → k4.val = 0 → c k1 k2 k3 k4 = 0) :
    neumannGapFloor L * fluctuationNormSq L c ≤ neumannQuadraticForm L c ∧
      0 < neumannGapFloor L := by
  refine ⟨?_, neumannGapFloor_pos L hL⟩
  unfold fluctuationNormSq neumannQuadraticForm
  simp only [Finset.mul_sum]
  refine Finset.sum_le_sum fun k1 _ => Finset.sum_le_sum fun k2 _ =>
    Finset.sum_le_sum fun k3 _ => Finset.sum_le_sum fun k4 _ => ?_
  by_cases h0 : k1.val = 0 ∧ k2.val = 0 ∧ k3.val = 0 ∧ k4.val = 0
  · rcases h0 with ⟨h1, h2, h3, h4⟩
    rw [hzero k1 k2 k3 k4 h1 h2 h3 h4]
    simp
  · have hne : k1.val ≠ 0 ∨ k2.val ≠ 0 ∨ k3.val ≠ 0 ∨ k4.val ≠ 0 := by
      by_contra hall
      push Not at hall
      exact h0 hall
    have hfloor := (neumann_4d_spectral_floor L k1.val k2.val k3.val k4.val hL
      k1.isLt k2.isLt k3.isLt k4.isLt hne).1
    exact mul_le_mul_of_nonneg_right hfloor (sq_nonneg _)

/-- Small-field Gaussian fluctuation weight suppression:
    for `β ≥ 0` and any zero-average fluctuation mode `c`, the Boltzmann weight satisfies
    `exp(-β ⟨c, (-Δ_N) c⟩) ≤ exp(-β λ_min(L) ‖c‖₂²)`. -/
theorem balaban_small_field_fluctuation_decay (L : ℕ) (hL : 2 ≤ L) (beta : ℝ) (hbeta : 0 ≤ beta)
    (c : Fin L → Fin L → Fin L → Fin L → ℝ)
    (hzero : ∀ k1 k2 k3 k4 : Fin L,
      k1.val = 0 → k2.val = 0 → k3.val = 0 → k4.val = 0 → c k1 k2 k3 k4 = 0) :
    Real.exp (-(beta * neumannQuadraticForm L c)) ≤
      Real.exp (-(beta * (neumannGapFloor L * fluctuationNormSq L c))) := by
  have hcoerc := (balaban_fluctuation_coercivity L hL c hzero).1
  apply Real.exp_le_exp.mpr
  have hmul := mul_le_mul_of_nonneg_left hcoerc hbeta
  linarith

end YangMills
