import Mathlib.MeasureTheory.Constructions.Pi
import YangMills.CompactGroupSeat
import YangMills.SU3CompactSeat

/-!
# Module 23: LatticeHaarMeasure (Lean 4 + Mathlib4)
Constructs the concrete finite-volume product Haar probability measure `latticeHaar μ N`
on `N`-link lattice gauge configurations `Fin N → G` (instantiated for both `SU(2)` and
`SU(3)`):
1. `latticeHaar μ N := Measure.pi (fun _ : Fin N => μ)` is a probability measure.
2. Exact invariance of `latticeHaar μ N` under arbitrary local link-by-link gauge
   transformations `U i ↦ gL i * U i * gR i` (`latticeHaar_map_gaugeTransform` and
   `latticeHaar_integral_gauge_inv`).
3. Uniform bounds and strict positivity of the concrete finite-volume lattice Wilson
   partition function `Z(β) = ∫ exp(-β S(U)) dμ^⊗N` (`latticePartition_bounds`,
   `latticePartition_pos`).
4. Exact gauge invariance of concrete finite-volume lattice Wilson expectations
   (`latticeExpect_gauge_invariant`), plus direct `SU(2)` and `SU(3)` instantiations.
-/

namespace YangMills

open MeasureTheory Topology

/-! ## 1. Finite-Volume Product Haar Measure on `N` Lattice Links -/

/-- Concrete product Haar measure on `N`-link gauge configurations `Fin N → G`. -/
noncomputable def latticeHaar {G : Type*} [MeasurableSpace G]
    (μ : Measure G) (N : ℕ) : Measure (Fin N → G) :=
  Measure.pi (fun _ : Fin N => μ)

instance latticeHaar_isProbabilityMeasure {G : Type*} [MeasurableSpace G]
    (μ : Measure G) [IsProbabilityMeasure μ] (N : ℕ) :
    IsProbabilityMeasure (latticeHaar μ N) := by
  unfold latticeHaar
  infer_instance

/-- Local link-by-link gauge transformation `U i ↦ gL i * U i * gR i` on `N` links. -/
def gaugeTransform {G : Type*} [Mul G] {N : ℕ}
    (gL gR : Fin N → G) (U : Fin N → G) : Fin N → G :=
  fun i => gL i * U i * gR i

theorem measurable_gaugeTransform {G : Type*} [Mul G] [MeasurableSpace G] [MeasurableMul G]
    {N : ℕ} (gL gR : Fin N → G) :
    Measurable (gaugeTransform gL gR) :=
  Measurable.of_eval fun i =>
    (measurable_mul_const (gR i)).comp
      ((measurable_const_mul (gL i)).comp (measurable_pi_apply i))

/-- Single-link two-sided Haar invariance for measurable sets. -/
theorem measure_preimage_mul_left_right {G : Type*} [Group G] [MeasurableSpace G]
    [MeasurableMul G] (μ : Measure G) [μ.IsMulLeftInvariant] [μ.IsMulRightInvariant]
    (gL gR : G) {s : Set G} (hs : MeasurableSet s) :
    μ ((fun x : G => gL * x * gR) ⁻¹' s) = μ s := by
  have h1 : (fun x : G => gL * x * gR) ⁻¹' s =
      (fun x : G => gL * x) ⁻¹' ((fun x : G => x * gR) ⁻¹' s) := by
    ext x; rfl
  rw [h1]
  have hL := Measure.IsMulLeftInvariant.map_mul_left_eq_self (μ := μ) gL
  have hR := Measure.IsMulRightInvariant.map_mul_right_eq_self (μ := μ) gR
  have hsR : MeasurableSet ((fun x : G => x * gR) ⁻¹' s) :=
    (measurable_mul_const gR) hs
  calc
    μ ((fun x : G => gL * x) ⁻¹' ((fun x : G => x * gR) ⁻¹' s))
        = Measure.map (fun x : G => gL * x) μ ((fun x : G => x * gR) ⁻¹' s) := by
          rw [Measure.map_apply (measurable_const_mul gL) hsR]
    _ = μ ((fun x : G => x * gR) ⁻¹' s) := by rw [hL]
    _ = Measure.map (fun x : G => x * gR) μ s := by
          rw [Measure.map_apply (measurable_mul_const gR) hs]
    _ = μ s := by rw [hR]

/-- Exact invariance of the `N`-link product Haar measure under local gauge transforms. -/
theorem latticeHaar_map_gaugeTransform {G : Type*} [Group G] [MeasurableSpace G]
    [MeasurableMul G] (μ : Measure G) [IsProbabilityMeasure μ]
    [μ.IsMulLeftInvariant] [μ.IsMulRightInvariant] {N : ℕ} (gL gR : Fin N → G) :
    Measure.map (gaugeTransform gL gR) (latticeHaar μ N) = latticeHaar μ N := by
  symm
  unfold latticeHaar
  apply Measure.pi_eq
  intro s hs
  rw [Measure.map_apply (measurable_gaugeTransform gL gR) (MeasurableSet.univ_pi hs)]
  have hpre : gaugeTransform gL gR ⁻¹' Set.univ.pi s =
      Set.univ.pi (fun i => (fun x : G => gL i * x * gR i) ⁻¹' s i) := by
    ext U
    simp [gaugeTransform, Set.mem_univ_pi]
  rw [hpre]
  change Measure.pi (fun _ : Fin N => μ)
      (Set.univ.pi (fun i => (fun x : G => gL i * x * gR i) ⁻¹' s i)) =
    ∏ i : Fin N, μ (s i)
  rw [Measure.pi_pi]
  refine Finset.prod_congr rfl fun i _ => ?_
  exact measure_preimage_mul_left_right μ (gL i) (gR i) (hs i)

/-- Bochner integral invariance of the `N`-link product Haar measure under gauge transforms. -/
theorem latticeHaar_integral_gauge_inv {G : Type*} [Group G] [MeasurableSpace G]
    [MeasurableMul G] (μ : Measure G) [IsProbabilityMeasure μ]
    [μ.IsMulLeftInvariant] [μ.IsMulRightInvariant] {N : ℕ}
    (gL gR : Fin N → G) (F : (Fin N → G) → ℝ)
    (hF : AEStronglyMeasurable F (latticeHaar μ N)) :
    ∫ U, F (gaugeTransform gL gR U) ∂(latticeHaar μ N) = ∫ U, F U ∂(latticeHaar μ N) := by
  have hmap := latticeHaar_map_gaugeTransform μ gL gR
  have hF' : AEStronglyMeasurable F (Measure.map (gaugeTransform gL gR) (latticeHaar μ N)) := by
    simpa [hmap] using hF
  have h := integral_map (measurable_gaugeTransform gL gR).aemeasurable hF'
  rw [hmap] at h
  exact h.symm

/-! ## 2. Concrete Finite-Volume Wilson Partition Function and Expectation -/

/-- Finite-volume lattice Wilson partition function `Z(β) = ∫ exp(-β S(U)) dμ^⊗N`. -/
noncomputable def latticePartition {G : Type*} [MeasurableSpace G]
    (μ : Measure G) (N : ℕ) (S : (Fin N → G) → ℝ) (beta : ℝ) : ℝ :=
  ∫ U, Real.exp (-(beta * S U)) ∂(latticeHaar μ N)

/-- Finite-volume lattice Wilson expectation `⟨F⟩ = Z(β)⁻¹ ∫ F(U) exp(-β S(U)) dμ^⊗N`. -/
noncomputable def latticeExpect {G : Type*} [MeasurableSpace G]
    (μ : Measure G) (N : ℕ) (S : (Fin N → G) → ℝ) (beta : ℝ) (F : (Fin N → G) → ℝ) : ℝ :=
  (latticePartition μ N S beta)⁻¹ *
    ∫ U, F U * Real.exp (-(beta * S U)) ∂(latticeHaar μ N)

/-- Uniform bounds `exp(-β M) ≤ Z(β) ≤ 1` for any bounded nonneg lattice action `0 ≤ S ≤ M`. -/
theorem latticePartition_bounds {G : Type*} [MeasurableSpace G]
    (μ : Measure G) [IsProbabilityMeasure μ] (N : ℕ)
    (S : (Fin N → G) → ℝ) (beta M : ℝ) (hbeta : 0 ≤ beta)
    (hS0 : ∀ U, 0 ≤ S U) (hSM : ∀ U, S U ≤ M)
    (hmeas : AEStronglyMeasurable (fun U => Real.exp (-(beta * S U))) (latticeHaar μ N)) :
    Real.exp (-(beta * M)) ≤ latticePartition μ N S beta ∧
      latticePartition μ N S beta ≤ 1 := by
  have hint : Integrable (fun U => Real.exp (-(beta * S U))) (latticeHaar μ N) := by
    refine Integrable.mono' (integrable_const (1 : ℝ)) hmeas (Filter.Eventually.of_forall fun U => ?_)
    rw [Real.norm_of_nonneg (Real.exp_pos _).le]
    exact Real.exp_le_one_iff.mpr (neg_nonpos.mpr (mul_nonneg hbeta (hS0 U)))
  constructor
  · have hlo := integral_mono (integrable_const (Real.exp (-(beta * M)))) hint fun U =>
      Real.exp_le_exp.mpr (neg_le_neg (mul_le_mul_of_nonneg_left (hSM U) hbeta))
    simpa [latticePartition] using hlo
  · have hhi := integral_mono hint (integrable_const (1 : ℝ)) fun U =>
      Real.exp_le_one_iff.mpr (neg_nonpos.mpr (mul_nonneg hbeta (hS0 U)))
    simpa [latticePartition] using hhi

/-- Strict positivity of the finite-volume lattice Wilson partition function `Z(β) > 0`. -/
theorem latticePartition_pos {G : Type*} [MeasurableSpace G]
    (μ : Measure G) [IsProbabilityMeasure μ] (N : ℕ)
    (S : (Fin N → G) → ℝ) (beta M : ℝ) (hbeta : 0 ≤ beta)
    (hS0 : ∀ U, 0 ≤ S U) (hSM : ∀ U, S U ≤ M)
    (hmeas : AEStronglyMeasurable (fun U => Real.exp (-(beta * S U))) (latticeHaar μ N)) :
    0 < latticePartition μ N S beta :=
  lt_of_lt_of_le (Real.exp_pos _) (latticePartition_bounds μ N S beta M hbeta hS0 hSM hmeas).1

/-- Exact gauge invariance of the finite-volume lattice Wilson expectation under local
    gauge transformations whenever the Wilson action `S` is gauge-invariant. -/
theorem latticeExpect_gauge_invariant {G : Type*} [Group G] [MeasurableSpace G]
    [MeasurableMul G] (μ : Measure G) [IsProbabilityMeasure μ]
    [μ.IsMulLeftInvariant] [μ.IsMulRightInvariant] {N : ℕ}
    (gL gR : Fin N → G) (S : (Fin N → G) → ℝ) (beta : ℝ) (F : (Fin N → G) → ℝ)
    (hS : ∀ U, S (gaugeTransform gL gR U) = S U)
    (hmeas : AEStronglyMeasurable
      (fun U => F U * Real.exp (-(beta * S U))) (latticeHaar μ N)) :
    latticeExpect μ N S beta (fun U => F (gaugeTransform gL gR U)) =
      latticeExpect μ N S beta F := by
  unfold latticeExpect
  congr 1
  have heq : (fun U => F (gaugeTransform gL gR U) * Real.exp (-(beta * S U))) =
      fun U => (fun V => F V * Real.exp (-(beta * S V))) (gaugeTransform gL gR U) := by
    funext U
    dsimp only
    rw [hS U]
  rw [heq]
  exact latticeHaar_integral_gauge_inv μ gL gR (fun V => F V * Real.exp (-(beta * S V))) hmeas

/-! ## 3. Concrete `SU(2)` and `SU(3)` Finite-Volume Lattice Haar Instantiations -/

/-- Concrete `N`-link product Haar probability measure for 4D `SU(2)` lattice gauge theory. -/
noncomputable def su2LatticeHaar (N : ℕ) : Measure (Fin N → SU2) :=
  latticeHaar su2Haar N

/-- Concrete `N`-link product Haar probability measure for 4D `SU(3)` lattice gauge theory. -/
noncomputable def su3LatticeHaar (N : ℕ) : Measure (Fin N → SU3) :=
  latticeHaar su3Haar N

theorem su2LatticeHaar_gauge_invariant {N : ℕ} (gL gR : Fin N → SU2) :
    Measure.map (gaugeTransform gL gR) (su2LatticeHaar N) = su2LatticeHaar N :=
  latticeHaar_map_gaugeTransform su2Haar gL gR

theorem su3LatticeHaar_gauge_invariant {N : ℕ} (gL gR : Fin N → SU3) :
    Measure.map (gaugeTransform gL gR) (su3LatticeHaar N) = su3LatticeHaar N :=
  latticeHaar_map_gaugeTransform su3Haar gL gR

theorem su2LatticePartition_pos (N : ℕ) (S : (Fin N → SU2) → ℝ) (beta M : ℝ)
    (hbeta : 0 ≤ beta) (hS0 : ∀ U, 0 ≤ S U) (hSM : ∀ U, S U ≤ M)
    (hmeas : AEStronglyMeasurable (fun U => Real.exp (-(beta * S U))) (su2LatticeHaar N)) :
    0 < latticePartition su2Haar N S beta :=
  latticePartition_pos su2Haar N S beta M hbeta hS0 hSM hmeas

theorem su3LatticePartition_pos (N : ℕ) (S : (Fin N → SU3) → ℝ) (beta M : ℝ)
    (hbeta : 0 ≤ beta) (hS0 : ∀ U, 0 ≤ S U) (hSM : ∀ U, S U ≤ M)
    (hmeas : AEStronglyMeasurable (fun U => Real.exp (-(beta * S U))) (su3LatticeHaar N)) :
    0 < latticePartition su3Haar N S beta :=
  latticePartition_pos su3Haar N S beta M hbeta hS0 hSM hmeas

end YangMills
