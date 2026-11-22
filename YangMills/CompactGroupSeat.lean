import Mathlib.MeasureTheory.Measure.Haar.Unique
import YangMills.SU2Seat
import YangMills.HaarMeasureSeat

/-!
# Module 17: CompactGroupSeat (Lean 4 + Mathlib4)
Equips our concrete non-Abelian unit-quaternion group `SU2` (`SU2Seat.lean`) with its
compact Hausdorff topological group structure (`S³ ⊂ ℝ⁴`), Borel measurable space, and
Mathlib's actual normalized bi-invariant Haar probability measure `su2Haar`:
1. Topological embedding `SU2.toVec : SU2 → ℝ × ℝ × ℝ × ℝ`, yielding `T2Space SU2`,
   `SecondCountableTopology SU2`, and `CompactSpace SU2` (closed subset of `[-1, 1]⁴`).
2. Continuity of Hamilton quaternion multiplication and inversion (`IsTopologicalGroup SU2`),
   Borel `MeasurableSpace SU2`, and `MeasurableMul SU2`.
3. Concrete normalized Haar probability measure `su2Haar : Measure SU2` via
   `Measure.haarMeasure`, with `IsProbabilityMeasure su2Haar`, `IsMulLeftInvariant`,
   and `IsMulRightInvariant` (automatic unimodularity from compactness).
4. Concrete `SU2` Bochner Haar invariance (`su2Haar_integral_conj_inv`), strict positivity
   and uniform bounds of the concrete `SU2` Wilson plaquette integral
   (`su2Haar_wilson_plaquette_bounds`, `su2Haar_wilson_plaquette_pos`), and concrete
   `SU2 × SU2` half-space reflection positivity (`su2Haar_reflection_positive_square`).
-/

namespace YangMills

open MeasureTheory Topology

namespace SU2

/-- Coordinate embedding `SU(2) ≅ S³ ↪ ℝ⁴`. -/
def toVec (u : SU2) : ℝ × ℝ × ℝ × ℝ := (u.a, u.b, u.c, u.d)

theorem toVec_injective : Function.Injective toVec := by
  intro x y h
  simp only [toVec, Prod.mk.injEq] at h
  ext
  · exact h.1
  · exact h.2.1
  · exact h.2.2.1
  · exact h.2.2.2

instance : Nonempty SU2 := ⟨1⟩

instance : TopologicalSpace SU2 :=
  TopologicalSpace.induced toVec inferInstance

theorem isInducing_toVec : IsInducing toVec := ⟨rfl⟩

theorem isEmbedding_toVec : IsEmbedding toVec :=
  ⟨isInducing_toVec, toVec_injective⟩

theorem continuous_toVec : Continuous toVec :=
  isInducing_toVec.continuous

theorem continuous_a : Continuous SU2.a :=
  continuous_fst.comp continuous_toVec

theorem continuous_b : Continuous SU2.b :=
  (continuous_fst.comp continuous_snd).comp continuous_toVec

theorem continuous_c : Continuous SU2.c :=
  (continuous_fst.comp (continuous_snd.comp continuous_snd)).comp continuous_toVec

theorem continuous_d : Continuous SU2.d :=
  (continuous_snd.comp (continuous_snd.comp continuous_snd)).comp continuous_toVec

instance : T2Space SU2 :=
  isEmbedding_toVec.t2Space

instance : SecondCountableTopology SU2 :=
  isInducing_toVec.secondCountableTopology

theorem range_toVec_eq :
    Set.range toVec =
      {p : ℝ × ℝ × ℝ × ℝ | p.1 ^ 2 + p.2.1 ^ 2 + p.2.2.1 ^ 2 + p.2.2.2 ^ 2 = 1} := by
  ext ⟨a, b, c, d⟩
  simp only [Set.mem_range, Set.mem_ofPred_eq, toVec]
  constructor
  · rintro ⟨u, hu⟩
    simp only [Prod.mk.injEq] at hu
    rcases hu with ⟨rfl, rfl, rfl, rfl⟩
    exact u.norm_sq
  · intro h
    exact ⟨⟨a, b, c, d, h⟩, rfl⟩

theorem isCompact_range_toVec : IsCompact (Set.range toVec) := by
  rw [range_toVec_eq]
  let box : Set (ℝ × ℝ × ℝ × ℝ) :=
    Set.Icc (-1 : ℝ) 1 ×ˢ (Set.Icc (-1 : ℝ) 1 ×ˢ (Set.Icc (-1 : ℝ) 1 ×ˢ Set.Icc (-1 : ℝ) 1))
  have hbox : IsCompact box :=
    isCompact_Icc.prod (isCompact_Icc.prod (isCompact_Icc.prod isCompact_Icc))
  have hclosed : IsClosed
      {p : ℝ × ℝ × ℝ × ℝ | p.1 ^ 2 + p.2.1 ^ 2 + p.2.2.1 ^ 2 + p.2.2.2 ^ 2 = 1} := by
    have hcont : Continuous
        (fun p : ℝ × ℝ × ℝ × ℝ => p.1 ^ 2 + p.2.1 ^ 2 + p.2.2.1 ^ 2 + p.2.2.2 ^ 2) := by
      have h1 : Continuous (fun p : ℝ × ℝ × ℝ × ℝ => p.1) := continuous_fst
      have h2 : Continuous (fun p : ℝ × ℝ × ℝ × ℝ => p.2.1) := continuous_fst.comp continuous_snd
      have h3 : Continuous (fun p : ℝ × ℝ × ℝ × ℝ => p.2.2.1) :=
        continuous_fst.comp (continuous_snd.comp continuous_snd)
      have h4 : Continuous (fun p : ℝ × ℝ × ℝ × ℝ => p.2.2.2) :=
        continuous_snd.comp (continuous_snd.comp continuous_snd)
      exact (((h1.pow 2).add (h2.pow 2)).add (h3.pow 2)).add (h4.pow 2)
    exact isClosed_eq hcont continuous_const
  have hsub : {p : ℝ × ℝ × ℝ × ℝ | p.1 ^ 2 + p.2.1 ^ 2 + p.2.2.1 ^ 2 + p.2.2.2 ^ 2 = 1} ⊆ box := by
    rintro ⟨a, b, c, d⟩ h
    simp only [Set.mem_ofPred_eq] at h
    have ha : a ^ 2 ≤ 1 := by linarith [sq_nonneg b, sq_nonneg c, sq_nonneg d]
    have hb : b ^ 2 ≤ 1 := by linarith [sq_nonneg a, sq_nonneg c, sq_nonneg d]
    have hc : c ^ 2 ≤ 1 := by linarith [sq_nonneg a, sq_nonneg b, sq_nonneg d]
    have hd : d ^ 2 ≤ 1 := by linarith [sq_nonneg a, sq_nonneg b, sq_nonneg c]
    refine ⟨⟨by nlinarith, by nlinarith⟩, ⟨by nlinarith, by nlinarith⟩,
      ⟨by nlinarith, by nlinarith⟩, ⟨by nlinarith, by nlinarith⟩⟩
  exact hbox.of_isClosed_subset hclosed hsub

instance : CompactSpace SU2 := by
  refine ⟨?_⟩
  rw [isInducing_toVec.isCompact_iff, Set.image_univ]
  exact isCompact_range_toVec

instance : ContinuousMul SU2 where
  continuous_mul := by
    rw [isInducing_toVec.continuous_iff]
    have ha1 : Continuous (fun p : SU2 × SU2 => p.1.a) := continuous_a.comp continuous_fst
    have hb1 : Continuous (fun p : SU2 × SU2 => p.1.b) := continuous_b.comp continuous_fst
    have hc1 : Continuous (fun p : SU2 × SU2 => p.1.c) := continuous_c.comp continuous_fst
    have hd1 : Continuous (fun p : SU2 × SU2 => p.1.d) := continuous_d.comp continuous_fst
    have ha2 : Continuous (fun p : SU2 × SU2 => p.2.a) := continuous_a.comp continuous_snd
    have hb2 : Continuous (fun p : SU2 × SU2 => p.2.b) := continuous_b.comp continuous_snd
    have hc2 : Continuous (fun p : SU2 × SU2 => p.2.c) := continuous_c.comp continuous_snd
    have hd2 : Continuous (fun p : SU2 × SU2 => p.2.d) := continuous_d.comp continuous_snd
    have hca : Continuous (fun p : SU2 × SU2 => (p.1 * p.2).a) :=
      (((ha1.mul ha2).sub (hb1.mul hb2)).sub (hc1.mul hc2)).sub (hd1.mul hd2)
    have hcb : Continuous (fun p : SU2 × SU2 => (p.1 * p.2).b) :=
      (((ha1.mul hb2).add (hb1.mul ha2)).add (hc1.mul hd2)).sub (hd1.mul hc2)
    have hcc : Continuous (fun p : SU2 × SU2 => (p.1 * p.2).c) :=
      (((ha1.mul hc2).sub (hb1.mul hd2)).add (hc1.mul ha2)).add (hd1.mul hb2)
    have hcd : Continuous (fun p : SU2 × SU2 => (p.1 * p.2).d) :=
      (((ha1.mul hd2).add (hb1.mul hc2)).sub (hc1.mul hb2)).add (hd1.mul ha2)
    exact hca.prodMk (hcb.prodMk (hcc.prodMk hcd))

instance : ContinuousInv SU2 where
  continuous_inv := by
    rw [isInducing_toVec.continuous_iff]
    exact continuous_a.prodMk
      (continuous_b.neg.prodMk (continuous_c.neg.prodMk continuous_d.neg))

instance : IsTopologicalGroup SU2 where

instance : MeasurableSpace SU2 := borel SU2

instance : BorelSpace SU2 := ⟨rfl⟩

/-- The whole compact group `SU(2)` as a `PositiveCompacts SU2` normalization set. -/
def univCompact : TopologicalSpace.PositiveCompacts SU2 where
  carrier := Set.univ
  isCompact' := isCompact_univ
  interior_nonempty' := by simp

end SU2

/-! ## Concrete Normalized Bi-Invariant Haar Measure on SU(2) -/

/-- Mathlib's concrete normalized bi-invariant Haar probability measure on `SU(2) ≅ S³`. -/
noncomputable def su2Haar : Measure SU2 :=
  Measure.haarMeasure SU2.univCompact

instance : su2Haar.IsHaarMeasure :=
  Measure.isHaarMeasure_haarMeasure SU2.univCompact

instance : IsProbabilityMeasure su2Haar := by
  refine ⟨?_⟩
  have h := Measure.haarMeasure_self (K₀ := SU2.univCompact)
  simpa [su2Haar, SU2.univCompact] using h

/-- Unimodularity of compact `SU(2)`: left-invariant probability Haar measure is right-invariant. -/
instance : su2Haar.IsMulRightInvariant := by
  refine ⟨fun g => ?_⟩
  set ν : Measure SU2 := Measure.map (fun x => x * g) su2Haar
  have hmeas_r : Measurable (fun x : SU2 => x * g) := measurable_mul_const g
  have : IsProbabilityMeasure ν :=
    ⟨by rw [Measure.map_apply hmeas_r MeasurableSet.univ]; simp⟩
  have : ν.IsMulLeftInvariant := by
    refine ⟨fun h => ?_⟩
    have hmeas_l : Measurable (fun x : SU2 => h * x) := measurable_const_mul h
    change Measure.map (fun x => h * x) (Measure.map (fun x => x * g) su2Haar) =
      Measure.map (fun x => x * g) su2Haar
    rw [Measure.map_map hmeas_l hmeas_r]
    have hcomm : (fun x : SU2 => h * x) ∘ (fun x : SU2 => x * g) =
        (fun x : SU2 => x * g) ∘ (fun x : SU2 => h * x) := by
      funext x; simp [mul_assoc]
    rw [hcomm, ← Measure.map_map hmeas_r hmeas_l,
        Measure.IsMulLeftInvariant.map_mul_left_eq_self (μ := su2Haar) h]
  have huniq := MeasureTheory.measure_eq_div_smul (s := Set.univ) ν su2Haar
    (by simp) (by simp)
  simp only [measure_univ, div_one, one_smul] at huniq
  exact huniq

/-- Concrete normalization of the `SU(2)` Haar integral: `∫ 1 dμ_{SU(2)} = 1`. -/
theorem su2Haar_integral_one : ∫ _ : SU2, (1 : ℝ) ∂su2Haar = 1 :=
  haar_integral_one (μ := su2Haar)

/-- Concrete left-translation invariance of the `SU(2)` Bochner Haar integral. -/
theorem su2Haar_integral_left_inv (f : SU2 → ℝ) (g : SU2) :
    ∫ x, f (g * x) ∂su2Haar = ∫ x, f x ∂su2Haar :=
  haar_integral_left_inv (μ := su2Haar) f g

/-- Concrete right-translation invariance of the `SU(2)` Bochner Haar integral. -/
theorem su2Haar_integral_right_inv (f : SU2 → ℝ) (g : SU2) :
    ∫ x, f (x * g) ∂su2Haar = ∫ x, f x ∂su2Haar :=
  haar_integral_right_inv (μ := su2Haar) f g

/-- Concrete adjoint (gauge conjugation) invariance of the `SU(2)` Bochner Haar integral. -/
theorem su2Haar_integral_conj_inv (f : SU2 → ℝ) (g : SU2) :
    ∫ x, f (g * x * g⁻¹) ∂su2Haar = ∫ x, f x ∂su2Haar :=
  haar_integral_conj_inv (μ := su2Haar) f g

/-- Uniform bounds on the concrete single-plaquette `SU(2)` Wilson Boltzmann integral
    `∫ exp(-β (1 - a)) dμ_{SU(2)} ∈ [exp(-2β), 1]` for all `β ≥ 0`. -/
theorem su2Haar_wilson_plaquette_bounds (beta : ℝ) (hbeta : 0 ≤ beta) :
    Real.exp (-(2 * beta)) ≤ ∫ u : SU2, Real.exp (-(beta * (1 - u.a))) ∂su2Haar ∧
      ∫ u : SU2, Real.exp (-(beta * (1 - u.a))) ∂su2Haar ≤ 1 := by
  have hcont : Continuous (fun u : SU2 => Real.exp (-(beta * (1 - u.a)))) :=
    Real.continuous_exp.comp
      ((continuous_const.mul (continuous_const.sub SU2.continuous_a)).neg)
  have hint : Integrable (fun u : SU2 => Real.exp (-(beta * (1 - u.a)))) su2Haar :=
    hcont.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hnonneg : ∀ u : SU2, 0 ≤ beta * (1 - u.a) := by
    intro u
    have ha : u.a ≤ 1 := su2Trace.le_one u
    exact mul_nonneg hbeta (by linarith)
  have hle : ∀ u : SU2, beta * (1 - u.a) ≤ 2 * beta := by
    intro u
    have ha : -1 ≤ u.a := su2Trace.neg_one_le u
    nlinarith
  exact haar_boltzmann_bounds (μ := su2Haar) hnonneg hle hint

/-- Strict positivity of the concrete single-plaquette `SU(2)` Wilson partition integral. -/
theorem su2Haar_wilson_plaquette_pos (beta : ℝ) (hbeta : 0 ≤ beta) :
    0 < ∫ u : SU2, Real.exp (-(beta * (1 - u.a))) ∂su2Haar :=
  lt_of_lt_of_le (Real.exp_pos (-(2 * beta))) (su2Haar_wilson_plaquette_bounds beta hbeta).1

/-- Concrete half-space reflection positivity on `su2Haar.prod su2Haar`. -/
theorem su2Haar_reflection_positive_square (f : SU2 → ℝ) :
    0 ≤ ∫ p : SU2 × SU2, f p.1 * f p.2 ∂(su2Haar.prod su2Haar) :=
  haar_reflection_positive_square (μ := su2Haar) f

end YangMills
