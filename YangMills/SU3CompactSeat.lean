import Mathlib.MeasureTheory.Measure.Haar.Unique
import YangMills.SU3Seat
import YangMills.HaarMeasureSeat

/-!
# Module 21: SU3CompactSeat (Lean 4 + Mathlib4)
Equips our concrete non-Abelian gauge group `SU3` (`3×3` complex special unitary matrices
from `SU3Seat.lean`) with its compact Hausdorff topological group structure, Borel
measurable space, and Mathlib's actual normalized bi-invariant Haar probability measure
`su3Haar`:
1. Topological embedding `SU3.mat : SU3 ↪ Mat3C`, yielding `T2Space SU3`,
   `SecondCountableTopology SU3`, and `CompactSpace SU3` (closed unitary + `det = 1`
   locus inside the compact unit square box `[-1, 1]² ⊂ ℂ` per entry).
2. Continuity of `3×3` complex matrix multiplication and Hermitian conjugation
   (`IsTopologicalGroup SU3`), Borel `MeasurableSpace SU3`, and `BorelSpace SU3`.
3. Concrete normalized bi-invariant Haar probability measure `su3Haar : Measure SU3`
   via `Measure.haarMeasure`, with `IsProbabilityMeasure su3Haar`, `IsMulLeftInvariant`,
   and `IsMulRightInvariant`.
4. Concrete `SU3` Bochner Haar invariance (`su3Haar_integral_conj_inv`), uniform bounds
   and strict positivity of the single-plaquette `SU3` Wilson Boltzmann integral
   (`su3Haar_wilson_plaquette_bounds`, `su3Haar_wilson_plaquette_pos`), and concrete
   `SU3 × SU3` half-space reflection positivity (`su3Haar_reflection_positive_square`).
-/

noncomputable section

namespace YangMills

open MeasureTheory Topology

/-! ## 1. Continuity of Concrete 3×3 Complex Matrix Operations -/

theorem continuous_cconj : Continuous cconj := by
  have heq : cconj = fun z : ℂ => (z.re : ℂ) - (z.im : ℂ) * Complex.I := by
    funext z
    apply Complex.ext <;> simp [cconj]
  rw [heq]
  exact (Complex.continuous_ofReal.comp Complex.continuous_re).sub
    ((Complex.continuous_ofReal.comp Complex.continuous_im).mul continuous_const)

theorem continuous_matDag : Continuous matDag := by
  refine continuous_pi fun i => continuous_pi fun j => ?_
  exact continuous_cconj.comp ((continuous_apply i).comp (continuous_apply j))

theorem continuous_matMul : Continuous (fun p : Mat3C × Mat3C => matMul p.1 p.2) := by
  refine continuous_pi fun i => continuous_pi fun j => ?_
  have hA : ∀ k : Fin 3, Continuous (fun p : Mat3C × Mat3C => p.1 i k) :=
    fun k => (continuous_apply k).comp ((continuous_apply i).comp continuous_fst)
  have hB : ∀ k : Fin 3, Continuous (fun p : Mat3C × Mat3C => p.2 k j) :=
    fun k => (continuous_apply j).comp ((continuous_apply k).comp continuous_snd)
  exact (((hA 0).mul (hB 0)).add ((hA 1).mul (hB 1))).add ((hA 2).mul (hB 2))

theorem continuous_det3 : Continuous det3 := by
  have h : ∀ i j : Fin 3, Continuous (fun A : Mat3C => A i j) :=
    fun i j => (continuous_apply j).comp (continuous_apply i)
  unfold det3
  exact (((h 0 0).mul (((h 1 1).mul (h 2 2)).sub ((h 1 2).mul (h 2 1)))).sub
    ((h 0 1).mul (((h 1 0).mul (h 2 2)).sub ((h 1 2).mul (h 2 0))))).add
    ((h 0 2).mul (((h 1 0).mul (h 2 1)).sub ((h 1 1).mul (h 2 0))))

/-! ## 2. Compact Hausdorff Topological Group Structure on SU(3) -/

namespace SU3

theorem mat_injective : Function.Injective SU3.mat :=
  fun _ _ h => SU3.ext h

instance : Nonempty SU3 := ⟨1⟩

instance : TopologicalSpace SU3 :=
  TopologicalSpace.induced SU3.mat inferInstance

theorem isInducing_mat : IsInducing SU3.mat := ⟨rfl⟩

theorem isEmbedding_mat : IsEmbedding SU3.mat :=
  ⟨isInducing_mat, mat_injective⟩

theorem continuous_mat : Continuous SU3.mat :=
  isInducing_mat.continuous

theorem continuous_entry (i j : Fin 3) : Continuous (fun U : SU3 => U.mat i j) :=
  (continuous_apply j).comp ((continuous_apply i).comp continuous_mat)

instance : T2Space SU3 :=
  isEmbedding_mat.t2Space

instance : SecondCountableTopology SU3 :=
  isInducing_mat.secondCountableTopology

/-- Compact closed unit square `[-1, 1] + i [-1, 1] ⊂ ℂ`. -/
def unitSqC : Set ℂ :=
  (fun p : ℝ × ℝ => (p.1 : ℂ) + (p.2 : ℂ) * Complex.I) ''
    (Set.Icc (-1 : ℝ) 1 ×ˢ Set.Icc (-1 : ℝ) 1)

theorem isCompact_unitSqC : IsCompact unitSqC := by
  have hcont : Continuous (fun p : ℝ × ℝ => (p.1 : ℂ) + (p.2 : ℂ) * Complex.I) :=
    (Complex.continuous_ofReal.comp continuous_fst).add
      ((Complex.continuous_ofReal.comp continuous_snd).mul continuous_const)
  exact (isCompact_Icc.prod isCompact_Icc).image hcont

theorem mem_unitSqC_of_sq_le_one {z : ℂ} (h : z.re ^ 2 + z.im ^ 2 ≤ 1) : z ∈ unitSqC := by
  have hre_sq : z.re ^ 2 ≤ 1 := by linarith [sq_nonneg z.im]
  have him_sq : z.im ^ 2 ≤ 1 := by linarith [sq_nonneg z.re]
  refine ⟨(z.re, z.im), ⟨⟨by nlinarith, by nlinarith⟩, ⟨by nlinarith, by nlinarith⟩⟩, ?_⟩
  apply Complex.ext <;> simp

theorem unitary_entry_sq_le_one {A : Mat3C} (hU : matMul (matDag A) A = matOne)
    (i j : Fin 3) : (A i j).re ^ 2 + (A i j).im ^ 2 ≤ 1 := by
  have hcol : (matMul (matDag A) A j j).re = 1 := by
    have h := congrArg Complex.re (congrFun (congrFun hU j) j)
    simpa [matOne] using h
  have hsum :
      (A 0 j).re ^ 2 + (A 0 j).im ^ 2 +
      (A 1 j).re ^ 2 + (A 1 j).im ^ 2 +
      (A 2 j).re ^ 2 + (A 2 j).im ^ 2 = 1 := by
    have hre :
        (matMul (matDag A) A j j).re =
        (A 0 j).re ^ 2 + (A 0 j).im ^ 2 +
        (A 1 j).re ^ 2 + (A 1 j).im ^ 2 +
        (A 2 j).re ^ 2 + (A 2 j).im ^ 2 := by
      simp only [matMul, matDag, cconj, Complex.add_re, Complex.mul_re]
      ring
    linarith
  have h0r := sq_nonneg (A 0 j).re
  have h0i := sq_nonneg (A 0 j).im
  have h1r := sq_nonneg (A 1 j).re
  have h1i := sq_nonneg (A 1 j).im
  have h2r := sq_nonneg (A 2 j).re
  have h2i := sq_nonneg (A 2 j).im
  match i with
  | ⟨0, _⟩ => change (A 0 j).re ^ 2 + (A 0 j).im ^ 2 ≤ 1; linarith
  | ⟨1, _⟩ => change (A 1 j).re ^ 2 + (A 1 j).im ^ 2 ≤ 1; linarith
  | ⟨2, _⟩ => change (A 2 j).re ^ 2 + (A 2 j).im ^ 2 ≤ 1; linarith

theorem range_mat_eq :
    Set.range SU3.mat =
      {A : Mat3C | matMul (matDag A) A = matOne ∧
        matMul A (matDag A) = matOne ∧ det3 A = 1} := by
  ext A
  simp only [Set.mem_range, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨U, rfl⟩
    exact ⟨U.unitary_left, U.unitary_right, U.det_eq_one⟩
  · rintro ⟨hl, hr, hd⟩
    exact ⟨⟨A, hl, hr, hd⟩, rfl⟩

private def unitBox3C : Set Mat3C :=
  Set.univ.pi fun _ : Fin 3 => Set.univ.pi fun _ : Fin 3 => unitSqC

private theorem isCompact_unitBox3C : IsCompact unitBox3C :=
  isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => isCompact_unitSqC

private theorem isClosed_unitary_left :
    IsClosed {A : Mat3C | matMul (matDag A) A = matOne} :=
  isClosed_eq (f := fun A : Mat3C => matMul (matDag A) A)
    (g := fun _ : Mat3C => matOne)
    (continuous_matMul.comp (continuous_matDag.prodMk continuous_id))
    continuous_const

private theorem isClosed_unitary_right :
    IsClosed {A : Mat3C | matMul A (matDag A) = matOne} :=
  isClosed_eq (f := fun A : Mat3C => matMul A (matDag A))
    (g := fun _ : Mat3C => matOne)
    (continuous_matMul.comp (continuous_id.prodMk continuous_matDag))
    continuous_const

private theorem isClosed_det3_one :
    IsClosed {A : Mat3C | det3 A = 1} :=
  isClosed_eq (f := det3) (g := fun _ : Mat3C => (1 : ℂ))
    continuous_det3 continuous_const

theorem isCompact_range_mat : IsCompact (Set.range SU3.mat) := by
  rw [range_mat_eq]
  have hset :
      {A : Mat3C | matMul (matDag A) A = matOne ∧
        matMul A (matDag A) = matOne ∧ det3 A = 1} =
      {A : Mat3C | matMul (matDag A) A = matOne} ∩
        ({A : Mat3C | matMul A (matDag A) = matOne} ∩
          {A : Mat3C | det3 A = 1}) := by
    ext A
    simp only [Set.mem_inter_iff, Set.mem_ofPred_eq]
  rw [hset]
  have hclosed : IsClosed
      ({A : Mat3C | matMul (matDag A) A = matOne} ∩
        ({A : Mat3C | matMul A (matDag A) = matOne} ∩
          {A : Mat3C | det3 A = 1})) :=
    isClosed_unitary_left.inter (isClosed_unitary_right.inter isClosed_det3_one)
  have hsub :
      ({A : Mat3C | matMul (matDag A) A = matOne} ∩
        ({A : Mat3C | matMul A (matDag A) = matOne} ∩
          {A : Mat3C | det3 A = 1})) ⊆ unitBox3C := by
    intro A hA
    simp only [Set.mem_inter_iff, Set.mem_ofPred_eq] at hA
    rw [unitBox3C, Set.mem_univ_pi]
    intro i
    rw [Set.mem_univ_pi]
    intro j
    exact mem_unitSqC_of_sq_le_one (unitary_entry_sq_le_one hA.1 i j)
  exact isCompact_unitBox3C.of_isClosed_subset hclosed hsub

instance : CompactSpace SU3 := by
  refine ⟨?_⟩
  rw [isInducing_mat.isCompact_iff, Set.image_univ]
  exact isCompact_range_mat

instance : ContinuousMul SU3 where
  continuous_mul := by
    rw [isInducing_mat.continuous_iff]
    exact continuous_matMul.comp
      ((continuous_mat.comp continuous_fst).prodMk (continuous_mat.comp continuous_snd))

instance : ContinuousInv SU3 where
  continuous_inv := by
    rw [isInducing_mat.continuous_iff]
    exact continuous_matDag.comp continuous_mat

instance : IsTopologicalGroup SU3 where

instance : MeasurableSpace SU3 := borel SU3

instance : BorelSpace SU3 := ⟨rfl⟩

/-- The whole compact group `SU(3)` as a `PositiveCompacts SU3` normalization set. -/
def univCompact : TopologicalSpace.PositiveCompacts SU3 where
  carrier := Set.univ
  isCompact' := isCompact_univ
  interior_nonempty' := by simp

theorem continuous_reTrNorm : Continuous su3Trace.reTrNorm := by
  have h0 : Continuous (fun U : SU3 => (U.mat 0 0).re) :=
    Complex.continuous_re.comp (continuous_entry 0 0)
  have h1 : Continuous (fun U : SU3 => (U.mat 1 1).re) :=
    Complex.continuous_re.comp (continuous_entry 1 1)
  have h2 : Continuous (fun U : SU3 => (U.mat 2 2).re) :=
    Complex.continuous_re.comp (continuous_entry 2 2)
  have heq : su3Trace.reTrNorm =
      fun U : SU3 => ((U.mat 0 0).re + (U.mat 1 1).re + (U.mat 2 2).re) / 3 := by
    funext U
    simp [su3Trace, tr3]
  rw [heq]
  exact ((h0.add h1).add h2).div_const 3

end SU3

/-! ## 3. Concrete Normalized Bi-Invariant Haar Measure on SU(3) -/

/-- Mathlib's concrete normalized bi-invariant Haar probability measure on `SU(3)`. -/
def su3Haar : Measure SU3 :=
  Measure.haarMeasure SU3.univCompact

instance : su3Haar.IsHaarMeasure :=
  Measure.isHaarMeasure_haarMeasure SU3.univCompact

instance : IsProbabilityMeasure su3Haar := by
  refine ⟨?_⟩
  have h := Measure.haarMeasure_self (K₀ := SU3.univCompact)
  simpa [su3Haar, SU3.univCompact] using h

/-- Unimodularity of compact `SU(3)`: normalized left Haar measure is right-invariant. -/
instance : su3Haar.IsMulRightInvariant := by
  refine ⟨fun g => ?_⟩
  set ν : Measure SU3 := Measure.map (fun x => x * g) su3Haar
  have hmeas_r : Measurable (fun x : SU3 => x * g) := measurable_mul_const g
  have : IsProbabilityMeasure ν :=
    ⟨by rw [Measure.map_apply hmeas_r MeasurableSet.univ]; simp⟩
  have : ν.IsMulLeftInvariant := by
    refine ⟨fun h => ?_⟩
    have hmeas_l : Measurable (fun x : SU3 => h * x) := measurable_const_mul h
    change Measure.map (fun x => h * x) (Measure.map (fun x => x * g) su3Haar) =
      Measure.map (fun x => x * g) su3Haar
    rw [Measure.map_map hmeas_l hmeas_r]
    have hcomm : (fun x : SU3 => h * x) ∘ (fun x : SU3 => x * g) =
        (fun x : SU3 => x * g) ∘ (fun x : SU3 => h * x) := by
      funext x; simp [mul_assoc]
    rw [hcomm, ← Measure.map_map hmeas_r hmeas_l,
        Measure.IsMulLeftInvariant.map_mul_left_eq_self (μ := su3Haar) h]
  have huniq := MeasureTheory.measure_eq_div_smul (s := Set.univ) ν su3Haar
    (by simp) (by simp)
  simp only [measure_univ, div_one, one_smul] at huniq
  exact huniq

/-- Concrete normalization of the `SU(3)` Haar integral: `∫ 1 dμ_{SU(3)} = 1`. -/
theorem su3Haar_integral_one : ∫ _ : SU3, (1 : ℝ) ∂su3Haar = 1 :=
  haar_integral_one (μ := su3Haar)

/-- Concrete left-translation invariance of the `SU(3)` Bochner Haar integral. -/
theorem su3Haar_integral_left_inv (f : SU3 → ℝ) (g : SU3) :
    ∫ x, f (g * x) ∂su3Haar = ∫ x, f x ∂su3Haar :=
  haar_integral_left_inv (μ := su3Haar) f g

/-- Concrete right-translation invariance of the `SU(3)` Bochner Haar integral. -/
theorem su3Haar_integral_right_inv (f : SU3 → ℝ) (g : SU3) :
    ∫ x, f (x * g) ∂su3Haar = ∫ x, f x ∂su3Haar :=
  haar_integral_right_inv (μ := su3Haar) f g

/-- Concrete adjoint (gauge conjugation) invariance of the `SU(3)` Bochner Haar integral. -/
theorem su3Haar_integral_conj_inv (f : SU3 → ℝ) (g : SU3) :
    ∫ x, f (g * x * g⁻¹) ∂su3Haar = ∫ x, f x ∂su3Haar :=
  haar_integral_conj_inv (μ := su3Haar) f g

/-- Uniform bounds on the concrete single-plaquette `SU(3)` Wilson Boltzmann integral
    `∫ exp(-β (1 - (1/3) Re Tr U)) dμ_{SU(3)} ∈ [exp(-2β), 1]` for all `β ≥ 0`. -/
theorem su3Haar_wilson_plaquette_bounds (beta : ℝ) (hbeta : 0 ≤ beta) :
    Real.exp (-(2 * beta)) ≤
      ∫ u : SU3, Real.exp (-(beta * (1 - su3Trace.reTrNorm u))) ∂su3Haar ∧
    ∫ u : SU3, Real.exp (-(beta * (1 - su3Trace.reTrNorm u))) ∂su3Haar ≤ 1 := by
  have hcont : Continuous (fun u : SU3 => Real.exp (-(beta * (1 - su3Trace.reTrNorm u)))) :=
    Real.continuous_exp.comp
      ((continuous_const.mul (continuous_const.sub SU3.continuous_reTrNorm)).neg)
  have hint : Integrable (fun u : SU3 => Real.exp (-(beta * (1 - su3Trace.reTrNorm u)))) su3Haar :=
    hcont.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hnonneg : ∀ u : SU3, 0 ≤ beta * (1 - su3Trace.reTrNorm u) := by
    intro u
    have hu : su3Trace.reTrNorm u ≤ 1 := su3Trace.le_one u
    exact mul_nonneg hbeta (by linarith)
  have hle : ∀ u : SU3, beta * (1 - su3Trace.reTrNorm u) ≤ 2 * beta := by
    intro u
    have hu : -1 ≤ su3Trace.reTrNorm u := su3Trace.neg_one_le u
    nlinarith
  exact haar_boltzmann_bounds (μ := su3Haar) hnonneg hle hint

/-- Strict positivity of the concrete single-plaquette `SU(3)` Wilson partition integral. -/
theorem su3Haar_wilson_plaquette_pos (beta : ℝ) (hbeta : 0 ≤ beta) :
    0 < ∫ u : SU3, Real.exp (-(beta * (1 - su3Trace.reTrNorm u))) ∂su3Haar :=
  lt_of_lt_of_le (Real.exp_pos (-(2 * beta))) (su3Haar_wilson_plaquette_bounds beta hbeta).1

/-- Concrete half-space reflection positivity on `su3Haar.prod su3Haar`. -/
theorem su3Haar_reflection_positive_square (f : SU3 → ℝ) :
    0 ≤ ∫ p : SU3 × SU3, f p.1 * f p.2 ∂(su3Haar.prod su3Haar) :=
  haar_reflection_positive_square (μ := su3Haar) f

end YangMills
