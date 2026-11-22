import YangMills.OSHilbertSpace
import YangMills.SpectralGapBridge

/-!
# Module 26: TransferMatrixGap (Lean 4 + Mathlib4)
Constructs the physical transfer matrix `T̂` directly on `PhysicalOSHilbertSpace L` from
a linear symmetric time-translation semigroup `G` on the observable space `V`, and
establishes the spectral mass gap on the vacuum-orthogonal Hilbert subspace.
-/

namespace YangMills

section PhysicalTransferMatrix

variable {V : Type*} [AddCommGroup V] [Module ℝ V] (L : LinearOSBilinearSpace V)

/-- A linear symmetric time-translation semigroup `T(n)` acting on a `LinearOSBilinearSpace V`. -/
structure LinearOSTransferSemigroup extends OSTransferSemigroup (osSpace L) where
  T_add_vec : ∀ t x y, T t (x + y) = T t x + T t y
  T_smul_vec : ∀ t (c : ℝ) x, T t (c • x) = c • T t x

namespace LinearOSTransferSemigroup

variable {L} (G : LinearOSTransferSemigroup L)

/-- Uniform boundedness condition ensuring `T(1)` descends as a contraction (`H ≥ 0`). -/
def UniformlyBounded : Prop :=
  ∀ x : V, ∃ C : ℝ, 0 ≤ C ∧ ∀ n : ℕ, L.B (G.T n x) (G.T n x) ≤ C

/-- `T(1)` preserves the OS null equivalence relation `osEquiv`. -/
theorem T1_preserves_osEquiv {x y : V} (hxy : (osSpace L).osEquiv x y) :
    (osSpace L).osEquiv (G.T 1 x) (G.T 1 y) := by
  unfold OSBilinearSpace.osEquiv OSBilinearSpace.sub at *
  change L.B (G.T 1 x + -G.T 1 y) (G.T 1 x + -G.T 1 y) = 0
  have hlin : G.T 1 x + -G.T 1 y = G.T 1 (x + -y) := by
    have hneg : -G.T 1 y = (-1 : ℝ) • G.T 1 y := (neg_one_smul ℝ _).symm
    have hneg2 : -y = (-1 : ℝ) • y := (neg_one_smul ℝ _).symm
    rw [hneg, hneg2, ← G.T_smul_vec, ← G.T_add_vec]
  rw [hlin]
  exact os_transfer_preserves_null G.toOSTransferSemigroup (x + -y) hxy

/-- Well-defined map `T₀ : LinearOSQuotient L → LinearOSQuotient L` induced by `T(1)`. -/
def quotientTransferFun : LinearOSQuotient L → LinearOSQuotient L :=
  Quotient.map (G.T 1) (fun _ _ h => T1_preserves_osEquiv G h)

/-- Packaged `ℝ`-linear map `T₀ : LinearOSQuotient L →ₗ[ℝ] LinearOSQuotient L`. -/
def quotientTransferLinear : LinearOSQuotient L →ₗ[ℝ] LinearOSQuotient L where
  toFun := quotientTransferFun G
  map_add' ψ φ := by
    refine Quotient.inductionOn₂ ψ φ fun x y => ?_
    exact Quotient.sound (by
      change (osSpace L).osEquiv (G.T 1 (x + y)) (G.T 1 x + G.T 1 y)
      rw [G.T_add_vec]
      exact (osSpace L).osEquiv_refl _)
  map_smul' c ψ := by
    refine Quotient.inductionOn ψ fun x => ?_
    exact Quotient.sound (by
      change (osSpace L).osEquiv (G.T 1 (c • x)) (c • G.T 1 x)
      rw [G.T_smul_vec]
      exact (osSpace L).osEquiv_refl _)

/-- Symmetry of `quotientTransferLinear G` on the pre-Hilbert quotient `LinearOSQuotient L`. -/
theorem quotientTransferLinear_symm (ψ φ : LinearOSQuotient L) :
    inner ℝ (quotientTransferLinear G ψ) φ = inner ℝ ψ (quotientTransferLinear G φ) := by
  refine Quotient.inductionOn₂ ψ φ fun x y => ?_
  exact G.T_symm 1 x y

/-- Contraction bound `‖T₀ ψ‖ ≤ ‖ψ‖` on `LinearOSQuotient L` derived from
    `os_transfer_contraction`. -/
theorem quotientTransferLinear_contraction (hb : UniformlyBounded G) (ψ : LinearOSQuotient L) :
    ‖quotientTransferLinear G ψ‖ ≤ ‖ψ‖ := by
  have hsq : ‖quotientTransferLinear G ψ‖ ^ 2 ≤ ‖ψ‖ ^ 2 := by
    rw [osQuotient_norm_sq, osQuotient_norm_sq]
    refine Quotient.inductionOn ψ fun x => ?_
    obtain ⟨C, hC, hbound⟩ := hb x
    exact os_transfer_contraction G.toOSTransferSemigroup x C hC hbound
  nlinarith [norm_nonneg (quotientTransferLinear G ψ), norm_nonneg ψ]

/-- Continuous linear transfer operator `T₀ : LinearOSQuotient L →L[ℝ] LinearOSQuotient L`. -/
noncomputable def quotientTransferOp (hb : UniformlyBounded G) :
    LinearOSQuotient L →L[ℝ] LinearOSQuotient L :=
  (quotientTransferLinear G).mkContinuous 1 (fun ψ => by
    simpa using quotientTransferLinear_contraction G hb ψ)

/-- The canonical physical transfer matrix `T̂` on the completed Osterwalder–Schrader
    Hilbert space `PhysicalOSHilbertSpace L`. -/
noncomputable def physicalTransferOp (hb : UniformlyBounded G) :
    PhysicalOSHilbertSpace L → PhysicalOSHilbertSpace L :=
  liftOperator (quotientTransferOp G hb)

/-- `T̂` is self-adjoint (symmetric) on `PhysicalOSHilbertSpace L`. -/
theorem physicalTransfer_symmetric (hb : UniformlyBounded G)
    (ψ φ : PhysicalOSHilbertSpace L) :
    inner ℝ (physicalTransferOp G hb ψ) φ = inner ℝ ψ (physicalTransferOp G hb φ) :=
  liftOperator_symmetric (quotientTransferOp G hb) (quotientTransferLinear_symm G) ψ φ

/-- `T̂` is a contraction (`‖T̂ ψ‖ ≤ ‖ψ‖`, i.e., `H ≥ 0`) on `PhysicalOSHilbertSpace L`. -/
theorem physicalTransfer_contraction (hb : UniformlyBounded G)
    (ψ : PhysicalOSHilbertSpace L) :
    ‖physicalTransferOp G hb ψ‖ ≤ ‖ψ‖ :=
  liftOperator_contraction (quotientTransferOp G hb) (quotientTransferLinear_contraction G hb) ψ

/-- `T̂` leaves the vacuum-orthogonal subspace `Ω^⊥` invariant whenever `T̂ Ω = Ω`. -/
theorem physicalTransfer_vacuumOrthog_invariant (hb : UniformlyBounded G)
    (Ω : PhysicalOSHilbertSpace L) (hvac : physicalTransferOp G hb Ω = Ω)
    (ψ : PhysicalOSHilbertSpace L) (hψ : ψ ∈ VacuumOrthog Ω) :
    physicalTransferOp G hb ψ ∈ VacuumOrthog Ω :=
  vacuumOrthog_invariant (quotientTransferOp G hb) (quotientTransferLinear_symm G) Ω hvac ψ hψ

/-- Mass-gap norm bound on the pre-Hilbert quotient for any observable satisfying OS4
    exponential clustering `B(T^n x, T^n x) ≤ C exp(-2 m₀ n)`. -/
theorem quotientTransfer_clustering_norm_le (hb : UniformlyBounded G) (m0 : ℝ)
    (x : V) (C : ℝ) (hC : 0 ≤ C)
    (hclust : ∀ n : ℕ, L.B (G.T n x) (G.T n x) ≤ C * Real.exp (-2 * m0 * (n : ℝ))) :
    ‖quotientTransferOp G hb (osMk L x)‖ ≤ Real.exp (-m0) * ‖osMk L x‖ := by
  have hsq : ‖quotientTransferOp G hb (osMk L x)‖ ^ 2 ≤
      Real.exp (-2 * m0) * ‖osMk L x‖ ^ 2 := by
    rw [osQuotient_norm_sq, osQuotient_norm_sq]
    exact os_clustering_implies_transfer_gap G.toOSTransferSemigroup x C m0 hC hclust
  have hrhs_nonneg : 0 ≤ Real.exp (-m0) * ‖osMk L x‖ :=
    mul_nonneg (le_of_lt (Real.exp_pos _)) (norm_nonneg _)
  have hsq_rhs : (Real.exp (-m0) * ‖osMk L x‖) ^ 2 = Real.exp (-2 * m0) * ‖osMk L x‖ ^ 2 := by
    rw [mul_pow, ← Real.exp_natCast_mul]
    congr 1; congr 1; push_cast; ring
  have hle : ‖quotientTransferOp G hb (osMk L x)‖ ^ 2 ≤ (Real.exp (-m0) * ‖osMk L x‖) ^ 2 := by
    rw [hsq_rhs]
    exact hsq
  nlinarith [norm_nonneg (quotientTransferOp G hb (osMk L x)), hrhs_nonneg]

/-- Physical Hamiltonian spectral-gap exclusion on `PhysicalOSHilbertSpace L`:
    no energy `E < m₀` can lie in the spectrum of the physical Hamiltonian `H` on `Ω^⊥`. -/
theorem physical_hamiltonian_mass_gap_exclusion (hb : UniformlyBounded G)
    (Ω : PhysicalOSHilbertSpace L)
    (m0 E : ℝ) (hE_lt : E < m0)
    (hgap : ∀ ψ ∈ VacuumOrthog Ω, ‖physicalTransferOp G hb ψ‖ ≤ Real.exp (-m0) * ‖ψ‖)
    (ψ : PhysicalOSHilbertSpace L) (hψ : ψ ∈ VacuumOrthog Ω) :
    (Real.exp (-E) - Real.exp (-m0)) * ‖ψ‖ ≤
      ‖physicalTransferOp G hb ψ - Real.exp (-E) • ψ‖ :=
  (hilbert_hamiltonian_gap_exclusion (quotientTransferOp G hb) m0 E hE_lt ψ (hgap ψ hψ)).2

end LinearOSTransferSemigroup

end PhysicalTransferMatrix

end YangMills
