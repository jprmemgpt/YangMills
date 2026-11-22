import YangMills.HilbertCompletion
import YangMills.RGFlowBridge

/-!
# Module 18: SpectralGapBridge (Lean 4 + Mathlib4)
Seals the IR end of the Yang–Mills mass-gap pipeline directly on the completed physical
Hilbert space `H := UniformSpace.Completion E`:
1. Vacuum-orthogonal subspace `VacuumOrthog Ω := {ψ | ⟨Ω, ψ⟩ = 0}` and invariance under
   any symmetric transfer operator fixing the vacuum (`vacuumOrthog_invariant`).
2. Rayleigh-quotient mass-gap bound (`hilbert_rayleigh_mass_gap`):
   `|⟨ψ, T̂ ψ⟩| ≤ exp(-m₀) ‖ψ‖²`.
3. Point-spectrum exclusion (`hilbert_no_eigenvalue_in_gap`): no nonzero eigenvector can have
   eigenvalue `|λ| > exp(-m₀)`.
4. Full approximate-point / continuous spectral gap exclusion
   (`hilbert_no_approx_eigenstate_in_gap`, `hilbert_hamiltonian_gap_exclusion`):
   for every energy `E < m₀`, `(exp(-E) - exp(-m₀)) ‖ψ‖ ≤ ‖T̂ ψ - exp(-E) • ψ‖`, proving
   explicit coercivity of `T̂ - exp(-E) I` and ruling out any Weyl sequence in `(0, m₀)`.
5. End-to-end master bridge `corridor_to_hilbert_spectral_gap` linking KP corridor entry
   (`InKPCorridor`) all the way to the completed Hilbert-space spectral gap.
-/

namespace YangMills

section HilbertSpectralGap

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Vacuum-orthogonal physical subspace `Ω^⊥` inside the completed Hilbert space. -/
def VacuumOrthog (Ω : UniformSpace.Completion E) : Set (UniformSpace.Completion E) :=
  {ψ | inner ℝ Ω ψ = 0}

/-- If `T` is symmetric and `T̂ Ω = Ω`, then `T̂` leaves the vacuum-orthogonal subspace
    `Ω^⊥` invariant. -/
theorem vacuumOrthog_invariant (T : E →L[ℝ] E)
    (hsym : ∀ x y : E, inner ℝ (T x) y = inner ℝ x (T y))
    (Ω : UniformSpace.Completion E) (hvac : liftOperator T Ω = Ω)
    (ψ : UniformSpace.Completion E) (hψ : ψ ∈ VacuumOrthog Ω) :
    liftOperator T ψ ∈ VacuumOrthog Ω := by
  change inner ℝ Ω (liftOperator T ψ) = 0
  rw [← liftOperator_symmetric T hsym Ω ψ, hvac]
  exact hψ

/-- Rayleigh-quotient mass-gap bound on the completed Hilbert space:
    if `‖T̂ ψ‖ ≤ exp(-m₀) ‖ψ‖`, then `|⟨ψ, T̂ ψ⟩| ≤ exp(-m₀) ‖ψ‖²`. -/
theorem hilbert_rayleigh_mass_gap (T : E →L[ℝ] E) (m0 : ℝ)
    (ψ : UniformSpace.Completion E)
    (hgap : ‖liftOperator T ψ‖ ≤ Real.exp (-m0) * ‖ψ‖) :
    |inner ℝ ψ (liftOperator T ψ)| ≤ Real.exp (-m0) * ‖ψ‖ ^ 2 := by
  have hcs := abs_real_inner_le_norm ψ (liftOperator T ψ)
  calc
    |inner ℝ ψ (liftOperator T ψ)|
      ≤ ‖ψ‖ * ‖liftOperator T ψ‖ := hcs
    _ ≤ ‖ψ‖ * (Real.exp (-m0) * ‖ψ‖) :=
        mul_le_mul_of_nonneg_left hgap (norm_nonneg ψ)
    _ = Real.exp (-m0) * ‖ψ‖ ^ 2 := by ring

/-- Point-spectrum exclusion on the completed Hilbert space:
    if `ψ ≠ 0`, `‖T̂ ψ‖ ≤ exp(-m₀) ‖ψ‖`, and `T̂ ψ = λ • ψ`, then `|λ| ≤ exp(-m₀)`. -/
theorem hilbert_no_eigenvalue_in_gap (T : E →L[ℝ] E) (m0 lam : ℝ)
    (ψ : UniformSpace.Completion E) (hψ : ψ ≠ 0)
    (hgap : ‖liftOperator T ψ‖ ≤ Real.exp (-m0) * ‖ψ‖)
    (heig : liftOperator T ψ = lam • ψ) :
    |lam| ≤ Real.exp (-m0) := by
  have hnorm_pos : 0 < ‖ψ‖ := norm_pos_iff.mpr hψ
  rw [heig, norm_smul, Real.norm_eq_abs] at hgap
  exact le_of_mul_le_mul_right hgap hnorm_pos

/-- Full approximate-point / continuous spectral gap coercivity:
    for any `λ > exp(-m₀)` and any state `ψ` with `‖T̂ ψ‖ ≤ exp(-m₀) ‖ψ‖`,
    `(λ - exp(-m₀)) ‖ψ‖ ≤ ‖T̂ ψ - λ • ψ‖`. -/
theorem hilbert_no_approx_eigenstate_in_gap (T : E →L[ℝ] E) (m0 lam : ℝ)
    (hlam : Real.exp (-m0) < lam)
    (ψ : UniformSpace.Completion E)
    (hgap : ‖liftOperator T ψ‖ ≤ Real.exp (-m0) * ‖ψ‖) :
    (lam - Real.exp (-m0)) * ‖ψ‖ ≤ ‖liftOperator T ψ - lam • ψ‖ := by
  have hlam_pos : 0 < lam := lt_trans (Real.exp_pos (-m0)) hlam
  have htri : ‖lam • ψ‖ ≤ ‖lam • ψ - liftOperator T ψ‖ + ‖liftOperator T ψ‖ := by
    have hsplit : lam • ψ = (lam • ψ - liftOperator T ψ) + liftOperator T ψ := by abel
    calc
      ‖lam • ψ‖ = ‖(lam • ψ - liftOperator T ψ) + liftOperator T ψ‖ := by rw [← hsplit]
      _ ≤ ‖lam • ψ - liftOperator T ψ‖ + ‖liftOperator T ψ‖ := norm_add_le _ _
  have hsym_norm : ‖lam • ψ - liftOperator T ψ‖ = ‖liftOperator T ψ - lam • ψ‖ :=
    norm_sub_rev _ _
  have hsmul : ‖lam • ψ‖ = lam * ‖ψ‖ := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hlam_pos]
  rw [hsmul, hsym_norm] at htri
  linarith

/-- Energy-variable Hamiltonian spectral gap exclusion on the completed Hilbert space:
    for every energy `E_val < m₀` (in particular every `E_val ∈ (0, m₀)`), the transfer
    resolvent defect `‖T̂ ψ - exp(-E_val) • ψ‖` is uniformly bounded below by
    `(exp(-E_val) - exp(-m₀)) ‖ψ‖` with strictly positive gap margin. -/
theorem hilbert_hamiltonian_gap_exclusion (T : E →L[ℝ] E) (m0 E_val : ℝ)
    (hE : E_val < m0)
    (ψ : UniformSpace.Completion E)
    (hgap : ‖liftOperator T ψ‖ ≤ Real.exp (-m0) * ‖ψ‖) :
    0 < Real.exp (-E_val) - Real.exp (-m0) ∧
      (Real.exp (-E_val) - Real.exp (-m0)) * ‖ψ‖ ≤
        ‖liftOperator T ψ - Real.exp (-E_val) • ψ‖ := by
  have hlt : Real.exp (-m0) < Real.exp (-E_val) :=
    Real.exp_lt_exp.mpr (by linarith)
  exact ⟨sub_pos.mpr hlt, hilbert_no_approx_eigenstate_in_gap T m0 (Real.exp (-E_val)) hlt ψ hgap⟩

/-- End-to-end KP corridor to completed Hilbert-space spectral gap theorem:
    from any certified KP corridor entry (`κ₀ ≥ 6.1516`, `0 ≤ ε_bridge ≤ 1/567`) and
    bounded transfer operator `T : E →L[ℝ] E` with squared-norm mass-gap contraction
    at rate `m0 := corridorMassFloor κ₀ b0 gStarSq LambdaRG`, the completed Hilbert space
    `UniformSpace.Completion E` and lifted operator `T̂ := liftOperator T` satisfy:
    1. Strictly positive mass floor `0 < m0` beating `R_stop⁻¹` and winning the renewal race.
    2. Iterated Hilbert-space norm decay `‖T̂^n ψ‖ ≤ exp(-m₀ n) ‖ψ‖` for all `n : ℕ`.
    3. Rayleigh-quotient bound `|⟨ψ, T̂ ψ⟩| ≤ exp(-m₀) ‖ψ‖²`.
    4. Full continuous + point spectral gap exclusion for every energy `E_val < m₀`. -/
theorem corridor_to_hilbert_spectral_gap
    (T : E →L[ℝ] E)
    (κ₀ epsBridge b0 gStarSq LambdaRG : ℝ)
    (hcorr : InKPCorridor κ₀ epsBridge)
    (hb0 : 0 < b0) (hgStar : 0 < gStarSq) (hLambda : 0 < LambdaRG)
    (hsq : ∀ x : E, ‖T x‖ ^ 2 ≤
      Real.exp (-2 * corridorMassFloor κ₀ b0 gStarSq LambdaRG) * ‖x‖ ^ 2) :
    let m0 := corridorMassFloor κ₀ b0 gStarSq LambdaRG
    let RstopInv := LambdaRG * Real.exp (1 / (2 * b0 * gStarSq))
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
  intro m0 RstopInv
  have hfloor := mass_gap_floor_from_five_tolls κ₀ b0 gStarSq LambdaRG
    hcorr.1 hb0 hgStar hLambda
  have hTnorm : ∀ x : E, ‖T x‖ ≤ Real.exp (-m0) * ‖x‖ :=
    os_norm_sq_gap_to_norm_gap T m0 hsq
  have hgap : ∀ ψ : UniformSpace.Completion E, ‖liftOperator T ψ‖ ≤ Real.exp (-m0) * ‖ψ‖ :=
    liftOperator_norm_le T (Real.exp (-m0)) hTnorm
  refine ⟨hfloor.1, hfloor.2.1, hfloor.2.2, ?_, ?_, ?_⟩
  · intro n ψ
    exact hilbert_transfer_mass_gap_decay T m0 hsq n ψ
  · intro ψ
    exact hilbert_rayleigh_mass_gap T m0 ψ (hgap ψ)
  · intro E_val hE ψ
    exact (hilbert_hamiltonian_gap_exclusion T m0 E_val hE ψ (hgap ψ)).2

end HilbertSpectralGap

end YangMills
