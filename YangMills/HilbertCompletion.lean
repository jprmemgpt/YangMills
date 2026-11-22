import Mathlib.Analysis.InnerProductSpace.Completion
import YangMills.OSReconstruction

/-!
# Module 16: HilbertCompletion (Lean 4 + Mathlib4)
Completes the Osterwalder–Schrader pre-Hilbert quotient space into a genuine complete
real Hilbert space via Mathlib's `UniformSpace.Completion`, and lifts the physical
transfer operator `T` with exact preservation of linearity, symmetry, contraction,
uniqueness, and the exponential mass-gap decay rate:
1. Completeness (`hilbertCompletion_complete`) and inner-product structure
   (`hilbertCompletion_inner_product`) of `UniformSpace.Completion E`, with isometric
   embedding (`hilbertCompletion_embed_isometry`, `hilbertCompletion_embed_inner`).
2. Canonical continuous extension `liftOperator T := UniformSpace.Completion.map T` of any
   bounded linear operator `T : E →L[ℝ] E`, preserving addition, scalar multiplication,
   symmetry (`liftOperator_symmetric`), operator-norm bounds (`liftOperator_norm_le`),
   and uniqueness on the dense pre-Hilbert subspace (`liftOperator_unique`).
3. Contraction lift (`liftOperator_contraction`), iterated decay (`liftOperator_iter_norm_le`),
   squared-norm to norm gap bridge (`os_norm_sq_gap_to_norm_gap`), and physical Hilbert-space
   exponential mass-gap decay `‖T̂^n ψ‖ ≤ exp(-m₀ n) ‖ψ‖` (`hilbert_transfer_mass_gap_decay`).
-/

namespace YangMills

section HilbertSpaceCompletion

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- `UniformSpace.Completion E` is a complete metric/uniform space (Hilbert space). -/
theorem hilbertCompletion_complete : CompleteSpace (UniformSpace.Completion E) :=
  inferInstance

/-- `UniformSpace.Completion E` carries a canonical real inner product space structure. -/
noncomputable def hilbertCompletion_inner_product :
    InnerProductSpace ℝ (UniformSpace.Completion E) :=
  inferInstance

/-- The embedding of the OS pre-Hilbert quotient `E` into its Hilbert completion is isometric. -/
theorem hilbertCompletion_embed_isometry (x : E) :
    ‖(x : UniformSpace.Completion E)‖ = ‖x‖ :=
  UniformSpace.Completion.norm_coe x

/-- The embedding of `E` into `UniformSpace.Completion E` preserves the OS inner product. -/
theorem hilbertCompletion_embed_inner (x y : E) :
    inner ℝ (x : UniformSpace.Completion E) (y : UniformSpace.Completion E) = inner ℝ x y :=
  UniformSpace.Completion.inner_coe x y

/-- Canonical continuous extension of a bounded linear operator `T : E →L[ℝ] E`
    to the completed physical Hilbert space `UniformSpace.Completion E`. -/
noncomputable def liftOperator (T : E →L[ℝ] E) :
    UniformSpace.Completion E → UniformSpace.Completion E :=
  UniformSpace.Completion.map T

/-- `liftOperator T` agrees with `T` on the dense pre-Hilbert subspace `E`. -/
theorem liftOperator_coe (T : E →L[ℝ] E) (x : E) :
    liftOperator T (x : UniformSpace.Completion E) = (T x : UniformSpace.Completion E) :=
  UniformSpace.Completion.map_coe T.uniformContinuous x

/-- `liftOperator T` is continuous on the completed Hilbert space. -/
theorem liftOperator_continuous (T : E →L[ℝ] E) :
    Continuous (liftOperator T) :=
  UniformSpace.Completion.continuous_map

/-- Uniqueness of the continuous Hilbert-space extension of `T`. -/
theorem liftOperator_unique (T : E →L[ℝ] E)
    (S : UniformSpace.Completion E → UniformSpace.Completion E)
    (hS : Continuous S)
    (hagree : ∀ x : E, S (x : UniformSpace.Completion E) = (T x : UniformSpace.Completion E)) :
    ∀ ψ : UniformSpace.Completion E, S ψ = liftOperator T ψ := by
  intro ψ
  refine UniformSpace.Completion.induction_on ψ
    (isClosed_eq hS (liftOperator_continuous T)) ?_
  intro x
  rw [hagree x, liftOperator_coe]

/-- Additivity of `liftOperator T` on the completed Hilbert space. -/
theorem liftOperator_add (T : E →L[ℝ] E) (ψ φ : UniformSpace.Completion E) :
    liftOperator T (ψ + φ) = liftOperator T ψ + liftOperator T φ := by
  refine UniformSpace.Completion.induction_on₂ ψ φ
    (isClosed_eq
      ((liftOperator_continuous T).comp continuous_add)
      (((liftOperator_continuous T).comp continuous_fst).add
        ((liftOperator_continuous T).comp continuous_snd))) ?_
  intro x y
  rw [← UniformSpace.Completion.coe_add, liftOperator_coe, liftOperator_coe, liftOperator_coe,
    map_add, UniformSpace.Completion.coe_add]

/-- Real homogeneity of `liftOperator T` on the completed Hilbert space. -/
theorem liftOperator_smul (T : E →L[ℝ] E) (r : ℝ) (ψ : UniformSpace.Completion E) :
    liftOperator T (r • ψ) = r • liftOperator T ψ := by
  refine UniformSpace.Completion.induction_on ψ
    (isClosed_eq
      ((liftOperator_continuous T).comp (continuous_const_smul r))
      ((continuous_const_smul r).comp (liftOperator_continuous T))) ?_
  intro x
  rw [← UniformSpace.Completion.coe_smul, liftOperator_coe, liftOperator_coe,
    map_smul, UniformSpace.Completion.coe_smul]

/-- Symmetry preservation: if `T` is symmetric on the OS pre-Hilbert quotient `E`, then its
    extension `liftOperator T` is symmetric on the completed Hilbert space. -/
theorem liftOperator_symmetric (T : E →L[ℝ] E)
    (hsym : ∀ x y : E, inner ℝ (T x) y = inner ℝ x (T y))
    (ψ φ : UniformSpace.Completion E) :
    inner ℝ (liftOperator T ψ) φ = inner ℝ ψ (liftOperator T φ) := by
  refine UniformSpace.Completion.induction_on₂ ψ φ
    (isClosed_eq
      (((liftOperator_continuous T).comp continuous_fst).inner continuous_snd)
      (continuous_fst.inner ((liftOperator_continuous T).comp continuous_snd))) ?_
  intro x y
  rw [liftOperator_coe, liftOperator_coe,
    UniformSpace.Completion.inner_coe, UniformSpace.Completion.inner_coe]
  exact hsym x y

/-- Operator-norm bound extension: if `‖T x‖ ≤ c ‖x‖` on the pre-Hilbert space `E`,
    then `‖T̂ ψ‖ ≤ c ‖ψ‖` for every `ψ` in the completed Hilbert space. -/
theorem liftOperator_norm_le (T : E →L[ℝ] E) (c : ℝ)
    (hT : ∀ x : E, ‖T x‖ ≤ c * ‖x‖) (ψ : UniformSpace.Completion E) :
    ‖liftOperator T ψ‖ ≤ c * ‖ψ‖ := by
  refine UniformSpace.Completion.induction_on ψ
    (isClosed_le
      (continuous_norm.comp (liftOperator_continuous T))
      (continuous_const.mul continuous_norm)) ?_
  intro x
  rw [liftOperator_coe, UniformSpace.Completion.norm_coe, UniformSpace.Completion.norm_coe]
  exact hT x

/-- Contraction lift (`H ≥ 0` on the completed Hilbert space):
    if `‖T x‖ ≤ ‖x‖` on `E`, then `‖T̂ ψ‖ ≤ ‖ψ‖` on `UniformSpace.Completion E`. -/
theorem liftOperator_contraction (T : E →L[ℝ] E)
    (hT : ∀ x : E, ‖T x‖ ≤ ‖x‖) (ψ : UniformSpace.Completion E) :
    ‖liftOperator T ψ‖ ≤ ‖ψ‖ := by
  have h := liftOperator_norm_le T 1 (fun x => by simpa using hT x) ψ
  simpa using h

/-- Iterated operator-norm decay on the completed Hilbert space:
    `‖T̂^n ψ‖ ≤ c^n ‖ψ‖` for all `n : ℕ`. -/
theorem liftOperator_iter_norm_le (T : E →L[ℝ] E) (c : ℝ) (hc : 0 ≤ c)
    (hT : ∀ x : E, ‖T x‖ ≤ c * ‖x‖) (n : ℕ) (ψ : UniformSpace.Completion E) :
    ‖(liftOperator T)^[n] ψ‖ ≤ c ^ n * ‖ψ‖ := by
  induction n with
  | zero =>
    simp
  | succ n ih =>
    rw [Function.iterate_succ_apply']
    calc
      ‖liftOperator T ((liftOperator T)^[n] ψ)‖
        ≤ c * ‖(liftOperator T)^[n] ψ‖ := liftOperator_norm_le T c hT _
      _ ≤ c * (c ^ n * ‖ψ‖) := mul_le_mul_of_nonneg_left ih hc
      _ = c ^ (n + 1) * ‖ψ‖ := by rw [pow_succ']; ring

/-- Bridge from the OS squared-norm mass-gap inequality (`OSReconstruction.os_clustering_implies_transfer_gap`)
    to the operator-norm mass-gap bound `‖T x‖ ≤ exp(-m₀) ‖x‖`. -/
theorem os_norm_sq_gap_to_norm_gap (T : E →L[ℝ] E) (m0 : ℝ)
    (hsq : ∀ x : E, ‖T x‖ ^ 2 ≤ Real.exp (-2 * m0) * ‖x‖ ^ 2) (x : E) :
    ‖T x‖ ≤ Real.exp (-m0) * ‖x‖ := by
  have hrhs_nonneg : 0 ≤ Real.exp (-m0) * ‖x‖ :=
    mul_nonneg (le_of_lt (Real.exp_pos _)) (norm_nonneg x)
  have hsq_rhs : (Real.exp (-m0) * ‖x‖) ^ 2 = Real.exp (-2 * m0) * ‖x‖ ^ 2 := by
    rw [mul_pow, ← Real.exp_natCast_mul]
    congr 1
    congr 1
    push_cast
    ring
  have hle : ‖T x‖ ^ 2 ≤ (Real.exp (-m0) * ‖x‖) ^ 2 := by
    rw [hsq_rhs]
    exact hsq x
  nlinarith [norm_nonneg (T x), hrhs_nonneg]

/-- Physical Hilbert-space exponential mass-gap decay:
    if the OS transfer operator satisfies `‖T x‖² ≤ exp(-2 m₀) ‖x‖²` on the pre-Hilbert
    quotient `E`, then its unique Hilbert-space extension `T̂` satisfies
    `‖T̂^n ψ‖ ≤ exp(-m₀ n) ‖ψ‖` for every state `ψ ∈ UniformSpace.Completion E` and `n : ℕ`. -/
theorem hilbert_transfer_mass_gap_decay (T : E →L[ℝ] E) (m0 : ℝ)
    (hsq : ∀ x : E, ‖T x‖ ^ 2 ≤ Real.exp (-2 * m0) * ‖x‖ ^ 2)
    (n : ℕ) (ψ : UniformSpace.Completion E) :
    ‖(liftOperator T)^[n] ψ‖ ≤ Real.exp (-m0 * (n : ℝ)) * ‖ψ‖ := by
  have hT : ∀ x : E, ‖T x‖ ≤ Real.exp (-m0) * ‖x‖ :=
    os_norm_sq_gap_to_norm_gap T m0 hsq
  have hiter := liftOperator_iter_norm_le T (Real.exp (-m0)) (le_of_lt (Real.exp_pos _)) hT n ψ
  have hexp : Real.exp (-m0) ^ n = Real.exp (-m0 * (n : ℝ)) := by
    rw [← Real.exp_natCast_mul]
    congr 1
    ring
  rw [hexp] at hiter
  exact hiter

end HilbertSpaceCompletion

end YangMills
