import YangMills.TransferMatrixGap
import YangMills.MultiScaleRGStep

/-!
# Module 27: ContinuumOS (Lean 4 + Mathlib4)
Formalizes the infinite-volume / continuum weak-limit passage (`n → ∞`, i.e., `a → 0, L → ∞`)
of finite-volume Osterwalder–Schrader bilinear forms `B_n` to a continuum limit `B_∞`:
1. Pointwise limit closure of symmetry, bilinearity, and OS2 reflection positivity,
   packaging `B_∞` directly into `continuumOSBilinearSpace : LinearOSBilinearSpace V`.
2. Preservation of Euclidean / gauge invariance (`continuum_os1_invariance`).
3. Preservation of uniform OS4 exponential clustering (`continuum_os4_clustering`) with
   a uniform `n`-independent mass floor `m₀ > 0`.
4. Continuum transfer semigroup (`continuumTransferSemigroup`) and physical continuum
   Hilbert-space mass-gap contraction (`continuum_transfer_mass_gap`).
-/

namespace YangMills

section ContinuumLimit

variable {V : Type*} [AddCommGroup V] [Module ℝ V]

/-- OS2 reflection positivity is closed under pointwise limits: if `0 ≤ B_n(x, x)` for all `n`
    and `B_n(x, x) → B_∞(x, x)`, then `0 ≤ B_∞(x, x)`. -/
theorem continuum_os2_reflection_positivity
    (Lseq : ℕ → LinearOSBilinearSpace V) (Binf : V → V → ℝ)
    (htend : ∀ x y, Filter.Tendsto (fun n => (Lseq n).B x y) Filter.atTop (nhds (Binf x y)))
    (x : V) :
    0 ≤ Binf x x :=
  ge_of_tendsto' (htend x x) (fun n => (Lseq n).pos_semidef x)

/-- Symmetry is preserved in the continuum weak limit. -/
theorem continuum_os_symm
    (Lseq : ℕ → LinearOSBilinearSpace V) (Binf : V → V → ℝ)
    (htend : ∀ x y, Filter.Tendsto (fun n => (Lseq n).B x y) Filter.atTop (nhds (Binf x y)))
    (x y : V) :
    Binf x y = Binf y x := by
  have h1 := htend x y
  have h2 : Filter.Tendsto (fun n => (Lseq n).B x y) Filter.atTop (nhds (Binf y x)) := by
    have heq : (fun n => (Lseq n).B x y) = (fun n => (Lseq n).B y x) := by
      funext n; exact (Lseq n).symm x y
    rw [heq]
    exact htend y x
  exact tendsto_nhds_unique h1 h2

/-- Left additivity is preserved in the continuum weak limit. -/
theorem continuum_os_add_left
    (Lseq : ℕ → LinearOSBilinearSpace V) (Binf : V → V → ℝ)
    (htend : ∀ x y, Filter.Tendsto (fun n => (Lseq n).B x y) Filter.atTop (nhds (Binf x y)))
    (x y z : V) :
    Binf (x + y) z = Binf x z + Binf y z := by
  have h1 := htend (x + y) z
  have h2 : Filter.Tendsto (fun n => (Lseq n).B (x + y) z) Filter.atTop
      (nhds (Binf x z + Binf y z)) := by
    have heq : (fun n => (Lseq n).B (x + y) z) =
        (fun n => (Lseq n).B x z + (Lseq n).B y z) := by
      funext n; exact (Lseq n).add_left x y z
    rw [heq]
    exact (htend x z).add (htend y z)
  exact tendsto_nhds_unique h1 h2

/-- Left scalar homogeneity is preserved in the continuum weak limit. -/
theorem continuum_os_smul_left
    (Lseq : ℕ → LinearOSBilinearSpace V) (Binf : V → V → ℝ)
    (htend : ∀ x y, Filter.Tendsto (fun n => (Lseq n).B x y) Filter.atTop (nhds (Binf x y)))
    (c : ℝ) (x y : V) :
    Binf (c • x) y = c * Binf x y := by
  have h1 := htend (c • x) y
  have h2 : Filter.Tendsto (fun n => (Lseq n).B (c • x) y) Filter.atTop
      (nhds (c * Binf x y)) := by
    have heq : (fun n => (Lseq n).B (c • x) y) = (fun n => c * (Lseq n).B x y) := by
      funext n; exact (Lseq n).smul_left c x y
    rw [heq]
    exact (htend x y).const_mul c
  exact tendsto_nhds_unique h1 h2

/-- Package the continuum limit `B_∞` directly as a `LinearOSBilinearSpace V`, ready for
    `PhysicalOSHilbertSpace` reconstruction. -/
def continuumOSBilinearSpace
    (Lseq : ℕ → LinearOSBilinearSpace V) (Binf : V → V → ℝ)
    (htend : ∀ x y, Filter.Tendsto (fun n => (Lseq n).B x y) Filter.atTop (nhds (Binf x y))) :
    LinearOSBilinearSpace V where
  B := Binf
  symm := continuum_os_symm Lseq Binf htend
  add_left := continuum_os_add_left Lseq Binf htend
  smul_left := continuum_os_smul_left Lseq Binf htend
  pos_semidef := continuum_os2_reflection_positivity Lseq Binf htend

/-- OS1 Euclidean / gauge invariance survives the continuum weak limit. -/
theorem continuum_os1_invariance
    (Lseq : ℕ → LinearOSBilinearSpace V) (Binf : V → V → ℝ)
    (htend : ∀ x y, Filter.Tendsto (fun n => (Lseq n).B x y) Filter.atTop (nhds (Binf x y)))
    (g : V → V) (hinv : ∀ n x y, (Lseq n).B (g x) (g y) = (Lseq n).B x y) (x y : V) :
    Binf (g x) (g y) = Binf x y := by
  have h1 := htend (g x) (g y)
  have h2 : Filter.Tendsto (fun n => (Lseq n).B (g x) (g y)) Filter.atTop (nhds (Binf x y)) := by
    have heq : (fun n => (Lseq n).B (g x) (g y)) = (fun n => (Lseq n).B x y) := by
      funext n; exact hinv n x y
    rw [heq]
    exact htend x y
  exact tendsto_nhds_unique h1 h2

/-- Uniform OS4 exponential clustering survives the continuum weak limit with the exact
    same mass floor `m₀`. -/
theorem continuum_os4_clustering
    (Lseq : ℕ → LinearOSBilinearSpace V) (Binf : V → V → ℝ)
    (htend : ∀ x y, Filter.Tendsto (fun n => (Lseq n).B x y) Filter.atTop (nhds (Binf x y)))
    (T : ℕ → V → V) (x : V) (C m0 : ℝ)
    (hclust : ∀ n t : ℕ, (Lseq n).B (T t x) (T t x) ≤ C * Real.exp (-2 * m0 * (t : ℝ)))
    (t : ℕ) :
    Binf (T t x) (T t x) ≤ C * Real.exp (-2 * m0 * (t : ℝ)) :=
  le_of_tendsto' (htend (T t x) (T t x)) (fun n => hclust n t)

/-- A time-translation semigroup `T` that is symmetric at every finite volume `n` remains
    symmetric on `continuumOSBilinearSpace`. -/
def continuumTransferSemigroup
    (Lseq : ℕ → LinearOSBilinearSpace V) (Binf : V → V → ℝ)
    (htend : ∀ x y, Filter.Tendsto (fun n => (Lseq n).B x y) Filter.atTop (nhds (Binf x y)))
    (T : ℕ → V → V)
    (T_zero : ∀ x, T 0 x = x)
    (T_add : ∀ s t x, T (s + t) x = T s (T t x))
    (T_add_vec : ∀ t x y, T t (x + y) = T t x + T t y)
    (T_smul_vec : ∀ t (c : ℝ) x, T t (c • x) = c • T t x)
    (T_symm : ∀ n t x y, (Lseq n).B (T t x) y = (Lseq n).B x (T t y)) :
    LinearOSTransferSemigroup (continuumOSBilinearSpace Lseq Binf htend) where
  T := T
  T_zero := T_zero
  T_add := T_add
  T_symm t x y := by
    have h1 := htend (T t x) y
    have h2 : Filter.Tendsto (fun n => (Lseq n).B (T t x) y) Filter.atTop
        (nhds (Binf x (T t y))) := by
      have heq : (fun n => (Lseq n).B (T t x) y) = (fun n => (Lseq n).B x (T t y)) := by
        funext n; exact T_symm n t x y
      rw [heq]
      exact htend x (T t y)
    exact tendsto_nhds_unique h1 h2
  T_add_vec := T_add_vec
  T_smul_vec := T_smul_vec

/-- Continuum physical transfer-matrix mass gap: uniform finite-volume OS4 clustering with
    mass floor `m₀` implies the continuum transfer operator satisfies
    `‖T₀ (osMk x)‖ ≤ exp(-m₀) ‖osMk x‖`. -/
theorem continuum_transfer_mass_gap
    (Lseq : ℕ → LinearOSBilinearSpace V) (Binf : V → V → ℝ)
    (htend : ∀ x y, Filter.Tendsto (fun n => (Lseq n).B x y) Filter.atTop (nhds (Binf x y)))
    (T : ℕ → V → V)
    (T_zero : ∀ x, T 0 x = x)
    (T_add : ∀ s t x, T (s + t) x = T s (T t x))
    (T_add_vec : ∀ t x y, T t (x + y) = T t x + T t y)
    (T_smul_vec : ∀ t (c : ℝ) x, T t (c • x) = c • T t x)
    (T_symm : ∀ n t x y, (Lseq n).B (T t x) y = (Lseq n).B x (T t y))
    (hb : (continuumTransferSemigroup Lseq Binf htend T T_zero T_add T_add_vec T_smul_vec T_symm).UniformlyBounded)
    (x : V) (C m0 : ℝ) (hC : 0 ≤ C)
    (hclust : ∀ n t : ℕ, (Lseq n).B (T t x) (T t x) ≤ C * Real.exp (-2 * m0 * (t : ℝ))) :
    let Lc := continuumOSBilinearSpace Lseq Binf htend
    let Gc := continuumTransferSemigroup Lseq Binf htend T T_zero T_add T_add_vec T_smul_vec T_symm
    ‖Gc.quotientTransferOp hb (osMk Lc x)‖ ≤ Real.exp (-m0) * ‖osMk Lc x‖ := by
  intro Lc Gc
  exact Gc.quotientTransfer_clustering_norm_le hb m0 x C hC
    (continuum_os4_clustering Lseq Binf htend T x C m0 hclust)

end ContinuumLimit

end YangMills
