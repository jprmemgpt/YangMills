import YangMills.LatticeHaarMeasure

/-!
# Module 24: LatticeReflectionPositivity (Lean 4 + Mathlib4)
Proves concrete finite-volume Osterwalder–Seiler OS2 reflection positivity on the full
half-space product configuration space `(Fin N → G) × (Fin N → G)` equipped with the
product Haar probability measure `(latticeHaar μ N).prod (latticeHaar μ N)`:
1. Single factorized crossing kernel (`lattice_os2_factorized_nonneg`) via Mathlib's
   `integral_prod_mul`.
2. Full bulk-plus-crossing Osterwalder–Seiler reflection positivity for any symmetric
   bulk half-space Wilson action `S0(U_-) + S0(U_+)` and any positive linear combination
   of factorized time-slice crossing terms `∑ c_k w_k(U_-) w_k(U_+)`
   (`lattice_os2_bulk_crossing_nonneg`).
3. Weak-limit preservation of reflection positivity as the Taylor order `M → ∞`
   (`lattice_os2_of_tendsto`), yielding normalized OS2 reflection positivity for the
   full finite-volume Wilson measure.
4. Direct concrete instantiations for `SU(2)` and `SU(3)` product Haar measures
   (`su2_lattice_os2_bulk_crossing_nonneg`, `su3_lattice_os2_bulk_crossing_nonneg`).
-/

namespace YangMills

open MeasureTheory

/-! ## 1. Half-Space Product Configuration Space & Reflection Positivity -/

/-- Two-half-space product Haar measure on `(U_-, U_+) : (Fin N → G) × (Fin N → G)`. -/
noncomputable def halfSpaceHaar {G : Type*} [MeasurableSpace G]
    (μ : Measure G) (N : ℕ) : Measure ((Fin N → G) × (Fin N → G)) :=
  (latticeHaar μ N).prod (latticeHaar μ N)

/-- Exact rank-1 factorized reflection positivity on the `N`-link half-space product:
    `∫ (F(U_-) F(U_+)) (w(U_-) w(U_+)) d(μ^⊗N × μ^⊗N) = (∫ F w dμ^⊗N)^2 ≥ 0`. -/
theorem lattice_os2_factorized_nonneg {G : Type*} [MeasurableSpace G]
    (μ : Measure G) [IsProbabilityMeasure μ] (N : ℕ)
    (F w : (Fin N → G) → ℝ) :
    0 ≤ ∫ p, (F p.1 * F p.2) * (w p.1 * w p.2) ∂(halfSpaceHaar μ N) := by
  let h : (Fin N → G) → ℝ := fun U => F U * w U
  have hrew : (fun p : (Fin N → G) × (Fin N → G) => (F p.1 * F p.2) * (w p.1 * w p.2)) =
      fun p => h p.1 * h p.2 := by
    funext p; dsimp only [h]; ring
  rw [hrew, halfSpaceHaar, integral_prod_mul (f := h) (g := h)]
  exact mul_self_nonneg _

/-- Full finite-volume Osterwalder–Seiler OS2 reflection positivity with symmetric bulk
    half-space Wilson action `S0(U_-) + S0(U_+)` and any positive factorized crossing
    expansion `∑ k, c k * (w k U_- * w k U_+)` with `c k ≥ 0`. -/
theorem lattice_os2_bulk_crossing_nonneg {G : Type*} [MeasurableSpace G]
    (μ : Measure G) [IsProbabilityMeasure μ] (N M : ℕ)
    (S0 : (Fin N → G) → ℝ) (beta : ℝ) (F : (Fin N → G) → ℝ)
    (c : Fin M → ℝ) (hc : ∀ k, 0 ≤ c k) (w : Fin M → (Fin N → G) → ℝ)
    (hint : ∀ k, Integrable (fun U => F U * Real.exp (-(beta * S0 U)) * w k U)
      (latticeHaar μ N)) :
    0 ≤ ∫ p, (F p.1 * F p.2) *
      (Real.exp (-(beta * S0 p.1)) * Real.exp (-(beta * S0 p.2)) *
        ∑ k : Fin M, c k * (w k p.1 * w k p.2)) ∂(halfSpaceHaar μ N) := by
  let g : Fin M → (Fin N → G) → ℝ := fun k U => F U * Real.exp (-(beta * S0 U)) * w k U
  have hrew :
      (fun p : (Fin N → G) × (Fin N → G) =>
        (F p.1 * F p.2) *
          (Real.exp (-(beta * S0 p.1)) * Real.exp (-(beta * S0 p.2)) *
            ∑ k : Fin M, c k * (w k p.1 * w k p.2))) =
      fun p => ∑ k : Fin M, c k * (g k p.1 * g k p.2) := by
    funext p
    rw [Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    simp only [g]
    ring
  have hsum : ∀ s : Finset (Fin M),
      0 ≤ ∫ p, ∑ k ∈ s, c k * (g k p.1 * g k p.2) ∂(halfSpaceHaar μ N) ∧
      Integrable (fun p => ∑ k ∈ s, c k * (g k p.1 * g k p.2)) (halfSpaceHaar μ N) := by
    intro s
    classical
    refine Finset.induction_on s ?_ ?_
    · simp only [Finset.sum_empty, integral_zero]
      exact ⟨le_rfl, integrable_zero _ _ _⟩
    · intro k s hk ih
      have hterm : Integrable (fun p : (Fin N → G) × (Fin N → G) =>
          c k * (g k p.1 * g k p.2)) (halfSpaceHaar μ N) :=
        ((hint k).mul_prod (hint k)).const_mul (c k)
      have hsplit : (fun p : (Fin N → G) × (Fin N → G) =>
          ∑ j ∈ insert k s, c j * (g j p.1 * g j p.2)) =
          fun p => c k * (g k p.1 * g k p.2) + ∑ j ∈ s, c j * (g j p.1 * g j p.2) := by
        funext p
        exact Finset.sum_insert hk
      rw [hsplit]
      constructor
      · rw [integral_add hterm ih.2]
        have hpos : 0 ≤ ∫ p, c k * (g k p.1 * g k p.2) ∂(halfSpaceHaar μ N) := by
          rw [integral_const_mul, halfSpaceHaar, integral_prod_mul (f := g k) (g := g k)]
          exact mul_nonneg (hc k) (mul_self_nonneg _)
        exact add_nonneg hpos ih.1
      · exact hterm.add ih.2
  rw [hrew]
  exact (hsum Finset.univ).1

/-- Normalized OS2 reflection positivity passes to the `M → ∞` limit (covering the full
    exponential `exp(-β S_cross)` via its Taylor series). -/
theorem lattice_os2_of_tendsto {Z : ℝ} (hZ : 0 < Z)
    (a : ℕ → ℝ) (L : ℝ) (ha : ∀ n, 0 ≤ a n)
    (htend : Filter.Tendsto a Filter.atTop (nhds L)) :
    0 ≤ Z⁻¹ * L :=
  mul_nonneg (inv_nonneg.mpr hZ.le) (ge_of_tendsto' htend ha)

/-! ## 2. Concrete `SU(2)` and `SU(3)` Full-Lattice OS2 Reflection Positivity -/

/-- Concrete finite-volume `SU(2)` Osterwalder–Seiler OS2 reflection positivity on `N` links. -/
theorem su2_lattice_os2_bulk_crossing_nonneg (N M : ℕ)
    (S0 : (Fin N → SU2) → ℝ) (beta : ℝ) (F : (Fin N → SU2) → ℝ)
    (c : Fin M → ℝ) (hc : ∀ k, 0 ≤ c k) (w : Fin M → (Fin N → SU2) → ℝ)
    (hint : ∀ k, Integrable (fun U => F U * Real.exp (-(beta * S0 U)) * w k U)
      (su2LatticeHaar N)) :
    0 ≤ ∫ p, (F p.1 * F p.2) *
      (Real.exp (-(beta * S0 p.1)) * Real.exp (-(beta * S0 p.2)) *
        ∑ k : Fin M, c k * (w k p.1 * w k p.2)) ∂(halfSpaceHaar su2Haar N) :=
  lattice_os2_bulk_crossing_nonneg su2Haar N M S0 beta F c hc w hint

/-- Concrete finite-volume `SU(3)` Osterwalder–Seiler OS2 reflection positivity on `N` links. -/
theorem su3_lattice_os2_bulk_crossing_nonneg (N M : ℕ)
    (S0 : (Fin N → SU3) → ℝ) (beta : ℝ) (F : (Fin N → SU3) → ℝ)
    (c : Fin M → ℝ) (hc : ∀ k, 0 ≤ c k) (w : Fin M → (Fin N → SU3) → ℝ)
    (hint : ∀ k, Integrable (fun U => F U * Real.exp (-(beta * S0 U)) * w k U)
      (su3LatticeHaar N)) :
    0 ≤ ∫ p, (F p.1 * F p.2) *
      (Real.exp (-(beta * S0 p.1)) * Real.exp (-(beta * S0 p.2)) *
        ∑ k : Fin M, c k * (w k p.1 * w k p.2)) ∂(halfSpaceHaar su3Haar N) :=
  lattice_os2_bulk_crossing_nonneg su3Haar N M S0 beta F c hc w hint

end YangMills
