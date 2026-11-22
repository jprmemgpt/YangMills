import Mathlib.MeasureTheory.Measure.Haar.Unique
import YangMills.WilsonMeasure

/-!
# Module 15: HaarMeasureSeat (Lean 4 + Mathlib4)
Instantiates the abstract Haar expectation and half-space product structure of
`YangMills.WilsonMeasure` with Mathlib's concrete `MeasureTheory.Measure` and Bochner
integration machinery:
1. Normalized probability Haar integral properties (`haar_integral_const`, `haar_integral_one`,
   `haar_integral_nonneg`, `haar_integral_mono`).
2. Left, right, and conjugation invariance of the Bochner Haar integral on any measurable
   group with left/right-invariant probability measure (`haar_integral_left_inv`,
   `haar_integral_right_inv`, `haar_integral_conj_inv`).
3. Uniform Boltzmann weight bounds and strict positivity of the Bochner-integrated finite-volume
   partition function (`haar_boltzmann_bounds`, `haar_boltzmann_pos`).
4. Fubini product factorization (`haar_integral_prod_factorize`) and concrete MeasureTheory
   Osterwalder–Seiler reflection positivity on `μ.prod μ` for every positive factorized kernel
   (`haar_factorized_kernel_reflection_positive`), every exponential Taylor truncation
   `expTruncKernel K N` (`haar_os_taylor_reflection_positive`), and the `N → ∞` limit
   (`haar_os2_reflection_positivity_of_tendsto`).
-/

namespace YangMills

open MeasureTheory

/-! ## 1. Concrete Bochner Haar Integral & Invariance Laws -/

section HaarIntegral

variable {G : Type*} [Group G] [MeasurableSpace G] [MeasurableMul G]
variable {μ : Measure G} [IsProbabilityMeasure μ]

/-- The probability Haar integral of a constant function equals that constant. -/
theorem haar_integral_const (c : ℝ) : ∫ _ : G, c ∂μ = c := by
  simp

/-- Normalization of the probability Haar integral: `∫ 1 dμ = 1`. -/
theorem haar_integral_one : ∫ _ : G, (1 : ℝ) ∂μ = 1 :=
  haar_integral_const (μ := μ) 1

/-- Positivity of the Bochner Haar integral. -/
theorem haar_integral_nonneg (f : G → ℝ) (hf : ∀ x, 0 ≤ f x) :
    0 ≤ ∫ x, f x ∂μ :=
  MeasureTheory.integral_nonneg hf

/-- Monotonicity of the Bochner Haar integral for integrable observables. -/
theorem haar_integral_mono {f g : G → ℝ} (hf : Integrable f μ) (hg : Integrable g μ)
    (hfg : ∀ x, f x ≤ g x) :
    ∫ x, f x ∂μ ≤ ∫ x, g x ∂μ :=
  MeasureTheory.integral_mono hf hg hfg

/-- Exact left-translation invariance of the Bochner Haar integral. -/
theorem haar_integral_left_inv [μ.IsMulLeftInvariant] (f : G → ℝ) (g : G) :
    ∫ x, f (g * x) ∂μ = ∫ x, f x ∂μ :=
  MeasureTheory.integral_mul_left_eq_self f g

/-- Exact right-translation invariance of the Bochner Haar integral. -/
theorem haar_integral_right_inv [μ.IsMulRightInvariant] (f : G → ℝ) (g : G) :
    ∫ x, f (x * g) ∂μ = ∫ x, f x ∂μ :=
  MeasureTheory.integral_mul_right_eq_self f g

/-- Exact conjugation (adjoint gauge) invariance of a bi-invariant Bochner Haar integral:
    `∫ f(g x g⁻¹) dμ(x) = ∫ f(x) dμ(x)`. -/
theorem haar_integral_conj_inv [μ.IsMulLeftInvariant] [μ.IsMulRightInvariant]
    (f : G → ℝ) (g : G) :
    ∫ x, f (g * x * g⁻¹) ∂μ = ∫ x, f x ∂μ := by
  calc
    ∫ x, f (g * x * g⁻¹) ∂μ = ∫ x, f (x * g⁻¹) ∂μ :=
      MeasureTheory.integral_mul_left_eq_self (fun x => f (x * g⁻¹)) g
    _ = ∫ x, f x ∂μ :=
      MeasureTheory.integral_mul_right_eq_self f g⁻¹

/-- Uniform bounds on the Bochner-integrated Boltzmann partition function
    `Z = ∫ exp(-S(x)) dμ(x)` when `0 ≤ S(x) ≤ M`. -/
theorem haar_boltzmann_bounds {S : G → ℝ} {M : ℝ}
    (hS_nonneg : ∀ x, 0 ≤ S x) (hS_le : ∀ x, S x ≤ M)
    (hint : Integrable (fun x => Real.exp (-S x)) μ) :
    Real.exp (-M) ≤ ∫ x, Real.exp (-S x) ∂μ ∧ ∫ x, Real.exp (-S x) ∂μ ≤ 1 := by
  constructor
  · have hlo := MeasureTheory.integral_mono (integrable_const (Real.exp (-M))) hint
      (fun x => Real.exp_le_exp.mpr (by linarith [hS_le x]))
    simpa [haar_integral_const] using hlo
  · have hhi := MeasureTheory.integral_mono hint (integrable_const (1 : ℝ))
      (fun x => by
        calc
          Real.exp (-S x) ≤ Real.exp 0 := Real.exp_le_exp.mpr (by linarith [hS_nonneg x])
          _ = 1 := Real.exp_zero)
    simpa [haar_integral_one] using hhi

/-- Strict positivity of the Bochner-integrated Boltzmann partition function. -/
theorem haar_boltzmann_pos {S : G → ℝ} {M : ℝ}
    (hS_nonneg : ∀ x, 0 ≤ S x) (hS_le : ∀ x, S x ≤ M)
    (hint : Integrable (fun x => Real.exp (-S x)) μ) :
    0 < ∫ x, Real.exp (-S x) ∂μ :=
  lt_of_lt_of_le (Real.exp_pos (-M)) (haar_boltzmann_bounds hS_nonneg hS_le hint).1

end HaarIntegral

/-! ## 2. Concrete Product Measure Fubini Factorization & Osterwalder–Seiler Reflection Positivity -/

section ProductReflectionPositivity

variable {α : Type*} [MeasurableSpace α] {μ : Measure α} [IsProbabilityMeasure μ]

/-- Concrete Fubini factorization on the half-space product measure `μ.prod μ`:
    `∫ f(u) g(v) d(μ × μ)(u, v) = (∫ f dμ) · (∫ g dμ)`. -/
theorem haar_integral_prod_factorize (f g : α → ℝ) :
    ∫ p : α × α, f p.1 * g p.2 ∂(μ.prod μ) = (∫ u, f u ∂μ) * (∫ v, g v ∂μ) :=
  MeasureTheory.integral_prod_mul f g

/-- Bare half-space reflection positivity on `μ.prod μ`:
    `∫ f(u) f(v) d(μ × μ)(u, v) = (∫ f dμ)² ≥ 0`. -/
theorem haar_reflection_positive_square (f : α → ℝ) :
    0 ≤ ∫ p : α × α, f p.1 * f p.2 ∂(μ.prod μ) := by
  rw [MeasureTheory.integral_prod_mul]
  exact mul_self_nonneg _

/-- Termwise half-space integrability of a weighted factorized kernel `K`. -/
def KernelIntegrable (μ : Measure α) (F S_plus : α → ℝ)
    (K : List (ℝ × (α → ℝ))) : Prop :=
  ∀ q ∈ K, Integrable (fun u => F u * Real.exp (-S_plus u) * q.2 u) μ

/-- Every termwise-integrable factorized kernel yields a `μ.prod μ`-integrable
    reflection-positivity integrand. -/
theorem evalKernel_weighted_integrable (F S_plus : α → ℝ) (K : List (ℝ × (α → ℝ)))
    (hint : KernelIntegrable μ F S_plus K) :
    Integrable (fun p : α × α =>
      F p.1 * F p.2 * Real.exp (-S_plus p.1) * Real.exp (-S_plus p.2) *
        evalKernel K p.1 p.2) (μ.prod μ) := by
  induction K with
  | nil =>
    have h0 : (fun p : α × α =>
      F p.1 * F p.2 * Real.exp (-S_plus p.1) * Real.exp (-S_plus p.2) *
        evalKernel [] p.1 p.2) = fun _ => 0 := by
      funext p; simp [evalKernel]
    rw [h0]
    exact integrable_zero _ _ _
  | cons q qs ih =>
    have hq_int : Integrable (fun u => F u * Real.exp (-S_plus u) * q.2 u) μ :=
      hint q (by simp)
    have hqs_int : KernelIntegrable μ F S_plus qs :=
      fun r hr => hint r (by simp [hr])
    have hhead : Integrable (fun p : α × α =>
      q.1 * ((F p.1 * Real.exp (-S_plus p.1) * q.2 p.1) *
        (F p.2 * Real.exp (-S_plus p.2) * q.2 p.2))) (μ.prod μ) :=
      (hq_int.mul_prod hq_int).const_mul q.1
    have htail := ih hqs_int
    have hsplit :
        (fun p : α × α =>
          F p.1 * F p.2 * Real.exp (-S_plus p.1) * Real.exp (-S_plus p.2) *
            evalKernel (q :: qs) p.1 p.2) =
        (fun p : α × α =>
          q.1 * ((F p.1 * Real.exp (-S_plus p.1) * q.2 p.1) *
            (F p.2 * Real.exp (-S_plus p.2) * q.2 p.2)) +
          F p.1 * F p.2 * Real.exp (-S_plus p.1) * Real.exp (-S_plus p.2) *
            evalKernel qs p.1 p.2) := by
      funext p
      simp only [evalKernel, List.map_cons, List.sum_cons]
      ring
    rw [hsplit]
    exact hhead.add htail

/-- Concrete MeasureTheory Osterwalder–Seiler reflection positivity:
    for any positive factorized kernel `K` on `α × α`, the Bochner integral on `μ.prod μ`
    is a non-negative weighted sum of squares. -/
theorem haar_factorized_kernel_reflection_positive (F S_plus : α → ℝ)
    (K : List (ℝ × (α → ℝ))) (hK : allNonneg K)
    (hint : KernelIntegrable μ F S_plus K) :
    0 ≤ ∫ p : α × α,
      F p.1 * F p.2 * Real.exp (-S_plus p.1) * Real.exp (-S_plus p.2) *
        evalKernel K p.1 p.2 ∂(μ.prod μ) := by
  induction K with
  | nil =>
    have h0 : (fun p : α × α =>
      F p.1 * F p.2 * Real.exp (-S_plus p.1) * Real.exp (-S_plus p.2) *
        evalKernel [] p.1 p.2) = fun _ => 0 := by
      funext p; simp [evalKernel]
    rw [h0]
    simp
  | cons q qs ih =>
    have hq : 0 ≤ q.1 := hK q (by simp)
    have hqs : allNonneg qs := fun r hr => hK r (by simp [hr])
    have hq_int : Integrable (fun u => F u * Real.exp (-S_plus u) * q.2 u) μ :=
      hint q (by simp)
    have hqs_int : KernelIntegrable μ F S_plus qs :=
      fun r hr => hint r (by simp [hr])
    have hhead_int : Integrable (fun p : α × α =>
      q.1 * ((F p.1 * Real.exp (-S_plus p.1) * q.2 p.1) *
        (F p.2 * Real.exp (-S_plus p.2) * q.2 p.2))) (μ.prod μ) :=
      (hq_int.mul_prod hq_int).const_mul q.1
    have htail_int := evalKernel_weighted_integrable (μ := μ) F S_plus qs hqs_int
    have hsplit :
        (fun p : α × α =>
          F p.1 * F p.2 * Real.exp (-S_plus p.1) * Real.exp (-S_plus p.2) *
            evalKernel (q :: qs) p.1 p.2) =
        (fun p : α × α =>
          q.1 * ((F p.1 * Real.exp (-S_plus p.1) * q.2 p.1) *
            (F p.2 * Real.exp (-S_plus p.2) * q.2 p.2)) +
          F p.1 * F p.2 * Real.exp (-S_plus p.1) * Real.exp (-S_plus p.2) *
            evalKernel qs p.1 p.2) := by
      funext p
      simp only [evalKernel, List.map_cons, List.sum_cons]
      ring
    rw [hsplit, MeasureTheory.integral_add hhead_int htail_int,
      MeasureTheory.integral_const_mul,
      MeasureTheory.integral_prod_mul
        (fun u => F u * Real.exp (-S_plus u) * q.2 u)
        (fun u => F u * Real.exp (-S_plus u) * q.2 u)]
    have hterm : 0 ≤ q.1 * ((∫ u, F u * Real.exp (-S_plus u) * q.2 u ∂μ) *
        (∫ u, F u * Real.exp (-S_plus u) * q.2 u ∂μ)) :=
      mul_nonneg hq (mul_self_nonneg _)
    linarith [ih hqs hqs_int]

/-- Concrete MeasureTheory Osterwalder–Seiler reflection positivity at every exponential
    Taylor order `N` on `μ.prod μ`. -/
theorem haar_os_taylor_reflection_positive (F S_plus : α → ℝ)
    (K : List (ℝ × (α → ℝ))) (hK : allNonneg K) (N : ℕ)
    (hint : KernelIntegrable μ F S_plus (expTruncKernel K N)) :
    0 ≤ ∫ p : α × α,
      F p.1 * F p.2 * Real.exp (-S_plus p.1) * Real.exp (-S_plus p.2) *
        evalKernel (expTruncKernel K N) p.1 p.2 ∂(μ.prod μ) :=
  haar_factorized_kernel_reflection_positive F S_plus (expTruncKernel K N)
    (allNonneg_expTrunc hK N) hint

/-- Concrete MeasureTheory OS2 reflection positivity in the `N → ∞` limit via `Filter.Tendsto`. -/
theorem haar_os2_reflection_positivity_of_tendsto (F S_plus : α → ℝ)
    (K : List (ℝ × (α → ℝ))) (hK : allNonneg K)
    (hint : ∀ N : ℕ, KernelIntegrable μ F S_plus (expTruncKernel K N))
    (E_full : ℝ)
    (hlim : Filter.Tendsto
      (fun N : ℕ =>
        ∫ p : α × α,
          F p.1 * F p.2 * Real.exp (-S_plus p.1) * Real.exp (-S_plus p.2) *
            evalKernel (expTruncKernel K N) p.1 p.2 ∂(μ.prod μ))
      Filter.atTop (nhds E_full)) :
    0 ≤ E_full :=
  ge_of_tendsto' hlim (fun N => haar_os_taylor_reflection_positive F S_plus K hK N (hint N))

end ProductReflectionPositivity

end YangMills
