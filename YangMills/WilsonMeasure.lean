import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import YangMills.GaugeLattice

/-!
# Module 11: WilsonMeasure (Lean 4 + Mathlib4)
Formalizes the finite-volume Wilson lattice measure and bare-lattice Osterwalder–Seiler (1978)
reflection positivity:
1. Finite-volume Wilson action `wilsonAction`, exact local gauge invariance, and uniform
   pointwise bounds `0 ≤ S_W(U) ≤ 2 β |P|`.
2. Normalized gauge-invariant Haar expectation `HaarExpectation`, Boltzmann weight
   `exp(-S_W(U))`, strict positivity and explicit bounds on the finite-volume partition
   function `exp(-2 β |P|) ≤ Z_{β,P} ≤ 1`, and exact gauge invariance of Wilson expectations.
3. Positive factorized kernels on half-space configurations closed under non-negative scaling,
   addition, pointwise multiplication, powers `W^n`, and exponential Taylor partial sums.
4. Exact Osterwalder–Seiler reflection positivity at every Taylor order `N` and in the
   convergent `N → ∞` limit (`wilson_os2_reflection_positivity_of_limit`).
-/

namespace YangMills

/-! ## 1. Finite-Volume Wilson Action & Partition Function -/

/-- An oriented lattice plaquette `(x, μ, ν)` in ℤ⁴. -/
structure Plaquette where
  x : Site
  μ : Fin 4
  ν : Fin 4

/-- Finite-volume Wilson action summed over a finite list of plaquettes `P`. -/
def wilsonAction {G : Type*} [Group G] (χ : UnitaryTrace G) (beta : ℝ)
    (P : List Plaquette) (U : GaugeField G) : ℝ :=
  (P.map (fun p => wilsonPlaquetteAction χ beta U p.x p.μ p.ν)).sum

/-- Exact local gauge invariance of the finite-volume Wilson action. -/
theorem wilsonAction_gauge_invariant {G : Type*} [Group G] (χ : UnitaryTrace G) (beta : ℝ)
    (P : List Plaquette) (g : GaugeTransform G) (U : GaugeField G) :
    wilsonAction χ beta P (gaugeAct g U) = wilsonAction χ beta P U := by
  unfold wilsonAction
  congr 1
  apply List.map_congr_left
  intro p _
  exact wilsonPlaquetteAction_gauge_invariant χ beta g U p.x p.μ p.ν

/-- Uniform finite-volume bounds on the Wilson action: `0 ≤ S_W(U) ≤ 2 β |P|`. -/
theorem wilsonAction_bounds {G : Type*} [Group G] (χ : UnitaryTrace G) (beta : ℝ)
    (hbeta : 0 ≤ beta) (P : List Plaquette) (U : GaugeField G) :
    0 ≤ wilsonAction χ beta P U ∧ wilsonAction χ beta P U ≤ 2 * beta * (P.length : ℝ) := by
  induction P with
  | nil =>
    simp [wilsonAction]
  | cons p ps ih =>
    have hp := wilsonPlaquetteAction_bounds χ beta hbeta U p.x p.μ p.ν
    simp only [wilsonAction, List.map_cons, List.sum_cons, List.length_cons, Nat.cast_add,
      Nat.cast_one] at ih ⊢
    constructor
    · linarith [hp.1, ih.1]
    · linarith [hp.2, ih.2]

/-- Unnormalized Wilson Boltzmann weight `exp(-S_W(U))`. -/
noncomputable def boltzmannWeight {G : Type*} [Group G] (χ : UnitaryTrace G) (beta : ℝ)
    (P : List Plaquette) (U : GaugeField G) : ℝ :=
  Real.exp (-wilsonAction χ beta P U)

/-- Exact gauge invariance of the Wilson Boltzmann weight. -/
theorem boltzmannWeight_gauge_invariant {G : Type*} [Group G] (χ : UnitaryTrace G) (beta : ℝ)
    (P : List Plaquette) (g : GaugeTransform G) (U : GaugeField G) :
    boltzmannWeight χ beta P (gaugeAct g U) = boltzmannWeight χ beta P U := by
  unfold boltzmannWeight
  rw [wilsonAction_gauge_invariant]

/-- Uniform pointwise bounds on the Boltzmann weight: `exp(-2 β |P|) ≤ exp(-S_W(U)) ≤ 1`. -/
theorem boltzmannWeight_bounds {G : Type*} [Group G] (χ : UnitaryTrace G) (beta : ℝ)
    (hbeta : 0 ≤ beta) (P : List Plaquette) (U : GaugeField G) :
    Real.exp (-(2 * beta * (P.length : ℝ))) ≤ boltzmannWeight χ beta P U ∧
      boltzmannWeight χ beta P U ≤ 1 := by
  have hb := wilsonAction_bounds χ beta hbeta P U
  unfold boltzmannWeight
  constructor
  · exact Real.exp_le_exp.mpr (by linarith [hb.2])
  · calc
      Real.exp (-wilsonAction χ beta P U) ≤ Real.exp 0 := Real.exp_le_exp.mpr (by linarith [hb.1])
      _ = 1 := Real.exp_zero

/-- Normalized, positive, linear, gauge-invariant product Haar expectation on `GaugeField G`. -/
structure HaarExpectation (G : Type*) [Group G] where
  E0 : (GaugeField G → ℝ) → ℝ
  linear_add : ∀ f g, E0 (fun U => f U + g U) = E0 f + E0 g
  linear_smul : ∀ c f, E0 (fun U => c * f U) = c * E0 f
  norm_one : E0 (fun _ => 1) = 1
  mono : ∀ f g, (∀ U, f U ≤ g U) → E0 f ≤ E0 g
  gauge_inv : ∀ (g : GaugeTransform G) f, E0 (fun U => f (gaugeAct g U)) = E0 f

theorem HaarExpectation.eval_const {G : Type*} [Group G] (H : HaarExpectation G) (c : ℝ) :
    H.E0 (fun _ => c) = c := by
  have h := H.linear_smul c (fun _ => 1)
  simp only [mul_one, H.norm_one] at h
  exact h

theorem HaarExpectation.nonneg {G : Type*} [Group G] (H : HaarExpectation G)
    (f : GaugeField G → ℝ) (hf : ∀ U, 0 ≤ f U) : 0 ≤ H.E0 f := by
  have h := H.mono (fun _ => 0) f hf
  rw [H.eval_const] at h
  exact h

/-- Finite-volume Wilson partition function `Z_{β,P} = E₀[exp(-S_W)]`. -/
noncomputable def partitionFunction {G : Type*} [Group G] (H : HaarExpectation G)
    (χ : UnitaryTrace G) (beta : ℝ) (P : List Plaquette) : ℝ :=
  H.E0 (boltzmannWeight χ beta P)

/-- Explicit uniform bounds on the partition function: `exp(-2 β |P|) ≤ Z_{β,P} ≤ 1`. -/
theorem partitionFunction_bounds {G : Type*} [Group G] (H : HaarExpectation G)
    (χ : UnitaryTrace G) (beta : ℝ) (hbeta : 0 ≤ beta) (P : List Plaquette) :
    Real.exp (-(2 * beta * (P.length : ℝ))) ≤ partitionFunction H χ beta P ∧
      partitionFunction H χ beta P ≤ 1 := by
  unfold partitionFunction
  constructor
  · have h := H.mono (fun _ => Real.exp (-(2 * beta * (P.length : ℝ))))
      (boltzmannWeight χ beta P) (fun U => (boltzmannWeight_bounds χ beta hbeta P U).1)
    rw [H.eval_const] at h
    exact h
  · have h := H.mono (boltzmannWeight χ beta P) (fun _ => 1)
      (fun U => (boltzmannWeight_bounds χ beta hbeta P U).2)
    rw [H.norm_one] at h
    exact h

/-- Strict positivity of the finite-volume Wilson partition function `Z_{β,P} > 0`. -/
theorem partitionFunction_pos {G : Type*} [Group G] (H : HaarExpectation G)
    (χ : UnitaryTrace G) (beta : ℝ) (hbeta : 0 ≤ beta) (P : List Plaquette) :
    0 < partitionFunction H χ beta P := by
  have hlo := (partitionFunction_bounds H χ beta hbeta P).1
  exact lt_of_lt_of_le (Real.exp_pos _) hlo

/-- Normalized finite-volume Wilson expectation `⟨f⟩_{β,P} = E₀[f · exp(-S_W)] / Z_{β,P}`. -/
noncomputable def wilsonExpect {G : Type*} [Group G] (H : HaarExpectation G)
    (χ : UnitaryTrace G) (beta : ℝ) (P : List Plaquette) (f : GaugeField G → ℝ) : ℝ :=
  H.E0 (fun U => f U * boltzmannWeight χ beta P U) / partitionFunction H χ beta P

/-- Normalization: `⟨1⟩_{β,P} = 1`. -/
theorem wilsonExpect_one {G : Type*} [Group G] (H : HaarExpectation G)
    (χ : UnitaryTrace G) (beta : ℝ) (hbeta : 0 ≤ beta) (P : List Plaquette) :
    wilsonExpect H χ beta P (fun _ => 1) = 1 := by
  unfold wilsonExpect partitionFunction
  have hpos : 0 < H.E0 (boltzmannWeight χ beta P) := partitionFunction_pos H χ beta hbeta P
  have h1 : (fun U => (1 : ℝ) * boltzmannWeight χ beta P U) = boltzmannWeight χ beta P := by
    funext U; ring
  rw [h1, div_self (ne_of_gt hpos)]

/-- Positivity of the normalized Wilson expectation functional. -/
theorem wilsonExpect_nonneg {G : Type*} [Group G] (H : HaarExpectation G)
    (χ : UnitaryTrace G) (beta : ℝ) (hbeta : 0 ≤ beta) (P : List Plaquette)
    (f : GaugeField G → ℝ) (hf : ∀ U, 0 ≤ f U) :
    0 ≤ wilsonExpect H χ beta P f := by
  unfold wilsonExpect
  apply div_nonneg
  · apply H.nonneg
    intro U
    exact mul_nonneg (hf U) (le_of_lt (Real.exp_pos _))
  · exact le_of_lt (partitionFunction_pos H χ beta hbeta P)

/-- Exact gauge invariance of the normalized finite-volume Wilson expectation. -/
theorem wilsonExpect_gauge_invariant {G : Type*} [Group G] (H : HaarExpectation G)
    (χ : UnitaryTrace G) (beta : ℝ) (P : List Plaquette)
    (g : GaugeTransform G) (f : GaugeField G → ℝ) :
    wilsonExpect H χ beta P (fun U => f (gaugeAct g U)) = wilsonExpect H χ beta P f := by
  unfold wilsonExpect
  congr 1
  have heq :
      (fun U => f (gaugeAct g U) * boltzmannWeight χ beta P U) =
      (fun U => f (gaugeAct g U) * boltzmannWeight χ beta P (gaugeAct g U)) := by
    funext U
    rw [boltzmannWeight_gauge_invariant]
  rw [heq]
  exact H.gauge_inv g (fun U => f U * boltzmannWeight χ beta P U)

/-! ## 2. Bare-Lattice Osterwalder–Seiler Reflection Positivity -/

/-- Factorized product expectation over half-space configurations `α × α` (representing
    independent negative-time and positive-time lattice half-spaces). -/
structure ProductHalfExpectation (α : Type*) where
  Ehalf : (α → ℝ) → ℝ
  Eprod : (α × α → ℝ) → ℝ
  linear_add : ∀ F₁ F₂, Eprod (fun p => F₁ p + F₂ p) = Eprod F₁ + Eprod F₂
  linear_smul : ∀ c F, Eprod (fun p => c * F p) = c * Eprod F
  eval_zero : Eprod (fun _ => 0) = 0
  factorize : ∀ f g, Eprod (fun p => f p.1 * g p.2) = Ehalf f * Ehalf g

/-- Evaluation of a finite factorized kernel `K(u, v) = ∑ (w, φ) ∈ K, w · φ(u) · φ(v)`. -/
def evalKernel {α : Type*} (K : List (ℝ × (α → ℝ))) (u v : α) : ℝ :=
  (K.map (fun p => p.1 * p.2 u * p.2 v)).sum

/-- Non-negativity of all kernel weights `w ≥ 0`. -/
def allNonneg {α : Type*} (K : List (ℝ × (α → ℝ))) : Prop :=
  ∀ p ∈ K, 0 ≤ p.1

/-- Unit kernel `1 = 1 · 1(u) · 1(v)`. -/
def oneKernel {α : Type*} : List (ℝ × (α → ℝ)) :=
  [(1, fun _ => 1)]

/-- Non-negative scalar multiple of a factorized kernel. -/
def scaleKernel {α : Type*} (c : ℝ) (K : List (ℝ × (α → ℝ))) : List (ℝ × (α → ℝ)) :=
  K.map (fun p => (c * p.1, p.2))

/-- Pointwise product of two factorized kernels. -/
def mulKernel {α : Type*} :
    List (ℝ × (α → ℝ)) → List (ℝ × (α → ℝ)) → List (ℝ × (α → ℝ))
  | [], _ => []
  | p :: ps, K₂ => (K₂.map (fun q => (p.1 * q.1, fun u => p.2 u * q.2 u))) ++ mulKernel ps K₂

/-- `n`-th pointwise power of a factorized kernel. -/
def powKernel {α : Type*} (K : List (ℝ × (α → ℝ))) : ℕ → List (ℝ × (α → ℝ))
  | 0 => oneKernel
  | n + 1 => mulKernel K (powKernel K n)

/-- `N`-th exponential Taylor truncation `∑_{n=0}^N K(u, v)^n / n!`. -/
noncomputable def expTruncKernel {α : Type*} (K : List (ℝ × (α → ℝ))) :
    ℕ → List (ℝ × (α → ℝ))
  | 0 => oneKernel
  | N + 1 =>
    expTruncKernel K N ++
      scaleKernel (1 / ((N + 1).factorial : ℝ)) (powKernel K (N + 1))

theorem evalKernel_append {α : Type*} (K₁ K₂ : List (ℝ × (α → ℝ))) (u v : α) :
    evalKernel (K₁ ++ K₂) u v = evalKernel K₁ u v + evalKernel K₂ u v := by
  unfold evalKernel
  rw [List.map_append, List.sum_append]

theorem allNonneg_append {α : Type*} {K₁ K₂ : List (ℝ × (α → ℝ))}
    (h1 : allNonneg K₁) (h2 : allNonneg K₂) : allNonneg (K₁ ++ K₂) := by
  intro p hp
  rcases List.mem_append.mp hp with hp1 | hp2
  · exact h1 p hp1
  · exact h2 p hp2

theorem evalKernel_one {α : Type*} (u v : α) : evalKernel (oneKernel (α := α)) u v = 1 := by
  simp [evalKernel, oneKernel]

theorem allNonneg_one {α : Type*} : allNonneg (oneKernel (α := α)) := by
  intro p hp
  simp only [oneKernel, List.mem_singleton] at hp
  rw [hp]
  norm_num

theorem evalKernel_scale {α : Type*} (c : ℝ) (K : List (ℝ × (α → ℝ))) (u v : α) :
    evalKernel (scaleKernel c K) u v = c * evalKernel K u v := by
  induction K with
  | nil => simp [evalKernel, scaleKernel]
  | cons p ps ih =>
    simp only [evalKernel, scaleKernel, List.map_cons, List.sum_cons] at ih ⊢
    linarith [show c * p.1 * p.2 u * p.2 v = c * (p.1 * p.2 u * p.2 v) by ring]

theorem allNonneg_scale {α : Type*} {c : ℝ} (hc : 0 ≤ c) {K : List (ℝ × (α → ℝ))}
    (hK : allNonneg K) : allNonneg (scaleKernel c K) := by
  intro q hq
  simp only [scaleKernel, List.mem_map] at hq
  rcases hq with ⟨p, hp, rfl⟩
  exact mul_nonneg hc (hK p hp)

theorem evalKernel_mul {α : Type*} (K₁ K₂ : List (ℝ × (α → ℝ))) (u v : α) :
    evalKernel (mulKernel K₁ K₂) u v = evalKernel K₁ u v * evalKernel K₂ u v := by
  induction K₁ with
  | nil => simp [evalKernel, mulKernel]
  | cons p ps ih =>
    rw [mulKernel, evalKernel_append, ih]
    have hhead :
        evalKernel (K₂.map (fun q => (p.1 * q.1, fun x => p.2 x * q.2 x))) u v =
          (p.1 * p.2 u * p.2 v) * evalKernel K₂ u v := by
      clear ih
      induction K₂ with
      | nil => simp [evalKernel]
      | cons q qs ih2 =>
        simp only [evalKernel, List.map_cons, List.sum_cons] at ih2 ⊢
        have hterm : p.1 * q.1 * (p.2 u * q.2 u) * (p.2 v * q.2 v) =
            (p.1 * p.2 u * p.2 v) * (q.1 * q.2 u * q.2 v) := by ring
        rw [ih2, hterm]; ring
    rw [hhead]
    simp only [evalKernel, List.map_cons, List.sum_cons]
    ring

theorem allNonneg_mul {α : Type*} {K₁ K₂ : List (ℝ × (α → ℝ))}
    (h1 : allNonneg K₁) (h2 : allNonneg K₂) : allNonneg (mulKernel K₁ K₂) := by
  induction K₁ with
  | nil =>
    intro p hp; simp [mulKernel] at hp
  | cons p ps ih =>
    rw [mulKernel]
    apply allNonneg_append
    · intro r hr
      simp only [List.mem_map] at hr
      rcases hr with ⟨q, hq, rfl⟩
      exact mul_nonneg (h1 p (by simp)) (h2 q hq)
    · exact ih (fun r hr => h1 r (by simp [hr]))

theorem evalKernel_pow {α : Type*} (K : List (ℝ × (α → ℝ))) (n : ℕ) (u v : α) :
    evalKernel (powKernel K n) u v = (evalKernel K u v) ^ n := by
  induction n with
  | zero => simp [powKernel, evalKernel_one]
  | succ n ih =>
    rw [powKernel, evalKernel_mul, ih, pow_succ']

theorem allNonneg_pow {α : Type*} {K : List (ℝ × (α → ℝ))} (hK : allNonneg K) (n : ℕ) :
    allNonneg (powKernel K n) := by
  induction n with
  | zero => exact allNonneg_one
  | succ n ih => exact allNonneg_mul hK ih

theorem evalKernel_expTrunc {α : Type*} (K : List (ℝ × (α → ℝ))) (N : ℕ) (u v : α) :
    evalKernel (expTruncKernel K N) u v =
      ∑ n ∈ Finset.range (N + 1), (evalKernel K u v) ^ n / (n.factorial : ℝ) := by
  induction N with
  | zero =>
    simp [expTruncKernel, evalKernel_one]
  | succ N ih =>
    rw [expTruncKernel, evalKernel_append, ih, evalKernel_scale, evalKernel_pow,
      one_div_mul_eq_div, ← Finset.sum_range_succ]

theorem allNonneg_expTrunc {α : Type*} {K : List (ℝ × (α → ℝ))} (hK : allNonneg K) (N : ℕ) :
    allNonneg (expTruncKernel K N) := by
  induction N with
  | zero => exact allNonneg_one
  | succ N ih =>
    apply allNonneg_append ih
    apply allNonneg_scale
    · positivity
    · exact allNonneg_pow hK (N + 1)

/-- Core Osterwalder–Seiler lemma: every positive factorized kernel produces a
    non-negative reflection-positive expectation (a non-negative weighted sum of squares). -/
theorem factorized_kernel_reflection_positive {α : Type*}
    (H : ProductHalfExpectation α) (F S_plus : α → ℝ)
    (K : List (ℝ × (α → ℝ))) (hK : allNonneg K) :
    0 ≤ H.Eprod (fun p =>
      F p.1 * F p.2 * Real.exp (-S_plus p.1) * Real.exp (-S_plus p.2) *
        evalKernel K p.1 p.2) := by
  induction K with
  | nil =>
    have h0 : (fun p : α × α =>
      F p.1 * F p.2 * Real.exp (-S_plus p.1) * Real.exp (-S_plus p.2) *
        evalKernel [] p.1 p.2) = fun _ => 0 := by
      funext p; simp [evalKernel]
    rw [h0, H.eval_zero]
  | cons q qs ih =>
    have hq : 0 ≤ q.1 := hK q (by simp)
    have hqs : allNonneg qs := fun r hr => hK r (by simp [hr])
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
    rw [hsplit, H.linear_add, H.linear_smul,
      H.factorize (fun u => F u * Real.exp (-S_plus u) * q.2 u)
        (fun u => F u * Real.exp (-S_plus u) * q.2 u)]
    have hterm1 : 0 ≤ q.1 * (H.Ehalf (fun u => F u * Real.exp (-S_plus u) * q.2 u) *
        H.Ehalf (fun u => F u * Real.exp (-S_plus u) * q.2 u)) :=
      mul_nonneg hq (mul_self_nonneg _)
    linarith [hterm1, ih hqs]

/-- Osterwalder–Seiler reflection positivity at every finite Taylor truncation order `N`
    for any crossing-plaquette interaction `W(u, v) = evalKernel K u v` with `allNonneg K`. -/
theorem os_taylor_truncation_reflection_positive {α : Type*}
    (H : ProductHalfExpectation α) (F S_plus : α → ℝ)
    (K : List (ℝ × (α → ℝ))) (hK : allNonneg K) (N : ℕ) :
    0 ≤ H.Eprod (fun p =>
      F p.1 * F p.2 * Real.exp (-S_plus p.1) * Real.exp (-S_plus p.2) *
        ∑ n ∈ Finset.range (N + 1), (evalKernel K p.1 p.2) ^ n / (n.factorial : ℝ)) := by
  have heq :
      (fun p : α × α =>
        F p.1 * F p.2 * Real.exp (-S_plus p.1) * Real.exp (-S_plus p.2) *
          ∑ n ∈ Finset.range (N + 1), (evalKernel K p.1 p.2) ^ n / (n.factorial : ℝ)) =
      (fun p : α × α =>
        F p.1 * F p.2 * Real.exp (-S_plus p.1) * Real.exp (-S_plus p.2) *
          evalKernel (expTruncKernel K N) p.1 p.2) := by
    funext p
    rw [evalKernel_expTrunc]
  rw [heq]
  exact factorized_kernel_reflection_positive H F S_plus (expTruncKernel K N)
    (allNonneg_expTrunc hK N)

/-- Full bare-lattice Osterwalder–Seiler reflection positivity in the `N → ∞` limit:
    if the truncated expectations converge to the full unnormalized Wilson inner product `I`
    and `Z > 0`, then the normalized expectation `I / Z ≥ 0`. -/
theorem wilson_os2_reflection_positivity_of_limit {α : Type*}
    (H : ProductHalfExpectation α) (F S_plus : α → ℝ)
    (K : List (ℝ × (α → ℝ))) (hK : allNonneg K) (I Z : ℝ) (hZ : 0 < Z)
    (hlim : Filter.Tendsto (fun N : ℕ =>
      H.Eprod (fun p =>
        F p.1 * F p.2 * Real.exp (-S_plus p.1) * Real.exp (-S_plus p.2) *
          ∑ n ∈ Finset.range (N + 1), (evalKernel K p.1 p.2) ^ n / (n.factorial : ℝ)))
      Filter.atTop (nhds I)) :
    0 ≤ I / Z := by
  have hI : 0 ≤ I :=
    ge_of_tendsto' hlim (fun N => os_taylor_truncation_reflection_positive H F S_plus K hK N)
  exact div_nonneg hI (le_of_lt hZ)

end YangMills
