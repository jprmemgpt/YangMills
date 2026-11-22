import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.Linarith

/-!
# Module 6: GaugeLattice (Lean 4 + Mathlib4)
Formalizes the foundational 4D hypercubic lattice gauge theory structures and exact identities:
1. 4D lattice sites, commuting unit shifts, gauge fields U_μ(x) ∈ G, and local gauge action.
2. Plaquette holonomies U_{μν}(x) and exact local gauge covariance:
   U_{μν}(g · U)(x) = g(x) U_{μν}(U)(x) g(x)⁻¹.
3. Exact local gauge invariance of the Wilson plaquette action S_p(U) and compact fiber
   exhaustion 0 ≤ 1 - (1/d_ρ) Re Tr_ρ(U_p) ≤ 2 (Invariant G1).
4. Exact non-Abelian discrete Bianchi identity around every 3-cube:
   P₁ · Q₂⁻¹ · P₂ · Q₃⁻¹ · P₃ · Q₁⁻¹ = 1 for any group G (SU(2), SU(3), etc.).
5. Exact hyperplane time-reflection involution θ² = id (OS2 geometric foundation).
-/

namespace YangMills

/-- 4D hypercubic lattice site x ∈ ℤ⁴. -/
abbrev Site := Fin 4 → Int

/-- Unit lattice shift x ↦ x + e_μ along direction μ ∈ {0, 1, 2, 3}. -/
def step (x : Site) (μ : Fin 4) : Site :=
  fun α => if α = μ then x α + 1 else x α

/-- Lattice shifts commute in every pair of directions. -/
theorem step_comm (x : Site) (μ ν : Fin 4) :
    step (step x μ) ν = step (step x ν) μ := by
  funext α
  unfold step
  by_cases h1 : α = μ <;> by_cases h2 : α = ν <;> simp [h1, h2] <;> split_ifs <;> rfl

/-! ## 1. Gauge Fields, Local Gauge Action, and Plaquette Holonomies -/

/-- A lattice gauge configuration assigns a group element U_μ(x) ∈ G to each oriented link. -/
abbrev GaugeField (G : Type*) := Site → Fin 4 → G

/-- A local gauge transformation assigns g(x) ∈ G to each lattice site. -/
abbrev GaugeTransform (G : Type*) := Site → G

/-- Local gauge transformation: U_μ(x) ↦ g(x) U_μ(x) g(x + e_μ)⁻¹. -/
def gaugeAct {G : Type*} [Group G] (g : GaugeTransform G) (U : GaugeField G) : GaugeField G :=
  fun x μ => g x * U x μ * (g (step x μ))⁻¹

/-- The trivial gauge transformation acts as the identity. -/
theorem gaugeAct_one {G : Type*} [Group G] (U : GaugeField G) :
    gaugeAct (fun _ => (1 : G)) U = U := by
  funext x μ
  simp [gaugeAct]

/-- Local gauge transformations form a left group action on gauge configurations. -/
theorem gaugeAct_mul {G : Type*} [Group G] (g1 g2 : GaugeTransform G) (U : GaugeField G) :
    gaugeAct (fun x => g1 x * g2 x) U = gaugeAct g1 (gaugeAct g2 U) := by
  funext x μ
  simp [gaugeAct, mul_assoc]

/-- Oriented plaquette holonomy U_{μν}(x) = U_μ(x) U_ν(x+e_μ) U_μ(x+e_ν)⁻¹ U_ν(x)⁻¹. -/
def plaquette {G : Type*} [Group G] (U : GaugeField G) (x : Site) (μ ν : Fin 4) : G :=
  U x μ * U (step x μ) ν * (U (step x ν) μ)⁻¹ * (U x ν)⁻¹

/-- Exact local gauge covariance of the plaquette holonomy in any group G. -/
theorem plaquette_gauge_covariant {G : Type*} [Group G]
    (g : GaugeTransform G) (U : GaugeField G) (x : Site) (μ ν : Fin 4) :
    plaquette (gaugeAct g U) x μ ν = g x * plaquette U x μ ν * (g x)⁻¹ := by
  simp [plaquette, gaugeAct, step_comm x ν μ, mul_assoc]

/-! ## 2. Wilson Plaquette Action & Compact Fiber Exhaustion (Invariant G1) -/

/-- Normalized real trace character χ(u) = (1 / d_ρ) Re Tr_ρ(u) of a unitary representation. -/
structure UnitaryTrace (G : Type*) [Group G] where
  reTrNorm : G → ℝ
  conj_inv : ∀ g u : G, reTrNorm (g * u * g⁻¹) = reTrNorm u
  le_one : ∀ u : G, reTrNorm u ≤ 1
  neg_one_le : ∀ u : G, -1 ≤ reTrNorm u
  at_one : reTrNorm 1 = 1

/-- Wilson plaquette action density S_p(U) = β (1 - (1/d_ρ) Re Tr_ρ(U_p)). -/
def wilsonPlaquetteAction {G : Type*} [Group G]
    (χ : UnitaryTrace G) (beta : ℝ) (U : GaugeField G) (x : Site) (μ ν : Fin 4) : ℝ :=
  beta * (1 - χ.reTrNorm (plaquette U x μ ν))

/-- Exact local gauge invariance of the Wilson plaquette action for every gauge group G. -/
theorem wilsonPlaquetteAction_gauge_invariant {G : Type*} [Group G]
    (χ : UnitaryTrace G) (beta : ℝ) (g : GaugeTransform G) (U : GaugeField G)
    (x : Site) (μ ν : Fin 4) :
    wilsonPlaquetteAction χ beta (gaugeAct g U) x μ ν =
      wilsonPlaquetteAction χ beta U x μ ν := by
  unfold wilsonPlaquetteAction
  rw [plaquette_gauge_covariant, χ.conj_inv]

/-- Invariant G1 (Compact Fiber Exhaustion): 0 ≤ 1 - (1/d_ρ) Re Tr_ρ(u) ≤ 2 everywhere. -/
theorem compact_fiber_exhaustion {G : Type*} [Group G] (χ : UnitaryTrace G) (u : G) :
    0 ≤ 1 - χ.reTrNorm u ∧ 1 - χ.reTrNorm u ≤ 2 := by
  have h1 := χ.le_one u
  have h2 := χ.neg_one_le u
  constructor <;> linarith

/-- Uniform pointwise bounds on the Wilson plaquette action: 0 ≤ S_p(U) ≤ 2β for β ≥ 0. -/
theorem wilsonPlaquetteAction_bounds {G : Type*} [Group G]
    (χ : UnitaryTrace G) (beta : ℝ) (hbeta : 0 ≤ beta)
    (U : GaugeField G) (x : Site) (μ ν : Fin 4) :
    0 ≤ wilsonPlaquetteAction χ beta U x μ ν ∧
      wilsonPlaquetteAction χ beta U x μ ν ≤ 2 * beta := by
  unfold wilsonPlaquetteAction
  obtain ⟨h0, h2⟩ := compact_fiber_exhaustion χ (plaquette U x μ ν)
  constructor
  · exact mul_nonneg hbeta h0
  · have hmul := mul_le_mul_of_nonneg_left h2 hbeta
    linarith

/-! ## 3. Exact Non-Abelian Discrete Bianchi Identity (Theorem II Foundation) -/

/-- Exact non-Abelian discrete Bianchi identity around every 3-cube (x; μ, ν, ρ):
    the ordered product of the 6 parallel-transported boundary plaquettes equals 1 ∈ G. -/
theorem discrete_bianchi_identity {G : Type*} [Group G]
    (U : GaugeField G) (x : Site) (μ ν ρ : Fin 4) :
    let P1 := plaquette U x μ ν
    let P2 := plaquette U x ν ρ
    let P3 := plaquette U x ρ μ
    let Q1 := U x μ * plaquette U (step x μ) ν ρ * (U x μ)⁻¹
    let Q2 := U x ν * plaquette U (step x ν) ρ μ * (U x ν)⁻¹
    let Q3 := U x ρ * plaquette U (step x ρ) μ ν * (U x ρ)⁻¹
    P1 * Q2⁻¹ * P2 * Q3⁻¹ * P3 * Q1⁻¹ = 1 := by
  dsimp only
  simp [plaquette, step_comm x ν μ, step_comm x ρ ν, step_comm x ρ μ, mul_assoc]

/-! ## 4. Hyperplane Time-Reflection Involution (OS2 Geometric Foundation) -/

/-- Hyperplane time-reflection θ(x₀, x₁, x₂, x₃) = (-x₀, x₁, x₂, x₃). -/
def timeReflect (x : Site) : Site :=
  fun α => if α = 0 then -(x 0) else x α

/-- Time-reflection is an exact involution: θ(θ(x)) = x. -/
theorem timeReflect_involutive (x : Site) : timeReflect (timeReflect x) = x := by
  funext α
  unfold timeReflect
  by_cases h : α = 0 <;> simp [h]

end YangMills
