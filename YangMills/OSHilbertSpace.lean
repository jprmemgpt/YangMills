import Mathlib.Analysis.InnerProductSpace.Completion
import YangMills.OSReconstruction
import YangMills.HilbertCompletion
import YangMills.LatticeReflectionPositivity

/-!
# Module 25: OSHilbertSpace (Lean 4 + Mathlib4)
Constructs the concrete physical Osterwalder–Schrader Hilbert space `PhysicalOSHilbertSpace L`
from any linear positive-semidefinite OS2 reflection-positive bilinear space
`L : LinearOSBilinearSpace V`.
-/

namespace YangMills

/-! ## 1. Linear OS2 Bilinear Space & Concrete Constructor from Reflection Positivity -/

/-- A real vector space `V` of positive-time observables equipped with a symmetric,
    bilinear, reflection-positive form `B : V → V → ℝ`. -/
structure LinearOSBilinearSpace (V : Type*) [AddCommGroup V] [Module ℝ V] where
  B : V → V → ℝ
  symm : ∀ x y, B x y = B y x
  add_left : ∀ x y z, B (x + y) z = B x z + B y z
  smul_left : ∀ (c : ℝ) x y, B (c • x) y = c * B x y
  pos_semidef : ∀ x, 0 ≤ B x x

namespace LinearOSBilinearSpace

variable {V : Type*} [AddCommGroup V] [Module ℝ V] (L : LinearOSBilinearSpace V)

/-- Forgetful conversion from `LinearOSBilinearSpace V` to `OSBilinearSpace V`. -/
def toOSBilinearSpace : OSBilinearSpace V where
  zero := 0
  add := (· + ·)
  neg := (- ·)
  smul := (· • ·)
  B := L.B
  symm := L.symm
  add_left := L.add_left
  neg_left := fun x y => by
    have h1 : (-1 : ℝ) • x = -x := neg_one_smul ℝ x
    rw [← h1, L.smul_left]
    ring
  smul_left := L.smul_left
  zero_left := fun y => by
    have h0 : (0 : ℝ) • (0 : V) = 0 := zero_smul ℝ 0
    have h1 := L.smul_left 0 0 y
    rw [h0] at h1
    linarith
  pos_semidef := L.pos_semidef

/-- Construct a `LinearOSBilinearSpace` directly from a linear functional `E : V → ℝ`,
    a multiplication `mul : V → V → V`, and a time-reflection involution `θ : V → V`
    satisfying OS2 reflection positivity `0 ≤ E (mul (θ x) x)`. -/
def ofReflectionFunctional
    (E : V → ℝ) (mul : V → V → V) (θ : V → V)
    (E_add : ∀ a b, E (a + b) = E a + E b)
    (E_smul : ∀ (c : ℝ) a, E (c • a) = c * E a)
    (θ_add : ∀ x y, θ (x + y) = θ x + θ y)
    (θ_smul : ∀ (c : ℝ) x, θ (c • x) = c • θ x)
    (mul_add_left : ∀ x y z, mul (x + y) z = mul x z + mul y z)
    (mul_smul_left : ∀ (c : ℝ) x y, mul (c • x) y = c • mul x y)
    (os_symm : ∀ x y, E (mul (θ x) y) = E (mul (θ y) x))
    (os_rp : ∀ x, 0 ≤ E (mul (θ x) x)) :
    LinearOSBilinearSpace V where
  B x y := E (mul (θ x) y)
  symm := os_symm
  add_left x y z := by
    rw [θ_add, mul_add_left, E_add]
  smul_left c x y := by
    rw [θ_smul, mul_smul_left, E_smul]
  pos_semidef := os_rp

end LinearOSBilinearSpace

/-! ## 2. Pre-Hilbert Space Structure on `LinearOSQuotient` -/

section QuotientPreHilbert

variable {V : Type*} [AddCommGroup V] [Module ℝ V] (L : LinearOSBilinearSpace V)

/-- Abbreviation for the underlying `OSBilinearSpace V`. -/
abbrev osSpace : OSBilinearSpace V := L.toOSBilinearSpace

/-- Abbreviation for the OS quotient `V / 𝒩`. -/
abbrev LinearOSQuotient := OSQuotient (osSpace L)

theorem osEquiv_add {x₁ x₂ y₁ y₂ : V}
    (hx : (osSpace L).osEquiv x₁ x₂) (hy : (osSpace L).osEquiv y₁ y₂) :
    (osSpace L).osEquiv (x₁ + y₁) (x₂ + y₂) := by
  have hx0 := ((osSpace L).os_null_iff_orthog ((osSpace L).sub x₁ x₂)).mp hx
  have hy0 := ((osSpace L).os_null_iff_orthog ((osSpace L).sub y₁ y₂)).mp hy
  unfold OSBilinearSpace.osEquiv OSBilinearSpace.sub at *
  change L.B ((x₁ + y₁) + -(x₂ + y₂)) ((x₁ + y₁) + -(x₂ + y₂)) = 0
  have hsplit : (x₁ + y₁) + -(x₂ + y₂) = (x₁ + -x₂) + (y₁ + -y₂) := by abel
  rw [hsplit, L.add_left]
  have h1 : L.B (x₁ + -x₂) (x₁ + -x₂ + (y₁ + -y₂)) = 0 := hx0 _
  have h2 : L.B (y₁ + -y₂) (x₁ + -x₂ + (y₁ + -y₂)) = 0 := hy0 _
  rw [h1, h2, add_zero]

theorem osEquiv_neg {x₁ x₂ : V} (hx : (osSpace L).osEquiv x₁ x₂) :
    (osSpace L).osEquiv (-x₁) (-x₂) := by
  unfold OSBilinearSpace.osEquiv OSBilinearSpace.sub at *
  change L.B (-x₁ + -(-x₂)) (-x₁ + -(-x₂)) = 0
  have hsplit : -x₁ + -(-x₂) = (-1 : ℝ) • (x₁ + -x₂) := by
    rw [neg_one_smul]; abel
  rw [hsplit, L.smul_left, L.symm, L.smul_left]
  have hbase : L.B (x₁ + -x₂) (x₁ + -x₂) = 0 := hx
  rw [hbase]
  ring

theorem osEquiv_smul (c : ℝ) {x₁ x₂ : V} (hx : (osSpace L).osEquiv x₁ x₂) :
    (osSpace L).osEquiv (c • x₁) (c • x₂) := by
  unfold OSBilinearSpace.osEquiv OSBilinearSpace.sub at *
  change L.B (c • x₁ + -(c • x₂)) (c • x₁ + -(c • x₂)) = 0
  have hsplit : c • x₁ + -(c • x₂) = c • (x₁ + -x₂) := by rw [smul_add, smul_neg]
  rw [hsplit, L.smul_left, L.symm, L.smul_left]
  have hbase : L.B (x₁ + -x₂) (x₁ + -x₂) = 0 := hx
  rw [hbase]
  ring

/-- Addition on `LinearOSQuotient L`. -/
def osQuotientAdd : LinearOSQuotient L → LinearOSQuotient L → LinearOSQuotient L :=
  Quotient.map₂ (· + ·) (fun _ _ hx _ _ hy => osEquiv_add L hx hy)

/-- Zero element on `LinearOSQuotient L`. -/
def osQuotientZero : LinearOSQuotient L :=
  Quotient.mk (osSpace L).osSetoid 0

/-- Negation on `LinearOSQuotient L`. -/
def osQuotientNeg : LinearOSQuotient L → LinearOSQuotient L :=
  Quotient.map (- ·) (fun _ _ hx => osEquiv_neg L hx)

/-- Real scalar multiplication on `LinearOSQuotient L`. -/
def osQuotientSMul (c : ℝ) : LinearOSQuotient L → LinearOSQuotient L :=
  Quotient.map (c • ·) (fun _ _ hx => osEquiv_smul L c hx)

instance instZeroLinearOSQuotient : Zero (LinearOSQuotient L) := ⟨osQuotientZero L⟩
instance instAddLinearOSQuotient : Add (LinearOSQuotient L) := ⟨osQuotientAdd L⟩
instance instNegLinearOSQuotient : Neg (LinearOSQuotient L) := ⟨osQuotientNeg L⟩

instance instAddCommGroupLinearOSQuotient : AddCommGroup (LinearOSQuotient L) where
  add := osQuotientAdd L
  add_assoc a b c := by
    refine Quotient.inductionOn₃ a b c fun x y z => ?_
    exact Quotient.sound (by dsimp only; rw [add_assoc])
  zero := osQuotientZero L
  zero_add a := by
    refine Quotient.inductionOn a fun x => ?_
    exact Quotient.sound (by dsimp only; rw [zero_add])
  add_zero a := by
    refine Quotient.inductionOn a fun x => ?_
    exact Quotient.sound (by dsimp only; rw [add_zero])
  nsmul := nsmulRec
  neg := osQuotientNeg L
  zsmul := zsmulRec
  neg_add_cancel a := by
    refine Quotient.inductionOn a fun x => ?_
    exact Quotient.sound (by dsimp only; rw [neg_add_cancel])
  add_comm a b := by
    refine Quotient.inductionOn₂ a b fun x y => ?_
    exact Quotient.sound (by dsimp only; rw [add_comm])

instance instModuleRealLinearOSQuotient : Module ℝ (LinearOSQuotient L) where
  smul := osQuotientSMul L
  one_smul a := by
    refine Quotient.inductionOn a fun x => ?_
    exact Quotient.sound (by dsimp only; rw [one_smul])
  mul_smul c d a := by
    refine Quotient.inductionOn a fun x => ?_
    exact Quotient.sound (by dsimp only; rw [mul_smul])
  smul_zero c := Quotient.sound (by dsimp only; rw [smul_zero])
  smul_add c a b := by
    refine Quotient.inductionOn₂ a b fun x y => ?_
    exact Quotient.sound (by dsimp only; rw [smul_add])
  add_smul c d a := by
    refine Quotient.inductionOn a fun x => ?_
    exact Quotient.sound (by dsimp only; rw [add_smul])
  zero_smul a := by
    refine Quotient.inductionOn a fun x => ?_
    exact Quotient.sound (by dsimp only; rw [zero_smul])

theorem osInner_add_left (ψ φ χ : LinearOSQuotient L) :
    osInner (osSpace L) (ψ + φ) χ = osInner (osSpace L) ψ χ + osInner (osSpace L) φ χ := by
  refine Quotient.inductionOn₃ ψ φ χ fun x y z => ?_
  exact L.add_left x y z

theorem osInner_smul_left (c : ℝ) (ψ φ : LinearOSQuotient L) :
    osInner (osSpace L) (c • ψ) φ = c * osInner (osSpace L) ψ φ := by
  refine Quotient.inductionOn₂ ψ φ fun x y => ?_
  exact L.smul_left c x y

theorem osInner_cauchy_schwarz (ψ φ : LinearOSQuotient L) :
    osInner (osSpace L) ψ φ ^ 2 ≤ osInner (osSpace L) ψ ψ * osInner (osSpace L) φ φ := by
  refine Quotient.inductionOn₂ ψ φ fun x y => ?_
  exact (osSpace L).os_cauchy_schwarz x y

/-- Genuine real `InnerProductSpace.Core` on the reconstructed OS quotient
    `LinearOSQuotient L`. -/
noncomputable def osQuotientCore : InnerProductSpace.Core ℝ (LinearOSQuotient L) where
  inner ψ φ := osInner (osSpace L) ψ φ
  conj_inner_symm ψ φ := by
    simp [osInner_symm]
  re_inner_nonneg ψ := by
    simpa using osInner_nonneg (osSpace L) ψ
  add_left := osInner_add_left L
  smul_left ψ φ c := by
    simpa using osInner_smul_left L c ψ φ
  definite ψ h := (osInner_eq_zero_iff (osSpace L) ψ).mp h

noncomputable instance instNormedAddCommGroupLinearOSQuotient :
    NormedAddCommGroup (LinearOSQuotient L) :=
  (osQuotientCore L).toNormedAddCommGroup

noncomputable instance instInnerProductSpaceLinearOSQuotient :
    InnerProductSpace ℝ (LinearOSQuotient L) :=
  InnerProductSpace.ofCore (osQuotientCore L).toCore

theorem osQuotient_norm_sq (ψ : LinearOSQuotient L) :
    ‖ψ‖ ^ 2 = osInner (osSpace L) ψ ψ := by
  rw [← real_inner_self_eq_norm_sq]
  rfl

/-! ## 3. Completed Physical Osterwalder–Schrader Hilbert Space -/

/-- The completed physical Osterwalder–Schrader Hilbert space `ℋ_phys = Completion(V / 𝒩)`. -/
abbrev PhysicalOSHilbertSpace := UniformSpace.Completion (LinearOSQuotient L)

/-- `PhysicalOSHilbertSpace L` is a complete Hilbert space. -/
theorem physicalOSHilbert_complete : CompleteSpace (PhysicalOSHilbertSpace L) :=
  hilbertCompletion_complete

/-- Canonical quotient map from observables `V` into `LinearOSQuotient L`. -/
def osMk (x : V) : LinearOSQuotient L :=
  Quotient.mk (osSpace L).osSetoid x

theorem physicalOSHilbert_inner_mk (x y : V) :
    inner ℝ
      ((osMk L x : LinearOSQuotient L) : PhysicalOSHilbertSpace L)
      ((osMk L y : LinearOSQuotient L) : PhysicalOSHilbertSpace L) =
      L.B x y := by
  rw [hilbertCompletion_embed_inner]
  rfl

theorem physicalOSHilbert_norm_sq_mk (x : V) :
    ‖((osMk L x : LinearOSQuotient L) : PhysicalOSHilbertSpace L)‖ ^ 2 =
      L.B x x := by
  rw [hilbertCompletion_embed_isometry, osQuotient_norm_sq]
  rfl

end QuotientPreHilbert

end YangMills
