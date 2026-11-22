import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import YangMills.GaugeLattice

/-!
# Module 10: SU3Seat (Lean 4 + Mathlib4)
Constructs the concrete non-Abelian gauge group SU(3) (3×3 complex special unitary matrices
with U†U = UU† = I and det U = 1) and instantiates the 4D lattice gauge framework from
`GaugeLattice.lean`:
1. Exact 3×3 complex matrix algebra (`matMul`, `matOne`, `matDag`, `det3`, `tr3`) with
   associativity, identities, multiplicativity of det, and cyclicity of trace.
2. Concrete `Group SU3` instance and explicit non-Abelian witness `SU3.nonabelian`.
3. Concrete normalized fundamental trace character `su3Trace : UnitaryTrace SU3`
   with `(1/3) Re Tr(U) ∈ [-1, 1]` and exact conjugation invariance.
4. Concrete SU(3) specializations of local Wilson gauge invariance, compact fiber exhaustion
   (`0 ≤ S_p ≤ 2β`), and the 3-cube non-Abelian discrete Bianchi identity.
-/

namespace YangMills

/-- 3×3 complex matrix represented as a function on `Fin 3 × Fin 3`. -/
abbrev Mat3C := Fin 3 → Fin 3 → ℂ

/-- Explicit complex conjugation z ↦ Re(z) - i Im(z). -/
def cconj (z : ℂ) : ℂ := ⟨z.re, -z.im⟩

/-- Explicit 3×3 complex matrix multiplication. -/
def matMul (A B : Mat3C) : Mat3C :=
  fun i j => A i 0 * B 0 j + A i 1 * B 1 j + A i 2 * B 2 j

/-- 3×3 complex identity matrix. -/
def matOne : Mat3C :=
  fun i j => if i = j then 1 else 0

/-- 3×3 Hermitian conjugate (conjugate transpose) A†. -/
def matDag (A : Mat3C) : Mat3C :=
  fun i j => cconj (A j i)

/-- Explicit 3×3 complex trace Tr(A). -/
def tr3 (A : Mat3C) : ℂ :=
  A 0 0 + A 1 1 + A 2 2

/-- Explicit 3×3 complex determinant det(A). -/
def det3 (A : Mat3C) : ℂ :=
  A 0 0 * (A 1 1 * A 2 2 - A 1 2 * A 2 1) -
  A 0 1 * (A 1 0 * A 2 2 - A 1 2 * A 2 0) +
  A 0 2 * (A 1 0 * A 2 1 - A 1 1 * A 2 0)

theorem fin3_cases {P : Fin 3 → Prop} (h0 : P 0) (h1 : P 1) (h2 : P 2) (i : Fin 3) : P i := by
  match i with
  | ⟨0, _⟩ => exact h0
  | ⟨1, _⟩ => exact h1
  | ⟨2, _⟩ => exact h2

theorem matMul_assoc (A B C : Mat3C) :
    matMul (matMul A B) C = matMul A (matMul B C) := by
  funext i j
  unfold matMul
  ring

theorem matOne_mul (A : Mat3C) : matMul matOne A = A := by
  funext i j
  revert i
  refine fin3_cases ?_ ?_ ?_ <;> (unfold matMul matOne; simp)

theorem matMul_one (A : Mat3C) : matMul A matOne = A := by
  funext i j
  revert j
  refine fin3_cases ?_ ?_ ?_ <;> (unfold matMul matOne; simp)

theorem matDag_one : matDag matOne = matOne := by
  funext i j
  revert i j
  refine fin3_cases ?_ ?_ ?_ <;> refine fin3_cases ?_ ?_ ?_ <;>
    (apply Complex.ext <;> simp [matDag, matOne, cconj])

theorem matDag_dag (A : Mat3C) : matDag (matDag A) = A := by
  funext i j
  apply Complex.ext <;> simp [matDag, cconj]

theorem matDag_mul (A B : Mat3C) :
    matDag (matMul A B) = matMul (matDag B) (matDag A) := by
  funext i j
  apply Complex.ext <;>
    (simp only [matDag, matMul, cconj, Complex.add_re, Complex.add_im,
      Complex.mul_re, Complex.mul_im]; ring)

theorem det3_one : det3 matOne = 1 := by
  unfold det3 matOne
  simp

theorem det3_mul (A B : Mat3C) : det3 (matMul A B) = det3 A * det3 B := by
  unfold det3 matMul
  ring

theorem det3_dag (A : Mat3C) : det3 (matDag A) = cconj (det3 A) := by
  apply Complex.ext <;>
    (simp only [det3, matDag, cconj, Complex.add_re, Complex.add_im,
      Complex.sub_re, Complex.sub_im, Complex.mul_re, Complex.mul_im]; ring)

theorem tr3_mul_comm (A B : Mat3C) : tr3 (matMul A B) = tr3 (matMul B A) := by
  unfold tr3 matMul
  ring

/-- Concrete SU(3) group: 3×3 complex matrices with U†U = UU† = I and det U = 1. -/
@[ext]
structure SU3 where
  mat : Mat3C
  unitary_left : matMul (matDag mat) mat = matOne
  unitary_right : matMul mat (matDag mat) = matOne
  det_eq_one : det3 mat = 1

namespace SU3

/-- Identity element I ∈ SU(3). -/
def one : SU3 where
  mat := matOne
  unitary_left := by rw [matDag_one, matOne_mul]
  unitary_right := by rw [matDag_one, matOne_mul]
  det_eq_one := det3_one

/-- Matrix product U · V in SU(3). -/
def mul (U V : SU3) : SU3 where
  mat := matMul U.mat V.mat
  unitary_left := by
    rw [matDag_mul, matMul_assoc, ← matMul_assoc (matDag U.mat) U.mat V.mat,
      U.unitary_left, matOne_mul, V.unitary_left]
  unitary_right := by
    rw [matDag_mul, matMul_assoc, ← matMul_assoc V.mat (matDag V.mat) (matDag U.mat),
      V.unitary_right, matOne_mul, U.unitary_right]
  det_eq_one := by
    rw [det3_mul, U.det_eq_one, V.det_eq_one, mul_one]

/-- Inverse element U⁻¹ = U† in SU(3). -/
def inv (U : SU3) : SU3 where
  mat := matDag U.mat
  unitary_left := by rw [matDag_dag]; exact U.unitary_right
  unitary_right := by rw [matDag_dag]; exact U.unitary_left
  det_eq_one := by
    rw [det3_dag, U.det_eq_one]
    apply Complex.ext <;> simp [cconj]

instance : Group SU3 where
  mul := SU3.mul
  one := SU3.one
  inv := SU3.inv
  mul_assoc := by
    intro x y z
    change SU3.mul (SU3.mul x y) z = SU3.mul x (SU3.mul y z)
    apply SU3.ext
    exact matMul_assoc x.mat y.mat z.mat
  one_mul := by
    intro x
    change SU3.mul SU3.one x = x
    apply SU3.ext
    exact matOne_mul x.mat
  mul_one := by
    intro x
    change SU3.mul x SU3.one = x
    apply SU3.ext
    exact matMul_one x.mat
  inv_mul_cancel := by
    intro x
    change SU3.mul (SU3.inv x) x = SU3.one
    apply SU3.ext
    exact x.unitary_left

/-- Embedded SU(2) generator iσ₁ ⊕ 1 inside SU(3). -/
def u1Mat (i j : Fin 3) : ℂ :=
  if i = 0 ∧ j = 1 then Complex.I
  else if i = 1 ∧ j = 0 then Complex.I
  else if i = 2 ∧ j = 2 then 1
  else 0

/-- Embedded SU(2) generator iσ₂ ⊕ 1 inside SU(3). -/
def u2Mat (i j : Fin 3) : ℂ :=
  if i = 0 ∧ j = 1 then 1
  else if i = 1 ∧ j = 0 then -1
  else if i = 2 ∧ j = 2 then 1
  else 0

def u1 : SU3 where
  mat := u1Mat
  unitary_left := by
    funext i j
    revert i j
    refine fin3_cases ?_ ?_ ?_ <;> refine fin3_cases ?_ ?_ ?_ <;>
      (apply Complex.ext <;> simp [matMul, matDag, matOne, u1Mat, cconj])
  unitary_right := by
    funext i j
    revert i j
    refine fin3_cases ?_ ?_ ?_ <;> refine fin3_cases ?_ ?_ ?_ <;>
      (apply Complex.ext <;> simp [matMul, matDag, matOne, u1Mat, cconj])
  det_eq_one := by
    apply Complex.ext <;> simp [det3, u1Mat]

def u2 : SU3 where
  mat := u2Mat
  unitary_left := by
    funext i j
    revert i j
    refine fin3_cases ?_ ?_ ?_ <;> refine fin3_cases ?_ ?_ ?_ <;>
      (apply Complex.ext <;> simp [matMul, matDag, matOne, u2Mat, cconj])
  unitary_right := by
    funext i j
    revert i j
    refine fin3_cases ?_ ?_ ?_ <;> refine fin3_cases ?_ ?_ ?_ <;>
      (apply Complex.ext <;> simp [matMul, matDag, matOne, u2Mat, cconj])
  det_eq_one := by
    apply Complex.ext <;> simp [det3, u2Mat]

/-- Concrete non-Abelian witness in SU(3): u1 · u2 ≠ u2 · u1. -/
theorem nonabelian : ∃ U V : SU3, U * V ≠ V * U := by
  refine ⟨u1, u2, ?_⟩
  intro h
  have him : ((u1 * u2).mat 0 0).im = ((u2 * u1).mat 0 0).im :=
    congrArg (fun x => (x.mat 0 0).im) h
  change ((matMul u1Mat u2Mat) 0 0).im = ((matMul u2Mat u1Mat) 0 0).im at him
  have h1 : ((matMul u1Mat u2Mat) 0 0).im = -1 := by simp [matMul, u1Mat, u2Mat]
  have h2 : ((matMul u2Mat u1Mat) 0 0).im = 1 := by simp [matMul, u1Mat, u2Mat]
  linarith

/-- Every diagonal entry of U ∈ SU(3) satisfies -1 ≤ Re(U_jj) ≤ 1. -/
theorem diag_re_bounds (U : SU3) (j : Fin 3) :
    -1 ≤ (U.mat j j).re ∧ (U.mat j j).re ≤ 1 := by
  have hcol : (matMul (matDag U.mat) U.mat j j).re = 1 := by
    have h := congrArg Complex.re (congrFun (congrFun U.unitary_left j) j)
    simpa [matOne] using h
  have hsum :
      (U.mat 0 j).re ^ 2 + (U.mat 0 j).im ^ 2 +
      (U.mat 1 j).re ^ 2 + (U.mat 1 j).im ^ 2 +
      (U.mat 2 j).re ^ 2 + (U.mat 2 j).im ^ 2 = 1 := by
    have hre :
        (matMul (matDag U.mat) U.mat j j).re =
        (U.mat 0 j).re ^ 2 + (U.mat 0 j).im ^ 2 +
        (U.mat 1 j).re ^ 2 + (U.mat 1 j).im ^ 2 +
        (U.mat 2 j).re ^ 2 + (U.mat 2 j).im ^ 2 := by
      simp only [matMul, matDag, cconj, Complex.add_re, Complex.mul_re]
      ring
    linarith
  have h0r := sq_nonneg (U.mat 0 j).re
  have h0i := sq_nonneg (U.mat 0 j).im
  have h1r := sq_nonneg (U.mat 1 j).re
  have h1i := sq_nonneg (U.mat 1 j).im
  have h2r := sq_nonneg (U.mat 2 j).re
  have h2i := sq_nonneg (U.mat 2 j).im
  have hj : j = 0 ∨ j = 1 ∨ j = 2 := by
    match j with
    | ⟨0, _⟩ => left; rfl
    | ⟨1, _⟩ => right; left; rfl
    | ⟨2, _⟩ => right; right; rfl
  have hsq : (U.mat j j).re ^ 2 ≤ 1 := by
    rcases hj with rfl | rfl | rfl <;> linarith
  constructor <;> nlinarith

end SU3

/-- Concrete normalized fundamental trace character (1/3) Re Tr(U) on SU(3). -/
noncomputable def su3Trace : UnitaryTrace SU3 where
  reTrNorm := fun U => (tr3 U.mat).re / 3
  conj_inv := by
    intro G U
    have htr : tr3 ((G * U * G⁻¹).mat) = tr3 U.mat := by
      change tr3 (matMul (matMul G.mat U.mat) (matDag G.mat)) = tr3 U.mat
      rw [tr3_mul_comm, ← matMul_assoc, G.unitary_left, matOne_mul]
    rw [htr]
  le_one := by
    intro U
    have h0 := (SU3.diag_re_bounds U 0).2
    have h1 := (SU3.diag_re_bounds U 1).2
    have h2 := (SU3.diag_re_bounds U 2).2
    simp only [tr3, Complex.add_re]
    linarith
  neg_one_le := by
    intro U
    have h0 := (SU3.diag_re_bounds U 0).1
    have h1 := (SU3.diag_re_bounds U 1).1
    have h2 := (SU3.diag_re_bounds U 2).1
    simp only [tr3, Complex.add_re]
    linarith
  at_one := by
    change (tr3 matOne).re / 3 = 1
    simp only [tr3, matOne, Complex.add_re]
    norm_num

/-- Concrete SU(3) Wilson plaquette action is exactly locally gauge invariant. -/
theorem su3_wilson_gauge_invariant (beta : ℝ) (g : GaugeTransform SU3) (U : GaugeField SU3)
    (x : Site) (μ ν : Fin 4) :
    wilsonPlaquetteAction su3Trace beta (gaugeAct g U) x μ ν =
      wilsonPlaquetteAction su3Trace beta U x μ ν :=
  wilsonPlaquetteAction_gauge_invariant su3Trace beta g U x μ ν

/-- Concrete SU(3) Wilson plaquette action satisfies compact fiber bounds 0 ≤ S_p ≤ 2β. -/
theorem su3_wilson_fiber_bounds (beta : ℝ) (hbeta : 0 ≤ beta) (U : GaugeField SU3)
    (x : Site) (μ ν : Fin 4) :
    0 ≤ wilsonPlaquetteAction su3Trace beta U x μ ν ∧
      wilsonPlaquetteAction su3Trace beta U x μ ν ≤ 2 * beta :=
  wilsonPlaquetteAction_bounds su3Trace beta hbeta U x μ ν

/-- Concrete SU(3) non-Abelian discrete Bianchi identity around every 3-cube. -/
theorem su3_discrete_bianchi (U : GaugeField SU3) (x : Site) (μ ν ρ : Fin 4) :
    let P1 := plaquette U x μ ν
    let P2 := plaquette U x ν ρ
    let P3 := plaquette U x ρ μ
    let Q1 := U x μ * plaquette U (step x μ) ν ρ * (U x μ)⁻¹
    let Q2 := U x ν * plaquette U (step x ν) ρ μ * (U x ν)⁻¹
    let Q3 := U x ρ * plaquette U (step x ρ) μ ν * (U x ρ)⁻¹
    P1 * Q2⁻¹ * P2 * Q3⁻¹ * P3 * Q1⁻¹ = 1 :=
  discrete_bianchi_identity U x μ ν ρ

end YangMills
