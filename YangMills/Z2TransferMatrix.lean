import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp

namespace YangMills.DualBook

/-- 2×2 real matrix for exact Z₂ transfer-matrix algebra. -/
structure Mat2 where
  a : ℝ
  b : ℝ
  c : ℝ
  d : ℝ

def Mat2.one : Mat2 := ⟨1, 0, 0, 1⟩

def Mat2.mul (X Y : Mat2) : Mat2 :=
  ⟨X.a * Y.a + X.b * Y.c, X.a * Y.b + X.b * Y.d,
   X.c * Y.a + X.d * Y.c, X.c * Y.b + X.d * Y.d⟩

def Mat2.tr (X : Mat2) : ℝ := X.a + X.d

/-- Symmetric Z₂ transfer matrix `M(x, y) = [[x, y], [y, x]]`. -/
def z2Mat (x y : ℝ) : Mat2 := ⟨x, y, y, x⟩

/-- Ordered product of a finite list of Z₂ transfer matrices. -/
def matProd : List (ℝ × ℝ) → Mat2
  | [] => Mat2.one
  | (x, y) :: rest => Mat2.mul (z2Mat x y) (matProd rest)

/-- Closed-form diagonalization of any finite Z₂ transfer-matrix product. -/
theorem matProd_closed : ∀ L : List (ℝ × ℝ),
    matProd L =
      let p := (L.map (fun q => q.1 + q.2)).prod
      let m := (L.map (fun q => q.1 - q.2)).prod
      ⟨(p + m) / 2, (p - m) / 2, (p - m) / 2, (p + m) / 2⟩
  | [] => by simp only [matProd, Mat2.one, List.map_nil, List.prod_nil]; congr 1 <;> ring
  | (x, y) :: rest => by
      simp only [matProd, List.map_cons, List.prod_cons, matProd_closed rest, z2Mat, Mat2.mul]
      congr 1 <;> ring

/-- Exact Z₂ transfer-matrix trace factorization:
    `Tr(∏ M(x_s, y_s)) = ∏(x_s + y_s) + ∏(x_s - y_s)`. -/
theorem z2_transfer_trace_factorization (L : List (ℝ × ℝ)) :
    (matProd L).tr =
      (L.map (fun q => q.1 + q.2)).prod + (L.map (fun q => q.1 - q.2)).prod := by
  rw [matProd_closed L]; simp only [Mat2.tr]; ring

/-- Kramers-Wannier / tanh inversion map `u ↦ (1 - u) / (1 + u)`. -/
noncomputable def kwDual (u : ℝ) : ℝ := (1 - u) / (1 + u)

/-- Exact tanh inversion involution: `kwDual (kwDual u) = u`. -/
theorem kwDual_involutive (u : ℝ) (h : 1 + u ≠ 0) : kwDual (kwDual u) = u := by
  unfold kwDual
  have h2 : 1 + (1 - u) / (1 + u) ≠ 0 := by
    intro h0
    have h1 := congrArg (· * (1 + u)) h0
    field_simp [h] at h1
    linarith
  field_simp [h, h2]; ring

/-- Exact Kramers-Wannier duality: `sinh(2β) * sinh(2β*) = 1` for `u = exp(-2β)`. -/
theorem kramers_wannier_sinh_duality (u : ℝ)
    (hu0 : u ≠ 0) (hu1 : 1 - u ≠ 0) (hu2 : 1 + u ≠ 0) :
    ((1 - u ^ 2) / (2 * u)) * ((1 - (kwDual u) ^ 2) / (2 * kwDual u)) = 1 := by
  unfold kwDual; field_simp [hu0, hu1, hu2]; ring

#print axioms z2_transfer_trace_factorization
#print axioms kwDual_involutive
#print axioms kramers_wannier_sinh_duality
end YangMills.DualBook
