import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import YangMills.GaugeLattice

/-!
# Module 9: SU2Seat (Lean 4 + Mathlib4)
Concrete non-Abelian Lie group instantiation of SU(2) ≅ S³ (unit quaternions):
1. Exact non-Abelian group structure on SU(2) via Euler's four-square identity.
2. Explicit witness that SU(2) is non-Abelian (i · j ≠ j · i).
3. Concrete `UnitaryTrace SU2` with (1/2) Re Tr(U) = a ∈ [-1, 1] and exact conjugation invariance.
4. Direct specialization of `GaugeLattice` (Wilson gauge invariance, compact fiber bounds,
   and the exact non-Abelian 3-cube discrete Bianchi identity) to SU(2).
-/

namespace YangMills

/-- Concrete SU(2) ≅ S³ represented by unit quaternions (a, b, c, d) ∈ ℝ⁴ with a²+b²+c²+d² = 1. -/
@[ext]
structure SU2 where
  a : ℝ
  b : ℝ
  c : ℝ
  d : ℝ
  norm_sq : a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2 = 1

namespace SU2

/-- Identity element 1 ∈ SU(2). -/
def one : SU2 where
  a := 1
  b := 0
  c := 0
  d := 0
  norm_sq := by norm_num

/-- Non-Abelian group multiplication in SU(2) (Hamilton quaternion product). -/
def mul (x y : SU2) : SU2 where
  a := x.a * y.a - x.b * y.b - x.c * y.c - x.d * y.d
  b := x.a * y.b + x.b * y.a + x.c * y.d - x.d * y.c
  c := x.a * y.c - x.b * y.d + x.c * y.a + x.d * y.b
  d := x.a * y.d + x.b * y.c - x.c * y.b + x.d * y.a
  norm_sq := by
    calc
      (x.a * y.a - x.b * y.b - x.c * y.c - x.d * y.d) ^ 2 +
      (x.a * y.b + x.b * y.a + x.c * y.d - x.d * y.c) ^ 2 +
      (x.a * y.c - x.b * y.d + x.c * y.a + x.d * y.b) ^ 2 +
      (x.a * y.d + x.b * y.c - x.c * y.b + x.d * y.a) ^ 2
        = (x.a ^ 2 + x.b ^ 2 + x.c ^ 2 + x.d ^ 2) *
          (y.a ^ 2 + y.b ^ 2 + y.c ^ 2 + y.d ^ 2) := by ring
      _ = 1 := by rw [x.norm_sq, y.norm_sq]; norm_num

/-- Inverse element u⁻¹ = u† in SU(2). -/
def inv (x : SU2) : SU2 where
  a := x.a
  b := -x.b
  c := -x.c
  d := -x.d
  norm_sq := by
    rw [neg_sq, neg_sq, neg_sq]
    exact x.norm_sq

instance : Group SU2 where
  mul := SU2.mul
  one := SU2.one
  inv := SU2.inv
  mul_assoc := by
    intro x y z
    change SU2.mul (SU2.mul x y) z = SU2.mul x (SU2.mul y z)
    ext <;> (unfold SU2.mul; ring)
  one_mul := by
    intro x
    change SU2.mul SU2.one x = x
    ext <;> (unfold SU2.mul SU2.one; ring)
  mul_one := by
    intro x
    change SU2.mul x SU2.one = x
    ext <;> (unfold SU2.mul SU2.one; ring)
  inv_mul_cancel := by
    intro x
    ext
    · change x.a * x.a - -x.b * x.b - -x.c * x.c - -x.d * x.d = 1
      calc
        x.a * x.a - -x.b * x.b - -x.c * x.c - -x.d * x.d
          = x.a ^ 2 + x.b ^ 2 + x.c ^ 2 + x.d ^ 2 := by ring
        _ = 1 := x.norm_sq
    · change x.a * x.b + -x.b * x.a + -x.c * x.d - -x.d * x.c = 0; ring
    · change x.a * x.c - -x.b * x.d + -x.c * x.a + -x.d * x.b = 0; ring
    · change x.a * x.d + -x.b * x.c - -x.c * x.b + -x.d * x.a = 0; ring

/-- Concrete non-Abelian witness in SU(2): i · j ≠ j · i. -/
theorem nonabelian : ∃ x y : SU2, x * y ≠ y * x := by
  let qi : SU2 := ⟨0, 1, 0, 0, by norm_num⟩
  let qj : SU2 := ⟨0, 0, 1, 0, by norm_num⟩
  refine ⟨qi, qj, ?_⟩
  intro h
  have hd : (qi * qj).d = (qj * qi).d := congrArg SU2.d h
  change (0 : ℝ) * 0 + 1 * 1 - 0 * 0 + 0 * 0 = 0 * 0 + 0 * 0 - 1 * 1 + 0 * 0 at hd
  norm_num at hd

end SU2

/-- Concrete normalized trace character (1/2) Re Tr(U) = U.a on SU(2). -/
def su2Trace : UnitaryTrace SU2 where
  reTrNorm := fun u => u.a
  conj_inv := by
    intro g u
    have hnorm : g.a ^ 2 + g.b ^ 2 + g.c ^ 2 + g.d ^ 2 = 1 := g.norm_sq
    calc
      (g * u * g⁻¹).a = u.a * (g.a ^ 2 + g.b ^ 2 + g.c ^ 2 + g.d ^ 2) := by
        change (SU2.mul (SU2.mul g u) (SU2.inv g)).a = _
        unfold SU2.mul SU2.inv
        ring
      _ = u.a := by rw [hnorm, mul_one]
  le_one := by
    intro u
    have ha2 : u.a ^ 2 ≤ 1 := by
      linarith [u.norm_sq, sq_nonneg u.b, sq_nonneg u.c, sq_nonneg u.d]
    nlinarith
  neg_one_le := by
    intro u
    have ha2 : u.a ^ 2 ≤ 1 := by
      linarith [u.norm_sq, sq_nonneg u.b, sq_nonneg u.c, sq_nonneg u.d]
    nlinarith
  at_one := rfl

/-! ## Concrete SU(2) Specializations of Module 6 (`GaugeLattice`) -/

/-- Exact local gauge invariance of the concrete 4D SU(2) Wilson plaquette action. -/
theorem su2_wilson_gauge_invariant
    (beta : ℝ) (g : GaugeTransform SU2) (U : GaugeField SU2) (x : Site) (μ ν : Fin 4) :
    wilsonPlaquetteAction su2Trace beta (gaugeAct g U) x μ ν =
      wilsonPlaquetteAction su2Trace beta U x μ ν :=
  wilsonPlaquetteAction_gauge_invariant su2Trace beta g U x μ ν

/-- Compact fiber exhaustion bounds 0 ≤ S_p(U) ≤ 2β on concrete 4D SU(2). -/
theorem su2_wilson_fiber_bounds
    (beta : ℝ) (hbeta : 0 ≤ beta) (U : GaugeField SU2) (x : Site) (μ ν : Fin 4) :
    0 ≤ wilsonPlaquetteAction su2Trace beta U x μ ν ∧
      wilsonPlaquetteAction su2Trace beta U x μ ν ≤ 2 * beta :=
  wilsonPlaquetteAction_bounds su2Trace beta hbeta U x μ ν

/-- Exact non-Abelian 3-cube discrete Bianchi identity on concrete 4D SU(2). -/
theorem su2_discrete_bianchi (U : GaugeField SU2) (x : Site) (μ ν ρ : Fin 4) :
    let P1 := plaquette U x μ ν
    let P2 := plaquette U x ν ρ
    let P3 := plaquette U x ρ μ
    let Q1 := U x μ * plaquette U (step x μ) ν ρ * (U x μ)⁻¹
    let Q2 := U x ν * plaquette U (step x ν) ρ μ * (U x ν)⁻¹
    let Q3 := U x ρ * plaquette U (step x ρ) μ ν * (U x ρ)⁻¹
    P1 * Q2⁻¹ * P2 * Q3⁻¹ * P3 * Q1⁻¹ = 1 :=
  discrete_bianchi_identity U x μ ν ρ

end YangMills
