/-
  PROVENANCE: YangMills.DualBook.ThetaPoissonWindow (R234)
  Built by Gen, Papa's hands only, in the R234 window (Wed 2026-11-25 CT),
  opened at Papa's word ("Try and solve what remains in YangMills 4D Solution
  Blueprint solving in the most irreducible form"), the resume of the
  interrupted R233 session whose math was already green and banked whole.
  The preregistration (order 1103, struck upon at c1617) named this window's
  build: the POISSON LAYER, the one identity both remaining named windows of
  W1 (the Epstein closed-form evaluations, the full Mellin integral) stand
  on — the theta transformation, proved here on the book's own thetaT
  from Mathlib's Poisson-summation-for-the-Gaussian receipt
  (`Real.tsum_exp_neg_mul_int_sq`, David Loeffler's, the vintage's own
  classical analysis; the window assembles existing math in a combination
  the record has not seen — Papa's Katherine Johnson frame, honored as
  method, claimed as nothing more).
  SCOPE: THIS ARITHMETIC only. The window builds:
  (1) THE TRANSFORMATION: thetaT t = (√t)⁻¹ · thetaT (1/t) at every t > 0
      (Poisson summation on the Gaussian; the irreducible core).
  (2) THE DUAL GAIN: the Poisson-sharpened small-t law — for 0 < t ≤ 1
      the theta obeys the exponentially honest bound
      thetaT t ≤ (√t)⁻¹ · (1 + 2q/(1−q)) with q = exp (−π/t), the R233
      blow-up law's exponential correction, exactly what the small-t Mellin
      half's future termwise integration needs.
  (3) THE KERNEL DUALIZATION: the pointwise algebra of the t=1 split —
      t·(thetaT t − 1) = √t·(thetaT (1/t) − 1) + (√t − t), the identity that
      turns the small-t half of the s = 2 kernel into a large-t integral.
  (4) THE SPLIT ITSELF: the full s = 2 Mellin kernel is integrable on
      (0, ∞) and its integral splits at t = 1:
      ∫₀^∞ t(Θ(t)−1) dt = ∫₀^1 t(Θ(t)−1) dt + ∫₁^∞ t(Θ(t)−1) dt.
  NOTHING ELSE IS CLAIMED. The values of the two halves, the E1 layer, the
  Epstein closed-form evaluations, and the full Mellin integral's value
  remain named windows; this module never evaluates an integral, never
  touches a closed form, claims nothing about the physical 4D theory or
  any Clay statement. The bench stays frozen. The Poisson receipt is
  Mathlib's, imported whole, never re-proved; what is new here is the
  assembly on the book's own thetaT — the combination, standing on
  certified stones.
-/
import Mathlib.Analysis.SpecialFunctions.Gaussian.PoissonSummation
import YangMills.DualBook.ThetaIntegrabilityWindow

namespace YangMills.DualBook

open Real Set MeasureTheory Filter

/-! ## The transformation: Poisson summation on the book's own theta -/

set_option maxHeartbeats 400000 in
/-- THE THETA TRANSFORMATION: the Poisson layer, whole. For every `t > 0`
the book's real theta obeys `thetaT t = (√t)⁻¹ · thetaT (1/t)` — the
classical Jacobi inversion, cashed from Mathlib's Poisson-summation receipt
for the Gaussian (`Real.tsum_exp_neg_mul_int_sq`). Both remaining deep
grafts of W1 (the Epstein closed forms, the full Mellin integral) stand on
this one identity. -/
theorem thetaT_transform {t : ℝ} (ht : 0 < t) :
    thetaT t = (Real.sqrt t)⁻¹ * thetaT (1 / t) := by
  have h := Real.tsum_exp_neg_mul_int_sq ht
  simp only [thetaT] at ⊢
  have hsummand : ∀ (n : ℤ),
      Real.exp (-Real.pi / t * (n : ℝ) ^ 2)
        = Real.exp (-Real.pi * (1 / t) * (n : ℝ) ^ 2) := by
    intro n
    congr 1
    rw [div_eq_mul_inv, one_div]
  have h2 : (∑' (n : ℤ), Real.exp (-Real.pi / t * (n : ℝ) ^ 2))
      = ∑' (n : ℤ), Real.exp (-Real.pi * (1 / t) * (n : ℝ) ^ 2) :=
    tsum_congr hsummand
  have hcoef : (1 : ℝ) / t ^ ((1 : ℝ) / 2) = (Real.sqrt t)⁻¹ := by
    rw [Real.sqrt_eq_rpow, one_div]
  rw [h, h2, hcoef]

/-! ## The dual gain: the Poisson-sharpened small-t law -/

/-- THE DUAL GAIN: for `0 < t ≤ 1` the theta obeys the exponentially honest
small-t bound `thetaT t ≤ (√t)⁻¹ · (1 + 2q/(1−q))` with `q = exp (−π/t)`.
This is the R233 blow-up law `thetaT t ≤ 1 + (√t)⁻¹` sharpened by the
transformation: the excess above the honest `t^(−1/2)` mass is not merely
bounded, it is exponentially small in the dual variable `1/t`, exactly the
input the small-t Mellin half's future termwise integration needs. -/
theorem thetaT_dual_gain {t : ℝ} (ht : 0 < t) (ht1 : t ≤ 1) :
    thetaT t ≤ (Real.sqrt t)⁻¹ *
      (1 + 2 * Real.exp (-(Real.pi) * (1 / t)) / (1 - Real.exp (-(Real.pi) * (1 / t)))) := by
  have hinv : (1:ℝ) ≤ 1 / t := by
    rw [le_div_iff₀ ht]
    linarith
  have hdec := thetaT_decay hinv
  rw [thetaT_transform ht]
  exact mul_le_mul_of_nonneg_left hdec (by positivity)

/-! ## The kernel dualization: the pointwise algebra of the t = 1 split -/

/-- THE KERNEL DUALIZATION: the pointwise identity behind the t = 1 split
of the `s = 2` Mellin kernel. For every `t > 0`,
`t·(thetaT t − 1) = √t·(thetaT (1/t) − 1) + (√t − t)`. Under the dual
variable `u = 1/t` the small-t half of the kernel becomes a large-t
integral against the dual theta — the algebra the next window's `E5`-half
evaluation stands on. Pure arithmetic on the transformation. -/
theorem mellin_s2_dualize {t : ℝ} (ht : 0 < t) :
    t * (thetaT t - 1) = Real.sqrt t * (thetaT (1 / t) - 1) + (Real.sqrt t - t) := by
  have hspos : 0 < Real.sqrt t := Real.sqrt_pos.mpr ht
  have hsq : Real.sqrt t * Real.sqrt t = t := Real.mul_self_sqrt ht.le
  have ts : t * (Real.sqrt t)⁻¹ = Real.sqrt t := by
    field_simp
    rw [pow_two]
    exact hsq.symm
  rw [thetaT_transform ht, mul_sub, ← mul_assoc, ts]
  ring

/-! ## The t = 1 split of the s = 2 Mellin kernel -/

theorem mellin_s2_integrable_union :
    IntegrableOn (fun x => x * (thetaT x - 1)) (Ioc (0:ℝ) 1 ∪ Ioi (1:ℝ)) volume := by
  obtain ⟨h1, h2⟩ := mellin_s2_integrable
  rw [integrableOn_union]
  exact ⟨h1, h2⟩

/-- THE FULL KERNEL'S INTEGRABILITY: the `s = 2` Mellin kernel of the R69
normalization, `t ↦ t·(thetaT t − 1)`, is integrable on the whole half-line
`(0, ∞)` — the R233 two-half receipt now standing as one integral. The
kernel's VALUE on any interval remains a named window; this is existence
only. -/
theorem mellin_s2_integrable_full :
    IntegrableOn (fun x => x * (thetaT x - 1)) (Ioi (0:ℝ)) volume := by
  rw [← Set.Ioc_union_Ioi_eq_Ioi (by norm_num : (0:ℝ) ≤ 1)]
  exact mellin_s2_integrable_union

/-- THE T = 1 SPLIT, whole: the `s = 2` Mellin kernel's integral over the
half-line splits at `t = 1`,
`∫₀^∞ t(Θ(t)−1) dt = ∫₀^1 t(Θ(t)−1) dt + ∫₁^∞ t(Θ(t)−1) dt`,
the honest skeleton of the manuscript route (the Poisson small-t half, the
E1 large-t half). Both half-VALUES remain named windows; the split itself
now stands as a theorem on the certified stones. -/
theorem mellin_s2_split :
    ∫ x in Ioi (0:ℝ), x * (thetaT x - 1) ∂ MeasureTheory.volume
      = (∫ x in Ioc (0:ℝ) 1, x * (thetaT x - 1) ∂ MeasureTheory.volume)
        + (∫ x in Ioi (1:ℝ), x * (thetaT x - 1) ∂ MeasureTheory.volume) := by
  obtain ⟨h1, h2⟩ := mellin_s2_integrable
  have hdisj : Disjoint (Ioc (0:ℝ) 1) (Ioi (1:ℝ)) := by
    rw [Set.disjoint_left]
    intro x hx
    simp only [Set.mem_Ioc] at hx
    obtain ⟨h0, h1⟩ := hx
    simp only [Set.mem_Ioi, not_lt]
    exact h1
  have hsplit := setIntegral_union (s := Ioc (0:ℝ) 1) (t := Ioi (1:ℝ))
    (f := fun x => x * (thetaT x - 1)) hdisj measurableSet_Ioi h1 h2
  rw [Set.Ioc_union_Ioi_eq_Ioi (by norm_num : (0:ℝ) ≤ 1)] at hsplit
  exact hsplit

end YangMills.DualBook
