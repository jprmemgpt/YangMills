/-
PROVENANCE: R230/R3 FRULLANI-EXPONENTIAL-INTEGRABILITY (Tue 2026-11-24). The next
stone of the W1 ladder after the v1.5 seal (commit 8fcfae0, both anchors and
the unconditional assembly on master). The window statement is read
byte-faithful from the certified retired source on live master
(YangMills/DualBook/FrullaniBook.lean, the rung-6 named window):

  frullaniExpWindow : Prop :=
    ∫ x : ℝ in Ioi (0 : ℝ), x⁻¹ * (Real.exp (-4 * x) - Real.exp (-x)) = -Real.log 4

THE CONTENT, IN ONE BREATH: this window is Mathlib's receipt cashed at the
book's own constants. Frullani.integral_Ioi_eq (the pinned vintage's exact
theorem, read before writing) gives, for f locally integrable on (0, ∞) with
limits L at 0⁺ and R at +∞ and integrable kernel x⁻¹ • (f (a·x) − f (b·x)):

  ∫ x in Ioi 0, x⁻¹ • (f (a·x) − f (b·x)) = log (b/a) • (L − R).

This window instantiates it at f = fun t => exp (−t), a = 4, b = 1: the limits
are L = exp (−0) = 1 and R = 0 (Mathlib's own tendsto receipts), and the value
log (1/4) • (L − 0) = −log 4 exactly. The one named sub-window — the near-0
integrability of the kernel, which FrullaniBook.lean carries as NAMED, never
paid — is paid here: |x⁻¹·(exp(−4x) − exp(−x))| ≤ 10 on (0,1) (the
cancellation |exp t − 1| ≤ 2|t| of the pinned Mathlib, priced at the two
exponentials, 8x + 2x = 10x, and the x ≥ 1/4 leg by x⁻¹ ≤ 4 and exp ≤ 1),
and ≤ 2·exp(−x) on [1,∞), so the kernel is integrable on (0,∞).

THE BORDER, NAMED BEFORE SILICON: every receipt of this window is proved on the
green record against the pinned triplet (Mathlib 31ce06ea, lake 5.0.0, Lean
v4.37.0-rc1) with the v1.5 seal reproduced green (3,544 jobs) before any new
math crossed the tree. Kernel measurability rides the `fun_prop` engine and
`Measurable.aestronglyMeasurable`; no sorry, no native_compute, no trust
beyond the pinned mathematical content.

SCOPE NOTE: this module certifies THIS ARITHMETIC — one classical Frullani
integral at explicit constants, standard real analysis. It proves nothing
about physical four-dimensional Yang–Mills theory and claims no Clay
Millennium result. Bench FROZEN AT 100.0, the crossing never claimed.
-/
import Mathlib.Analysis.SpecialFunctions.FrullaniIntegral
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import YangMills.DualBook.FrullaniBook

/-!
# The Frullani window paid (R3, the third stone of W1)
-/

namespace YangMills.DualBook

open Set MeasureTheory Filter

/-! ## The near-0 sub-window: the kernel is integrable on (0, ∞) -/

/-- The kernel is measurable: inverses, exponentials, products and
differences of continuous pieces, closed by the `fun_prop` engine. -/
private theorem kernel_meas :
    Measurable (fun x : ℝ => x⁻¹ * (Real.exp (-4 * x) - Real.exp (-x))) := by
  fun_prop

/-- The near-0 cancellation bound (the paid sub-window, first half): on
(0, 1) the kernel is bounded by 10 in absolute value — for `x ≤ 1/4` by the
pinned Mathlib bound `abs_exp_sub_one_le` (the exp(t) − 1 = O(t)
cancellation at both exponentials: 8x + 2x = 10x), for `x ≥ 1/4` by
`x⁻¹ ≤ 4` and `exp ≤ 1` on the nonpositive arguments. -/
private theorem bound_kernel (x : ℝ) (hx0 : 0 < x) :
    |x⁻¹ * (Real.exp (-4 * x) - Real.exp (-x))| ≤ 10 := by
  by_cases hq : x ≤ 1 / (4:ℝ)
  · -- near 0: the exponential cancellation 8x + 2x = 10x
    have ha4 : |(-4:ℝ) * x| ≤ 1 := by
      rw [abs_mul, abs_of_neg (by norm_num : (-4:ℝ) < 0), abs_of_pos hx0]
      linarith
    have h4 := Real.abs_exp_sub_one_le ha4
    rw [abs_mul, abs_of_neg (by norm_num : (-4:ℝ) < 0), abs_of_pos hx0] at h4
    have h4' : |Real.exp (-4 * x) - 1| ≤ 8 * x := by linarith [h4]
    have hbx : |(-x:ℝ)| ≤ 1 := by
      rw [abs_neg, abs_of_pos hx0]
      linarith
    have h1 := Real.abs_exp_sub_one_le (x := -x) hbx
    have hxabs : |x| = x := abs_of_pos hx0
    rw [abs_neg, hxabs] at h1
    obtain ⟨h4a, h4b⟩ := abs_le.mp h4'
    obtain ⟨h1a, h1b⟩ := abs_le.mp h1
    have hkey : |Real.exp (-4 * x) - Real.exp (-x)| ≤ 10 * x :=
      abs_le.mpr ⟨by linarith, by linarith⟩
    rw [abs_mul, abs_of_pos (inv_pos.mpr hx0)]
    calc x⁻¹ * |Real.exp (-4 * x) - Real.exp (-x)| ≤ x⁻¹ * (10 * x) :=
          mul_le_mul_of_nonneg_left hkey (by positivity)
      _ = 10 := by rw [← mul_assoc, mul_right_comm, inv_mul_cancel₀ (ne_of_gt hx0), one_mul]
  · -- past 1/4: x⁻¹ ≤ 4 and both exponentials ≤ 1
    push_neg at hq
    have hinv : x⁻¹ ≤ 4 := by
      rw [← one_div, div_le_iff₀ hx0]
      linarith
    have he4 : (0:ℝ) < Real.exp (-4 * x) := Real.exp_pos _
    have he1 : (0:ℝ) < Real.exp (-x) := Real.exp_pos _
    have hb4 : Real.exp (-4 * x) ≤ 1 := by
      have h := Real.exp_le_exp.mpr (by linarith : (-4:ℝ) * x ≤ 0)
      rwa [Real.exp_zero] at h
    have hb1 : Real.exp (-x) ≤ 1 := by
      have h := Real.exp_le_exp.mpr (by linarith : (-x:ℝ) ≤ 0)
      rwa [Real.exp_zero] at h
    have hd2 : |Real.exp (-4 * x) - Real.exp (-x)| ≤ 2 :=
      abs_le.mpr ⟨by linarith, by linarith⟩
    rw [abs_mul, abs_of_pos (inv_pos.mpr hx0)]
    calc x⁻¹ * |Real.exp (-4 * x) - Real.exp (-x)| ≤ x⁻¹ * 2 :=
          mul_le_mul_of_nonneg_left hd2 (by positivity)
      _ ≤ 10 := by linarith

/-- The tail bound: on [1, ∞) the kernel is dominated by
`exp (−x) + exp (−x)`, since `x⁻¹ ≤ 1` and the second exponential
dominates the first on the nonpositive arguments. -/
private theorem bound_kernel_ci (x : ℝ) (hx1 : (1:ℝ) ≤ x) :
    |x⁻¹ * (Real.exp (-4 * x) - Real.exp (-x))| ≤ Real.exp (-x) + Real.exp (-x) := by
  have hx0 : (0:ℝ) < x := lt_of_lt_of_le zero_lt_one hx1
  have hin : x⁻¹ ≤ 1 := by
    rw [← one_div, div_le_iff₀ hx0]
    linarith
  have he4 : (0:ℝ) < Real.exp (-4 * x) := Real.exp_pos _
  have he1 : (0:ℝ) < Real.exp (-x) := Real.exp_pos _
  have hb4 : Real.exp (-4 * x) ≤ Real.exp (-x) := Real.exp_le_exp.mpr (by linarith)
  rw [abs_mul, abs_of_pos (inv_pos.mpr hx0),
    abs_of_nonpos (by linarith : Real.exp (-4 * x) - Real.exp (-x) ≤ 0), neg_sub]
  calc x⁻¹ * (Real.exp (-x) - Real.exp (-4 * x))
      ≤ 1 * (Real.exp (-x) - Real.exp (-4 * x)) :=
        mul_le_mul_of_nonneg_right hin (by linarith)
    _ = Real.exp (-x) - Real.exp (-4 * x) := by ring
    _ ≤ Real.exp (-x) + Real.exp (-x) := by linarith

/-- The kernel is integrable on (0, 1): bounded by 10 on a finite-measure
interval, by the `IntegrableOn.of_bound` receipt. -/
private theorem integrable_on_Ioo :
    IntegrableOn (fun x : ℝ => x⁻¹ * (Real.exp (-4 * x) - Real.exp (-x)))
      (Ioo (0:ℝ) 1) := by
  have hvol : volume (Ioo (0:ℝ) 1) < ⊤ := by rw [Real.volume_Ioo]; simp
  have hmeas : AEStronglyMeasurable
      (fun x : ℝ => x⁻¹ * (Real.exp (-4 * x) - Real.exp (-x)))
      (volume.restrict (Ioo (0:ℝ) 1)) := kernel_meas.aestronglyMeasurable
  refine IntegrableOn.of_bound hvol hmeas 10 ?_
  refine Filter.mem_of_superset (self_mem_ae_restrict measurableSet_Ioo)
    (fun x hx => ?_)
  have hx0 : (0:ℝ) < x := hx.1
  show ‖(fun x : ℝ => x⁻¹ * (Real.exp (-4 * x) - Real.exp (-x))) x‖ ≤ 10
  rw [Real.norm_eq_abs (x⁻¹ * (Real.exp (-4 * x) - Real.exp (-x)))]
  exact bound_kernel x hx0

/-- The kernel is integrable on [1, ∞): dominated by `exp (−x) + exp (−x)`,
which rides the pinned `integrableOn_exp_neg_Ioi` receipt. -/
private theorem integrable_on_Ici :
    IntegrableOn (fun x : ℝ => x⁻¹ * (Real.exp (-4 * x) - Real.exp (-x)))
      (Ici (1:ℝ)) := by
  have hexp : IntegrableOn (fun x : ℝ => Real.exp (-x)) (Ici (1:ℝ)) :=
    (integrableOn_exp_neg_Ioi (0:ℝ)).mono_set
      (fun x hx => Set.mem_Ioi.mpr (lt_of_lt_of_le zero_lt_one hx))
  have hmeas : AEStronglyMeasurable
      (fun x : ℝ => x⁻¹ * (Real.exp (-4 * x) - Real.exp (-x)))
      (volume.restrict (Ici (1:ℝ))) := kernel_meas.aestronglyMeasurable
  refine Integrable.mono (IntegrableOn.add hexp hexp) hmeas ?_
  refine Filter.mem_of_superset (self_mem_ae_restrict measurableSet_Ici)
    (fun x hx => ?_)
  show ‖(fun x : ℝ => x⁻¹ * (Real.exp (-4 * x) - Real.exp (-x))) x‖
      ≤ ‖((fun x : ℝ => Real.exp (-x)) + (fun x : ℝ => Real.exp (-x))) x‖
  simp only [Real.norm_eq_abs, Pi.add_apply]
  rw [abs_of_nonneg (by positivity : (0:ℝ) ≤ Real.exp (-x) + Real.exp (-x))]
  exact bound_kernel_ci x hx

/-- THE NAMED SUB-WINDOW, PAID: the Frullani kernel is integrable on
(0, ∞) — the near-0 half by the cancellation bound, the tail by domination,
the whole by the interval split (0, 1) ∪ [1, ∞). -/
theorem frKernel_integrable :
    IntegrableOn (fun x : ℝ => x⁻¹ * (Real.exp (-4 * x) - Real.exp (-x)))
      (Ioi (0:ℝ)) := by
  have hsplit : (Ioo (0:ℝ) 1) ∪ Ici (1:ℝ) = Ioi (0:ℝ) :=
    Ioo_union_Ici_eq_Ioi (by norm_num)
  rw [← hsplit]
  exact IntegrableOn.union integrable_on_Ioo integrable_on_Ici

/-! ## The window itself -/

/-- THE FRULLANI EXPONENTIAL WINDOW, PAID: the book's named window
`frullaniExpWindow` (FrullaniBook.lean, rung 6) — the exponential kernel at
the book's own constants −4 and −1 pays exactly −log 4 — now an
unconditional theorem: Mathlib's `Frullani.integral_Ioi_eq` instantiated at
`f = fun t => exp (−t)`, `a = 4`, `b = 1`, limits `L = exp (−0) = 1` and
`R = 0`, with the named near-0 integrability sub-window paid above. W1's
third rung, closed. -/
theorem frullaniExpWindow_paid : frullaniExpWindow := by
  have hfcont : Continuous fun t : ℝ => Real.exp (-t) :=
    Real.continuous_exp.comp continuous_neg
  have hf : LocallyIntegrableOn (fun t : ℝ => Real.exp (-t)) (Ioi (0:ℝ)) :=
    (hfcont.continuousOn (s := Ioi (0:ℝ))).locallyIntegrableOn measurableSet_Ioi
  have hL : Tendsto (fun t : ℝ => Real.exp (-t)) (nhdsWithin (0:ℝ) (Ioi (0:ℝ)))
      (nhds ((fun t : ℝ => Real.exp (-t)) (0:ℝ))) :=
    hfcont.continuousWithinAt
  have hR : Tendsto (fun t : ℝ => Real.exp (-t)) atTop (nhds 0) :=
    Real.tendsto_exp_neg_atTop_nhds_zero
  have heqon : EqOn (fun x : ℝ => x⁻¹ * (Real.exp (-4 * x) - Real.exp (-x)))
      (fun x : ℝ => x⁻¹ • ((fun t : ℝ => Real.exp (-t)) (4 * x) -
        (fun t : ℝ => Real.exp (-t)) (1 * x)))
      (Ioi (0:ℝ)) := fun x _ => by
    show x⁻¹ * (Real.exp (-4 * x) - Real.exp (-x))
        = x⁻¹ • (Real.exp (-(4 * x)) - Real.exp (-(1 * x)))
    rw [smul_eq_mul, neg_mul, one_mul]
  have hint : IntegrableOn
      (fun x : ℝ => x⁻¹ • ((fun t : ℝ => Real.exp (-t)) (4 * x) -
        (fun t : ℝ => Real.exp (-t)) (1 * x)))
      (Ioi (0:ℝ)) :=
    IntegrableOn.congr_fun frKernel_integrable heqon measurableSet_Ioi
  have hval := Frullani.integral_Ioi_eq hf (by norm_num : (0:ℝ) < 4)
    (by norm_num : (0:ℝ) < 1) hL hR hint
  have hlog : Real.log (1 / (4:ℝ)) = -Real.log 4 := by
    rw [Real.log_div (by norm_num : (1:ℝ) ≠ 0) (by norm_num : (4:ℝ) ≠ 0), Real.log_one]
    ring
  show ∫ x : ℝ in Ioi (0:ℝ),
      x⁻¹ * (Real.exp (-4 * x) - Real.exp (-x)) = -Real.log 4
  rw [setIntegral_congr_fun measurableSet_Ioi heqon, hval, hlog]
  simp [smul_eq_mul]

end YangMills.DualBook
