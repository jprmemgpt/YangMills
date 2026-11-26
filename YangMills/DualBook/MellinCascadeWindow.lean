/-
PROVENANCE: R238 — the Mellin Scaling Cascade window (w3), Papa's 170th
ask, following Gemini's relay (R237 sealed at master 5daeee0, W1 closed).
The window lifts the theta structural laws to the s = 2 Mellin integrals
via the change of variables t -> c*t, reducing the four remaining
Epstein debts (Z_1100, Z_1000 + Z_1110, and the shared Z_1111) to the
TWO analytic evaluations of window w2.

HONEST WINDOW SPLIT (read before citing):
  PROVEN HERE (conditional on the two time-axis Jacobi anchors, exactly
  mirroring DualBookAssembly's pattern):
    * `mellin_cov_scale` — the pure change-of-variables engine,
      UNCONDITIONAL (no theta content, no anchors);
    * `theta1100T_eq_scaled` — the v1.5 latch law read on the time axis,
      under anchor A;
    * `kernel1100_integrable_full` — the 1100 kernel's full-half-line
      integrability, under anchor A (by the cascade it IS the paid 1111
      kernel after t -> 2t);
    * `ZAdic1100_eq_quarter_ZAdic1111` — STONE A: Z_1100(2) = (1/4) Z_1111(2);
    * `gauss_sum_eq_scaled` — the D1' sum law read on the time axis,
      under anchors A and B;
    * `ZAdic1000_add_ZAdic1110_eq` — STONE B:
      Z_1000(2) + Z_1110(2) = (1/8) Z_1111(2).
  NAMED WINDOWS (hypotheses, NOT proved here): the two Jacobi doubling
  anchors `anchorA_time`, `anchorB_time` (the Landen identities
  thetaT t * thetaFour t = thetaFour (2*t)^2 and
  thetaT t^2 + thetaFour t^2 = 2 * thetaT (2*t)^2). The q-space
  conditional laws `theta_1100_of_anchor` and `theta_sum_D1'`
  (DualBookAssembly, rung 5) are the same anchors' q-space faces; the
  anchor window itself (the parity decomposition of the two-dimensional
  theta series) is the sharpest named stone on the docket.

SCOPE NOTE: this module certifies THIS ARITHMETIC — change of variables
and theta composite identities at s = 2. It proves nothing about
physical four-dimensional Yang-Mills theory and claims no Clay
Millennium result. Bench frozen at 100.0. The crossing never claimed.

PROVED AND SEALED in the c1664/c1665 window (Thu 2026-11-26, Mathlib
31ce06ea / Lean v4.37.0-rc1 vintage): lake build zero errors, zero
sorry, zero native_decide, zero unsafe; notarized
[propext, Classical.choice, Quot.sound] on all six public theorems
(mellin_cov_scale, theta1100T_eq_scaled, kernel1100_integrable_full,
ZAdic1100_eq_quarter_ZAdic1111, gauss_sum_eq_scaled,
ZAdic1000_add_ZAdic1110_eq). The build and notary ran on exactly the
source of md5 15cfcdab83ecd3c185b5b6cd3a8a481e; this certificate adds
only this seal note and the remainders footer below.
Pre-registered via mailbox order 1134 item GEN_PREREG (Papa's 170th
ask, Gemini's relay); window w3 DISCHARGED, the four Epstein debts
reduced to the two w2 evaluations as the relay specified.
-/
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import YangMills.DualBook.ThetaFourPoisson

/-!
# The Mellin Scaling Cascade (R238, window w3)

The two cascade stones: under the Jacobi anchors, the latch law
`Theta_1100(q) = Theta_1111(q^2)` integrates to
`Z_1100(2) = (1/4) Z_1111(2)` (t -> 2t), and the D1' sum law
`Theta_1000(q) + Theta_1110(q) = 2 Theta_1111(q^4)` integrates to
`Z_1000(2) + Z_1110(2) = (1/8) Z_1111(2)` (t -> 4t). The engine is the
pure dilation change of variables `mellin_cov_scale`, unconditional.
-/

namespace YangMills.DualBook

open MeasureTheory Real Set

/-! ## The change-of-variables engine (unconditional) -/

/-- THE MELLIN SCALING ENGINE: for any `c > 0` and any function `f`,
the s = 2 Mellin kernel's dilation `t -> c*t` rescales the half-line
integral by exactly `c^(-2)`. Pure change of variables: no theta
content, no measurability, no hypotheses beyond `0 < c`. -/
theorem mellin_cov_scale {f : ℝ → ℝ} {c : ℝ} (hc : 0 < c) :
    ∫ x in Ioi (0:ℝ), x * f (x * c) ∂volume
      = (c⁻¹ * c⁻¹) * ∫ u in Ioi (0:ℝ), u * f u ∂volume := by
  have key := integral_comp_mul_right_Ioi
    (g := fun u => u * f u) (a := (0:ℝ)) hc
  simp only [zero_mul] at key
  have hL : ∀ x : ℝ, x * f (x * c) = c⁻¹ • ((x * c) * f (x * c)) := by
    intro x
    have h1 : c⁻¹ * (x * c) = x := by
      rw [mul_comm x c, ← mul_assoc, inv_mul_cancel₀ hc.ne', one_mul]
    calc x * f (x * c) = (c⁻¹ * (x * c)) * f (x * c) := by rw [h1]
      _ = c⁻¹ * ((x * c) * f (x * c)) := by ring
  calc ∫ x in Ioi (0:ℝ), x * f (x * c) ∂volume
      = ∫ x in Ioi (0:ℝ), c⁻¹ • ((x * c) * f (x * c)) ∂volume :=
        integral_congr_ae
          (Filter.mem_of_superset (self_mem_ae_restrict measurableSet_Ioi)
            (fun x _hx => hL x))
    _ = c⁻¹ • ∫ x in Ioi (0:ℝ), (x * c) * f (x * c) ∂volume :=
        integral_smul c⁻¹ (fun x => (x * c) * f (x * c))
    _ = c⁻¹ • (c⁻¹ • ∫ u in Ioi (0:ℝ), u * f u ∂volume) := by rw [key]
    _ = (c⁻¹ * c⁻¹) * ∫ u in Ioi (0:ℝ), u * f u ∂volume := by
        rw [smul_smul, smul_eq_mul]

/-! ## The time-axis Jacobi anchors (named windows, carried as hypotheses) -/

/-- Jacobi anchor A on the time axis (the Landen identity):
`thetaT t * thetaFour t = thetaFour (2 * t)^2` for all `t > 0`.

A NAMED WINDOW, not proved in this file: it rides every cascade theorem
below as an explicit hypothesis, exactly as `jacobiAnchorA` rides the
q-space laws of `DualBookAssembly`. The parity-decomposition proof of
the doubling identity is the follow-up window; this file only cashes
what the anchor buys. -/
def anchorA_time : Prop :=
  ∀ t, 0 < t → thetaT t * thetaFour t = thetaFour (2 * t) ^ 2

/-- Jacobi anchor B on the time axis:
`thetaT t^2 + thetaFour t^2 = 2 * thetaT (2 * t)^2` for all `t > 0`.

A NAMED WINDOW, carried as an explicit hypothesis, like `anchorA_time`
(the q-space face is `jacobiAnchorB`). -/
def anchorB_time : Prop :=
  ∀ t, 0 < t → thetaT t ^ 2 + thetaFour t ^ 2 = 2 * thetaT (2 * t) ^ 2

/-! ## STONE A: the latch law integrated (t -> 2t) -/

/-- Θ_1100 on the time axis: `thetaFour^2 * thetaT^2`, the corrected
convention composite of `DualBookAssembly` read at the t-nome. -/
noncomputable def theta1100T (t : ℝ) : ℝ := thetaFour t ^ 2 * thetaT t ^ 2

/-- THE LATCH LAW ON THE TIME AXIS: under anchor A,
`theta1100T t = thetaFour (2 * t)^4` for every `t > 0` — the v1.5 law
`Theta_1100(q) = Theta_1111(q^2)` at the t-nome `q = exp (-pi t)`,
i.e. the R236 Landen route `thetaT * thetaFour = thetaFour(2t)^2`
squared. -/
theorem theta1100T_eq_scaled (hA : anchorA_time) {t : ℝ} (ht : 0 < t) :
    theta1100T t = thetaFour (2 * t) ^ 4 := by
  have e := hA t ht
  unfold theta1100T
  calc thetaFour t ^ 2 * thetaT t ^ 2 = (thetaT t * thetaFour t) ^ 2 := by ring
    _ = (thetaFour (2 * t) ^ 2) ^ 2 := by rw [e]
    _ = thetaFour (2 * t) ^ 4 := by ring

/-- THE 1100 KERNEL'S EXISTENCE: under anchor A the 1100 kernel is the
paid 1111 kernel after `t -> 2t`, so its full half-line integrability
is `kernel1111_integrable_full` in disguise — the cascade's first
dividend: the new arm's existence costs one change of variables. -/
theorem kernel1100_integrable_full (hA : anchorA_time) :
    IntegrableOn (fun x => x * (theta1100T x - 1)) (Ioi (0:ℝ)) volume := by
  have hIff := (integrableOn_Ioi_comp_mul_left_iff
    (fun u => (1 / 2) * u * (thetaFour u ^ 4 - 1)) (0:ℝ) (a := (2:ℝ))
    (by norm_num))
  simp only [mul_zero] at hIff
  have hFin : IntegrableOn (fun u => (1 / 2) * u * (thetaFour u ^ 4 - 1))
      (Ioi (0:ℝ)) volume := by
    have hker : Integrable (fun u => u * (thetaFour u ^ 4 - 1))
        (MeasureTheory.Measure.restrict volume (Ioi (0:ℝ))) :=
      kernel1111_integrable_full
    have hconst : Integrable (fun u => (1 / 2) * (u * (thetaFour u ^ 4 - 1)))
        (MeasureTheory.Measure.restrict volume (Ioi (0:ℝ))) :=
      hker.const_mul (1 / 2)
    exact hconst.congr
      (Filter.mem_of_superset (self_mem_ae_restrict measurableSet_Ioi)
        (fun u _hu => by
          show (1 / 2) * (u * (thetaFour u ^ 4 - 1))
            = (1 / 2) * u * (thetaFour u ^ 4 - 1)
          ring))
  have hScaled : Integrable
      (fun x => (1 / 2) * (2 * x) * (thetaFour (2 * x) ^ 4 - 1))
      (MeasureTheory.Measure.restrict volume (Ioi (0:ℝ))) := hIff.mpr hFin
  exact hScaled.congr
    (Filter.mem_of_superset (self_mem_ae_restrict measurableSet_Ioi)
      (fun x hx => by
        have e := theta1100T_eq_scaled hA (Set.mem_Ioi.mp hx)
        have hx2 : (1:ℝ) / 2 * (2 * x) = x := by
          show (1:ℝ) * (2:ℝ)⁻¹ * (2 * x) = x
          rw [one_mul]
          exact inv_mul_cancel_left₀ (by norm_num : (2:ℝ) ≠ 0) x
        show (1 / 2) * (2 * x) * (thetaFour (2 * x) ^ 4 - 1)
          = x * (theta1100T x - 1)
        rw [e, hx2]))

/-- THE 1100 ARM'S HONEST OBJECT (D1''): the book's s = 2 normalization
of the 1100 arm,
`ZAdic1100 = pi^2 * integral over (0, inf) of t * (theta1100T t - 1)`.
Under anchor A the defining integral EXISTS by
`kernel1100_integrable_full`; its closed-form VALUE is window (w2),
paid automatically once Z_1111(2) is evaluated (STONE A below). -/
noncomputable def ZAdic1100 : ℝ :=
  Real.pi ^ 2 * ∫ x in Ioi (0:ℝ), x * (theta1100T x - 1) ∂volume

/-- STONE A — THE LATCH LAW INTEGRATED: under anchor A,
`Z_1100(2) = (1/4) * Z_1111(2)`. The latch law turns the 1111 Mellin
kernel into the 1100 kernel after `t -> 2t`, and the dilation costs
exactly `2^(-2) = 1/4`. The first Epstein debt is reduced to the shared
Z_1111 evaluation. -/
theorem ZAdic1100_eq_quarter_ZAdic1111 (hA : anchorA_time) :
    ZAdic1100 = (1 / 4) * ZAdic1111 := by
  have hK : ∫ x in Ioi (0:ℝ), x * (theta1100T x - 1) ∂volume
      = ∫ x in Ioi (0:ℝ), x * (thetaFour (x * 2) ^ 4 - 1) ∂volume :=
    integral_congr_ae
      (Filter.mem_of_superset (self_mem_ae_restrict measurableSet_Ioi)
        (fun x hx => by
          have e := theta1100T_eq_scaled hA (Set.mem_Ioi.mp hx)
          show x * (theta1100T x - 1) = x * (thetaFour (x * 2) ^ 4 - 1)
          rw [e, mul_comm 2 x]))
  have hM : ∫ x in Ioi (0:ℝ), x * (thetaFour (x * 2) ^ 4 - 1) ∂volume
      = ((2:ℝ)⁻¹ * (2:ℝ)⁻¹) * ∫ u in Ioi (0:ℝ), u * (thetaFour u ^ 4 - 1) ∂volume :=
    mellin_cov_scale (f := fun u => thetaFour u ^ 4 - 1) (c := (2:ℝ))
      (by norm_num)
  have hC : ((2:ℝ)⁻¹ * (2:ℝ)⁻¹) = (1:ℝ) / 4 := by norm_num
  unfold ZAdic1100 ZAdic1111
  rw [hK, hM, hC]
  ring

/-! ## STONE B: the D1' sum law integrated (t -> 4t) -/

/-- THE D1' SUM LAW ON THE TIME AXIS: under anchors A and B,
`gauss1000 t + gauss1110 t = 2 * thetaFour (4 * t)^4` for every `t > 0`
— the q-space `theta_sum_D1'` at the t-nome (q^4 = exp (-4 pi t)):
the mixed pair sums onto twice the quadrupled 1111 character. -/
theorem gauss_sum_eq_scaled (hA : anchorA_time) (hB : anchorB_time)
    {t : ℝ} (ht : 0 < t) :
    gauss1000 t + gauss1110 t = 2 * thetaFour (4 * t) ^ 4 := by
  have eA := hA t ht
  have eB := hB t ht
  have h2t : 0 < 2 * t := by positivity
  have eA2' : thetaT (2 * t) * thetaFour (2 * t) = thetaFour (4 * t) ^ 2 := by
    have h := hA (2 * t) h2t
    have h4 : 2 * (2 * t) = 4 * t := by ring
    rw [h, h4]
  simp only [gauss1000, gauss1110]
  calc thetaFour t * thetaT t ^ 3 + thetaFour t ^ 3 * thetaT t
      = (thetaT t * thetaFour t) * (thetaT t ^ 2 + thetaFour t ^ 2) := by ring
    _ = thetaFour (2 * t) ^ 2 * (2 * thetaT (2 * t) ^ 2) := by rw [eA, eB]
    _ = 2 * (thetaT (2 * t) * thetaFour (2 * t)) ^ 2 := by ring
    _ = 2 * (thetaFour (4 * t) ^ 2) ^ 2 := by rw [eA2']
    _ = 2 * thetaFour (4 * t) ^ 4 := by ring_nf

/-- STONE B — THE D1' SUM LAW INTEGRATED: under anchors A and B,
`Z_1000(2) + Z_1110(2) = (1/8) * Z_1111(2)`. The sum law turns the
quadrupled 1111 kernel into the sum of the 1000 and 1110 kernels, and
the dilation `t -> 4t` costs exactly `4^(-2) = 1/16`, halved to `1/8`
by the sum law's factor 2. The three remaining Epstein debts collapse
to the single shared Z_1111 evaluation. -/
theorem ZAdic1000_add_ZAdic1110_eq (hA : anchorA_time) (hB : anchorB_time) :
    ZAdic1000 + ZAdic1110 = (1 / 8) * ZAdic1111 := by
  have h1 : Integrable (fun x => x * (gauss1000 x - 1))
      (MeasureTheory.Measure.restrict volume (Ioi (0:ℝ))) :=
    kernel1000_integrable_full
  have h2 : Integrable (fun x => x * (gauss1110 x - 1))
      (MeasureTheory.Measure.restrict volume (Ioi (0:ℝ))) :=
    kernel1110_integrable_full
  have hM : ∫ x in Ioi (0:ℝ), x * (thetaFour (x * 4) ^ 4 - 1) ∂volume
      = ((4:ℝ)⁻¹ * (4:ℝ)⁻¹) * ∫ u in Ioi (0:ℝ), u * (thetaFour u ^ 4 - 1) ∂volume :=
    mellin_cov_scale (f := fun u => thetaFour u ^ 4 - 1) (c := (4:ℝ))
      (by norm_num)
  have hAdd : ∫ x in Ioi (0:ℝ), x * (gauss1000 x - 1) ∂volume
      + ∫ x in Ioi (0:ℝ), x * (gauss1110 x - 1) ∂volume
      = ∫ x in Ioi (0:ℝ),
          (fun x => x * (gauss1000 x - 1)) x
            + (fun x => x * (gauss1110 x - 1)) x ∂volume :=
    (integral_add h1 h2).symm
  have hSum : ∫ x in Ioi (0:ℝ),
      (fun x => x * (gauss1000 x - 1)) x
        + (fun x => x * (gauss1110 x - 1)) x ∂volume
      = 2 * (((4:ℝ)⁻¹ * (4:ℝ)⁻¹)
          * ∫ u in Ioi (0:ℝ), u * (thetaFour u ^ 4 - 1) ∂volume) := by
    calc ∫ x in Ioi (0:ℝ),
          (fun x => x * (gauss1000 x - 1)) x
            + (fun x => x * (gauss1110 x - 1)) x ∂volume
        = ∫ x in Ioi (0:ℝ),
            (2:ℝ) • (x * (thetaFour (x * 4) ^ 4 - 1)) ∂volume :=
          integral_congr_ae
            (Filter.mem_of_superset (self_mem_ae_restrict measurableSet_Ioi)
              (fun x hx => by
                have e := gauss_sum_eq_scaled hA hB (Set.mem_Ioi.mp hx)
                have hFac : x * (gauss1000 x - 1) + x * (gauss1110 x - 1)
                    = x * (gauss1000 x + gauss1110 x - 2) := by ring
                show x * (gauss1000 x - 1) + x * (gauss1110 x - 1)
                  = (2:ℝ) • (x * (thetaFour (x * 4) ^ 4 - 1))
                rw [hFac, e, mul_comm 4 x, smul_eq_mul]
                ring))
      _ = (2:ℝ) • ∫ x in Ioi (0:ℝ),
            x * (thetaFour (x * 4) ^ 4 - 1) ∂volume :=
          integral_smul (2:ℝ) (fun x => x * (thetaFour (x * 4) ^ 4 - 1))
      _ = 2 * (((4:ℝ)⁻¹ * (4:ℝ)⁻¹)
          * ∫ u in Ioi (0:ℝ), u * (thetaFour u ^ 4 - 1) ∂volume) := by
          rw [hM, smul_eq_mul]
  have hC : ((4:ℝ)⁻¹ * (4:ℝ)⁻¹) = (1:ℝ) / 16 := by norm_num
  have hD : (1:ℝ) / 8 = 2 * ((1:ℝ) / 16) := by norm_num
  unfold ZAdic1000 ZAdic1110 ZAdic1111
  rw [← mul_add, hAdd, hSum, hC, hD]
  ring

end YangMills.DualBook

/-!
  REMAINDERS, honest and named (for R239+):
  (w2) the VALUES, now the sole remaining debt of the Epstein book:
       Z_1111(2) = -(2/3)*pi^2*log 2 (the modular engine is banked:
       thetaFour_transform, R237), and the difference
       Z_1000(2) - Z_1110(2) = 2*pi*G (Gaussian integers + the R231
       Catalan gate); with this window's cascade both evaluations
       then cascade down to all four arms at once.
  (ANCHORS) the two Jacobi doubling anchors anchorA_time/anchorB_time
       remain NAMED WINDOWS (hypotheses here, exactly as their q-space
       faces jacobiAnchorA/B ride DualBookAssembly): the parity
       decomposition of the two-dimensional theta series is the
       sharpest named stone on the docket (R239 candidate).
  Bench frozen at 100.0. Scope: THIS ARITHMETIC only.
-/
