/-
  PROVENANCE: YangMills.DualBook.GaussArm (R236, Theorem B, the Gaussian arm).

  PRE-REGISTERED (order 1119, Papa's 160th ask, Gemini's relay): the
  elementary floor and Z[i] spine of Theorem B on the time axis,
  mirroring the R235 ThetaAdicArm pattern. Nothing re-proved that is
  already paid: thetaT_summable / thetaT_blowup / thetaT_decay (R233),
  thetaT_transform / thetaT_dual_gain (R234), thetaFour_bounds /
  abs_thetaFour_le_one (R235) are imported and used as receipts.

  STONES OF THIS WINDOW:

  (STONE i) THE HONEST OBJECTS (mask 1000 and mask 1110):
      gauss1000 t = thetaFour t * thetaT t ^ 3
      gauss1110 t = thetaFour t ^ 3 * thetaT t
  the sign characters of the four-torus on the first, resp. the first
  three, coordinates, read on the time axis.

  (STONE ii) THE INTEGRABILITY FLOOR at s = 2:
      kernel1110 small half: |t * (gauss1110 t - 1)| <= 3 on (0, 1]
        (the thetaFour cube is capped by the absolute sandwich, the
        thetaT by the R233 blow-up law) -- a bounded kernel on finite
        volume;
      kernel1110 large half: |gauss1110 t - 1| <= 22 * exp (-pi*t), the
        deficit law (thetaFour's deficit 2q cubed to 6q, times thetaT
        <= 3, plus thetaT's own deficit 4q), dominated by
        22 * (t * exp (-t)), integrable by the R235 receipt
        integrableOn_rpow_mul_exp_neg_rpow;
      kernel1000 large half: |gauss1000 t - 1| <= 54 * exp (-pi*t)
        (thetaT^3's deficit <= 52q through the R233 decay law sharpened
        to 4q on the nome <= 1/2, plus thetaFour's 2q), same dominator
        with 54;
      hence ZAdic1110 EXISTS (the full-line integral converges).

  (STONE iii) THE DIFFERENCE SPINE, opened:
      gauss1000 t - gauss1110 t
        = thetaFour t * thetaT t * (thetaT t ^ 2 - thetaFour t ^ 2)
  the antisymmetric factored form (ring identity), and the difference
  kernel is integrable on the large half (<= 76 * (t * exp (-t))). The
  chi_{-4} / r_2(n) = 4 * zeta(s) * L(s, chi_{-4}) reindex behind it is
  a NAMED WINDOW, as is the connection into catalanGate_paid (R231) and
  diffLaw_gate (R232).

  NAMED WINDOWS (unproved, explicitly not claimed this window):
  (w1) kernel1000_integrable_small: the 1000 arm's origin half needs the
       small-t super-exponential death of thetaFour, which no window has
       banked. Attack routes pre-registered for R237: the half-lattice
       Poisson stone (order 1113's flagged IF), or the Landen route
       thetaT t * thetaFour t = thetaFour (2 * t) ^ 2. Until one lands,
       ZAdic1000's defining integral is an honest formal object whose
       convergence is NOT claimed.
  (w2) The closed-form VALUES of Theorem B:
       Z_1000(2) = pi * G - (pi^2/24) * log 2
       Z_1110(2) = -pi * G - (pi^2/24) * log 2.
  (w3) The D1' sum bridge Theta_1000 + Theta_1110 = 2 * Theta_1111(q^4):
       cashes automatically once Z_1111(2) is paid (order 1114 cascade).

  House law: zero sorry, axioms [propext, Classical.choice, Quot.sound]
  only; bench frozen at 100.0; scope THIS ARITHMETIC only, nothing
  Clay claimed, the crossing never claimed.
-/
import YangMills.DualBook.ThetaAdicArm
import YangMills.DualBook.ThetaIntegrabilityWindow

namespace YangMills.DualBook

open MeasureTheory Real Set

/-! ## The mirror families of the R233 receipts -/

/-- The integer family of the time-axis theta, mirrored from R233's
`thetaFam` (same body, so the paid receipts on `thetaT_summable` see it
definitionally). -/
private noncomputable def gaussFam (t : ℝ) (z : ℤ) : ℝ :=
  Real.exp (-Real.pi * t * (z : ℝ) ^ 2)

private noncomputable def gaussTerm (t : ℝ) (n : ℕ) : ℝ :=
  Real.exp (-Real.pi * t * (n : ℝ) ^ 2)

/-- The value split on the time axis, mirroring R233's `thetaT_split`
(the `tsum_int_eq_zero_add_two_mul_tsum_pnat` twin split and
`tsum_pnat_eq_tsum_succ` for the ℕ+ face -- receipts already green in
this exact vintage). -/
private theorem thetaT_splitG {t : ℝ} (ht : 0 < t) :
    thetaT t = 1 + 2 * ∑' (n : ℕ), gaussTerm t (n + 1) := by
  have hsumm : Summable (gaussFam t) := by
    have h := thetaT_summable ht
    exact h.congr (fun z => rfl)
  have heven : Function.Even (gaussFam t) := by
    intro z
    simp only [gaussFam]
    congr 1
    push_cast
    ring
  have h0 : gaussFam t 0 = 1 := by simp only [gaussFam]; norm_num
  have hc : ∀ m : ℕ, gaussFam t ((m : ℕ) : ℤ) = gaussTerm t m := by
    intro m
    simp only [gaussFam, gaussTerm]
    push_cast
    ring
  have hsplit := tsum_int_eq_zero_add_two_mul_tsum_pnat heven hsumm
  rw [two_nsmul, ← two_mul] at hsplit
  have hpnat := tsum_pnat_eq_tsum_succ
    (f := fun (m : ℕ) => gaussFam t ((m : ℕ) : ℤ))
  have hfinal : ∑' (p : ℕ+), gaussFam t ((↑(p : ℕ) : ℕ) : ℤ) =
      ∑' (n : ℕ), gaussTerm t (n + 1) := by
    rw [hpnat]
    exact tsum_congr (fun n => by rw [hc (n + 1)])
  show ∑' (z : ℤ), gaussFam t z = 1 + 2 * ∑' (n : ℕ), gaussTerm t (n + 1)
  rw [hsplit, h0, hfinal]

/-- The two-sided theta carries its zero mode: `1 <= thetaT t` on the
time axis (the mirror of R233's private receipt, made public for the
Gaussian arm). -/
theorem thetaT_ge_one {t : ℝ} (ht : 0 < t) : 1 ≤ thetaT t := by
  rw [thetaT_splitG ht]
  have hS : 0 ≤ ∑' (n : ℕ), gaussTerm t (n + 1) :=
    tsum_nonneg (fun n => by simp only [gaussTerm]; positivity)
  linarith

/-- The two-sided theta is nonnegative on the time axis: it owns its
constant mode. -/
theorem thetaT_nonneg {t : ℝ} (ht : 0 < t) : 0 ≤ thetaT t := by
  have := thetaT_ge_one ht
  linarith

/-- The positive tail is a measurable object: the ℕ-tsum of measurable
exponentials (the `tailT_measurable` receipt, mirrored). -/
private theorem tailG_measurable :
    Measurable (fun (t : ℝ) => ∑' (n : ℕ), gaussTerm t (n + 1)) := by
  have h : ∀ (n : ℕ), Measurable (fun (t : ℝ) => gaussTerm t (n + 1)) := by
    intro n
    simp only [gaussTerm]
    fun_prop
  exact Measurable.tsum (f := fun (n : ℕ) (t : ℝ) => gaussTerm t (n + 1)) h

/-- The t-arm thetaFour is measurable, mirroring R235's private
`thetaFour_measurable` verbatim (same object, the alternating tsum of
powers of the nome, `Measurable.tsum` over the measurable exponentials;
certified green in this vintage). -/
private theorem thetaFour_measurable' : Measurable (thetaFour) := by
  have honexp : Measurable (fun t : ℝ => Real.exp (-Real.pi * t)) :=
    Real.measurable_exp.comp (measurable_const.mul measurable_id)
  have hsum : Measurable (fun t : ℝ => ∑' n : ℕ,
      (-1 : ℝ) ^ (n + 1) * Real.exp (-Real.pi * t) ^ ((n + 1) ^ 2)) := by
    refine Measurable.tsum
      (f := fun (n : ℕ) (t : ℝ) =>
        (-1 : ℝ) ^ (n + 1) * Real.exp (-Real.pi * t) ^ ((n + 1) ^ 2))
      (fun n => ?_)
    exact measurable_const.mul (honexp.pow_const ((n + 1) ^ 2))
  have heq : thetaFour
      = fun t : ℝ => 1 + 2 * ∑' n : ℕ,
        (-1 : ℝ) ^ (n + 1) * Real.exp (-Real.pi * t) ^ ((n + 1) ^ 2) := rfl
  rw [heq]
  exact measurable_const.add (measurable_const.mul hsum)

/-- The triangle law on the reals, `|a + b| <= |a| + |b|`, the honesty
lemma this vintage's `abs_add` absence forces us to carry. -/
private theorem abs_tri (a b : ℝ) : |a + b| ≤ |a| + |b| := by
  have ha1 : -|a| ≤ a := (abs_le.mp (le_refl (|a|))).1
  have hb1 : -|b| ≤ b := (abs_le.mp (le_refl (|b|))).1
  exact abs_le.mpr ⟨by nlinarith [ha1, hb1], by linarith [le_abs_self a, le_abs_self b]⟩

/-! ## The Gaussian-arm honest objects -/

/-- THE 1000 CHARACTER THETA (mask one): `Theta_1000 = thetaFour * thetaT^3`
on the time axis -- the four-torus lattice sum with the sign character
on the first coordinate. -/
noncomputable def gauss1000 (t : ℝ) : ℝ := thetaFour t * thetaT t ^ 3

/-- THE 1110 CHARACTER THETA (mask three):
`Theta_1110 = thetaFour^3 * thetaT` -- the sign character on the first
three coordinates. -/
noncomputable def gauss1110 (t : ℝ) : ℝ := thetaFour t ^ 3 * thetaT t

/-- The 1000 kernel is a.e. strongly measurable on any measurable set
lying in the positive time axis, through the value split (the R233
`kernel_aemeas` pattern: the kernel coincides on the set with a
measurable tail expression). -/
private theorem kernel1000_aemeas (s : Set ℝ) (ms : MeasurableSet s)
    (hs : ∀ t ∈ s, (0:ℝ) < t) :
    AEStronglyMeasurable (fun t => t * (gauss1000 t - 1))
      (MeasureTheory.volume.restrict s) := by
  have hmeas : Measurable (fun t => t *
      (thetaFour t * (1 + 2 * ∑' (n : ℕ), gaussTerm t (n + 1)) ^ 3 - 1)) := by
    refine measurable_id.mul ?_
    exact (thetaFour_measurable'.mul
      ((measurable_const.add (measurable_const.mul tailG_measurable)).pow_const 3)).sub
      measurable_const
  have hptwise : ∀ t ∈ s,
      t * (thetaFour t * (1 + 2 * ∑' (n : ℕ), gaussTerm t (n + 1)) ^ 3 - 1)
        = t * (gauss1000 t - 1) := by
    intro t ht'
    simp only [gauss1000]
    rw [thetaT_splitG (hs t ht')]
  exact hmeas.aestronglyMeasurable.congr
    (Filter.mem_of_superset (self_mem_ae_restrict ms) hptwise)

/-- The 1110 kernel's a.e. strong measurability, same pattern. -/
private theorem kernel1110_aemeas (s : Set ℝ) (ms : MeasurableSet s)
    (hs : ∀ t ∈ s, (0:ℝ) < t) :
    AEStronglyMeasurable (fun t => t * (gauss1110 t - 1))
      (MeasureTheory.volume.restrict s) := by
  have hmeas : Measurable (fun t => t *
      (thetaFour t ^ 3 * (1 + 2 * ∑' (n : ℕ), gaussTerm t (n + 1)) - 1)) := by
    refine measurable_id.mul ?_
    exact ((thetaFour_measurable'.pow_const 3).mul
      (measurable_const.add (measurable_const.mul tailG_measurable))).sub
      measurable_const
  have hptwise : ∀ t ∈ s,
      t * (thetaFour t ^ 3 * (1 + 2 * ∑' (n : ℕ), gaussTerm t (n + 1)) - 1)
        = t * (gauss1110 t - 1) := by
    intro t ht'
    simp only [gauss1110]
    rw [thetaT_splitG (hs t ht')]
  exact hmeas.aestronglyMeasurable.congr
    (Filter.mem_of_superset (self_mem_ae_restrict ms) hptwise)

/-- The difference kernel is a.e. strongly measurable on any measurable
set lying in the positive time axis, through the same value-split
pattern (both arms unfold to tail expressions). -/
private theorem kernelDiff_aemeas (s : Set ℝ) (ms : MeasurableSet s)
    (hs : ∀ t ∈ s, (0:ℝ) < t) :
    AEStronglyMeasurable (fun t => t * (gauss1000 t - gauss1110 t))
      (MeasureTheory.volume.restrict s) := by
  have hmeas : Measurable (fun t => t *
      (thetaFour t * (1 + 2 * ∑' (n : ℕ), gaussTerm t (n + 1)) ^ 3
        - thetaFour t ^ 3 * (1 + 2 * ∑' (n : ℕ), gaussTerm t (n + 1)))) := by
    refine measurable_id.mul ?_
    have htail : Measurable
        (fun (t : ℝ) => 1 + 2 * ∑' (n : ℕ), gaussTerm t (n + 1)) :=
      measurable_const.add (measurable_const.mul tailG_measurable)
    exact (thetaFour_measurable'.mul (htail.pow_const 3)).sub
      ((thetaFour_measurable'.pow_const 3).mul htail)
  have hptwise : ∀ t ∈ s,
      t * (thetaFour t * (1 + 2 * ∑' (n : ℕ), gaussTerm t (n + 1)) ^ 3
        - thetaFour t ^ 3 * (1 + 2 * ∑' (n : ℕ), gaussTerm t (n + 1)))
        = t * (gauss1000 t - gauss1110 t) := by
    intro t ht'
    simp only [gauss1000, gauss1110]
    rw [thetaT_splitG (hs t ht')]
  exact hmeas.aestronglyMeasurable.congr
    (Filter.mem_of_superset (self_mem_ae_restrict ms) hptwise)

/-! ## The numerics of the large arm -/

/-- `2 <= exp pi` through `3 + 1 <= exp 3` and `3 <= pi`. -/
private theorem exp_pi_ge_two : (2:ℝ) ≤ Real.exp (Real.pi) := by
  have h1 : (3:ℝ) + 1 ≤ Real.exp 3 := add_one_le_exp 3
  have h3 : (3:ℝ) ≤ Real.pi := by
    have h := pi_gt_three
    linarith
  have h2 : Real.exp 3 ≤ Real.exp (Real.pi) := Real.exp_le_exp.mpr h3
  have h4 : (2:ℝ) ≤ 3 + 1 := by norm_num
  linarith

/-- THE NOME LAW: on the large arm `exp (-pi * x) <= 1/2`. -/
private theorem expm_le_half {x : ℝ} (hx : (1:ℝ) ≤ x) :
    Real.exp (-(Real.pi) * x) ≤ 1 / 2 := by
  have hpix : Real.pi * 1 ≤ Real.pi * x :=
    mul_le_mul_of_nonneg_left hx Real.pi_pos.le
  rw [mul_one] at hpix
  have hp2 : Real.exp (Real.pi) ≤ Real.exp (Real.pi * x) :=
    Real.exp_le_exp.mpr hpix
  have h1 : (2:ℝ) ≤ Real.exp (Real.pi) := exp_pi_ge_two
  have h2 : (2:ℝ) ≤ Real.exp (Real.pi * x) := le_trans h1 hp2
  have hEpos : 0 < Real.exp (Real.pi * x) := Real.exp_pos _
  have hinv : Real.exp (-(Real.pi) * x) = (Real.exp (Real.pi * x))⁻¹ := by
    rw [← Real.exp_neg]
    congr 1
    ring
  rw [hinv, inv_eq_one_div,
    div_le_div_iff₀ hEpos (by norm_num : (0:ℝ) < 2), one_mul, one_mul]
  exact h2

/-- THE SHARPENED DECAY: on the large arm
`thetaT t <= 1 + 4 * exp (-pi*t)` -- the R233 geometric bound with the
nome capped at 1/2 (the quotient pays its factor: `2q/(1-q) <= 4q`). -/
private theorem thetaT_decay' {t : ℝ} (ht : (1:ℝ) ≤ t) :
    thetaT t ≤ 1 + 4 * Real.exp (-(Real.pi) * t) := by
  have hd := thetaT_decay ht
  have hEhalf := expm_le_half ht
  have hEpos : 0 < Real.exp (-(Real.pi) * t) := Real.exp_pos _
  have hstep : 2 * Real.exp (-(Real.pi) * t) / (1 - Real.exp (-(Real.pi) * t))
      ≤ 4 * Real.exp (-(Real.pi) * t) := by
    have hd0 : 0 < 1 - Real.exp (-(Real.pi) * t) := by linarith
    rw [div_le_iff₀ hd0]
    nlinarith [hEhalf, hEpos.le]
  have hsum : 1 + 2 * Real.exp (-(Real.pi) * t) / (1 - Real.exp (-(Real.pi) * t))
      ≤ 1 + 4 * Real.exp (-(Real.pi) * t) := by linarith
  linarith

/-- THE 1110 DEFICIT LAW on the large arm:
`|gauss1110 x - 1| <= 22 * exp (-pi*x)`. The thetaFour cube's deficit is
at most `6q` (the deficit `2q` times a quadratic form capped at 3, the
cube sandwich on `[-1, 1]`), the thetaT factor is at most 3, and
thetaT's own deficit is at most `4q`: `18q + 4q = 22q`. -/
private theorem gauss1110_deficit {x : ℝ} (hx0 : 0 < x) (hx1 : (1:ℝ) ≤ x) :
    |gauss1110 x - 1| ≤ 22 * Real.exp (-(Real.pi) * x) := by
  have hqhalf : Real.exp (-(Real.pi) * x) ≤ 1 / 2 := expm_le_half hx1
  have hT1 : 1 ≤ thetaT x := thetaT_ge_one hx0
  have hTu : thetaT x - 1 ≤ 4 * Real.exp (-(Real.pi) * x) := by
    have hθ := thetaT_decay' hx1
    linarith
  have hT3 : thetaT x ≤ 3 := by linarith
  have hT1n : 0 ≤ thetaT x - 1 := by linarith
  have hTn : 0 ≤ thetaT x := thetaT_nonneg hx0
  -- the thetaFour sandwich on the arm
  have habspow : |thetaFour x| ≤ 1 := abs_thetaFour_le_one hx0
  have hFu : thetaFour x ≤ 1 := (thetaFour_bounds hx0).1
  have hF2 : thetaFour x ^ 2 ≤ 1 := by
    have habs2 : |thetaFour x| * |thetaFour x| ≤ 1 * 1 :=
      mul_le_mul habspow habspow (abs_nonneg _) zero_le_one
    calc thetaFour x ^ 2 = |thetaFour x| ^ 2 := (sq_abs _).symm
      _ = |thetaFour x| * |thetaFour x| := pow_two _
      _ ≤ 1 * 1 := habs2
      _ = 1 := one_mul _
  have hqcap : thetaFour x ^ 2 + thetaFour x + 1 ≤ 3 := by nlinarith [hF2, hFu]
  have hqnon : 0 ≤ thetaFour x ^ 2 + thetaFour x + 1 := by
    have h := sq_nonneg (thetaFour x + 1 / 2)
    nlinarith [h]
  have hF41 : |thetaFour x - 1| ≤ 2 * Real.exp (-(Real.pi) * x) := by
    obtain ⟨hθ1, hdef⟩ := thetaFour_bounds hx0
    exact abs_le.mpr ⟨by linarith, by linarith⟩
  have hcub : |thetaFour x ^ 3 - 1| ≤ 6 * Real.exp (-(Real.pi) * x) := by
    have hfact : thetaFour x ^ 3 - 1 =
        (thetaFour x - 1) * (thetaFour x ^ 2 + thetaFour x + 1) := by ring
    rw [hfact, abs_mul, abs_of_nonneg hqnon]
    have hh := mul_le_mul hF41 hqcap hqnon (by positivity)
    linarith [hh]
  have hg : gauss1110 x - 1 =
      (thetaFour x ^ 3 - 1) * thetaT x + (thetaT x - 1) := by
    simp only [gauss1110]
    ring
  rw [hg]
  refine le_trans (abs_tri _ _) ?_
  rw [abs_mul, abs_of_nonneg hTn, abs_of_nonneg hT1n]
  have hcapb : |thetaFour x ^ 3 - 1| * thetaT x
      ≤ 18 * Real.exp (-(Real.pi) * x) := by
    have hA : |thetaFour x ^ 3 - 1| * thetaT x
        ≤ 6 * Real.exp (-(Real.pi) * x) * thetaT x :=
      mul_le_mul_of_nonneg_right hcub hTn
    have hB : 6 * Real.exp (-(Real.pi) * x) * thetaT x
        ≤ 18 * Real.exp (-(Real.pi) * x) := by
      have hC := mul_le_mul_of_nonneg_left hT3
        (by positivity : (0:ℝ) ≤ 6 * Real.exp (-(Real.pi) * x))
      linarith [hC]
    exact le_trans hA hB
  linarith [hcapb, hTu]

/-- THE 1000 DEFICIT LAW on the large arm:
`|gauss1000 x - 1| <= 54 * exp (-pi*x)`. The thetaT cube's deficit is at
most `52q` (deficit `4q` times a quadratic form capped at 13, from
thetaT bounded by 3), the thetaFour factor's deficit is at most `2q`:
`52q + 2q = 54q`. -/
private theorem gauss1000_deficit {x : ℝ} (hx0 : 0 < x) (hx1 : (1:ℝ) ≤ x) :
    |gauss1000 x - 1| ≤ 54 * Real.exp (-(Real.pi) * x) := by
  have hqhalf : Real.exp (-(Real.pi) * x) ≤ 1 / 2 := expm_le_half hx1
  have hT1 : 1 ≤ thetaT x := thetaT_ge_one hx0
  have hTu : thetaT x - 1 ≤ 4 * Real.exp (-(Real.pi) * x) := by
    have hθ := thetaT_decay' hx1
    linarith
  have hT3 : thetaT x ≤ 3 := by linarith
  have hT1n : 0 ≤ thetaT x - 1 := by linarith
  have hTn : 0 ≤ thetaT x := thetaT_nonneg hx0
  have habspow : |thetaFour x| ≤ 1 := abs_thetaFour_le_one hx0
  have hF41 : |thetaFour x - 1| ≤ 2 * Real.exp (-(Real.pi) * x) := by
    obtain ⟨hθ1, hdef⟩ := thetaFour_bounds hx0
    exact abs_le.mpr ⟨by linarith, by linarith⟩
  -- the thetaT cube: deficit and quadratic cap
  have hT2 : thetaT x ^ 2 ≤ 9 := by
    have h1 : 0 ≤ 3 - thetaT x := by linarith
    have h2 : 0 ≤ 3 + thetaT x := by linarith
    have h3 : (3 - thetaT x) * (3 + thetaT x) = 9 - thetaT x ^ 2 := by ring
    nlinarith [h1, h2, h3]
  have hqcapT : thetaT x ^ 2 + thetaT x + 1 ≤ 13 := by linarith [hT2, hT3]
  have hqnonT : 0 ≤ thetaT x ^ 2 + thetaT x + 1 := by
    have h := sq_nonneg (thetaT x + 1 / 2)
    nlinarith [h]
  have hT30 : 0 ≤ thetaT x ^ 3 - 1 := by
    have hfact : thetaT x ^ 3 - 1 =
        (thetaT x - 1) * (thetaT x ^ 2 + thetaT x + 1) := by ring
    rw [hfact]
    exact mul_nonneg hT1n hqnonT
  have hT31 : thetaT x ^ 3 - 1 ≤ 52 * Real.exp (-(Real.pi) * x) := by
    have hfact : thetaT x ^ 3 - 1 =
        (thetaT x - 1) * (thetaT x ^ 2 + thetaT x + 1) := by ring
    rw [hfact]
    have hh := mul_le_mul hTu hqcapT hqnonT (by positivity)
    linarith [hh]
  have hg : gauss1000 x - 1 =
      thetaFour x * (thetaT x ^ 3 - 1) + (thetaFour x - 1) := by
    simp only [gauss1000]
    ring
  rw [hg]
  refine le_trans (abs_tri _ _) ?_
  rw [abs_mul, abs_of_nonneg hT30]
  have hh : |thetaFour x| * (thetaT x ^ 3 - 1)
      ≤ 52 * Real.exp (-(Real.pi) * x) := by
    have hh2 := mul_le_mul hT31 habspow (abs_nonneg _) (by positivity)
    calc |thetaFour x| * (thetaT x ^ 3 - 1)
        = (thetaT x ^ 3 - 1) * |thetaFour x| := mul_comm _ _
      _ ≤ 52 * Real.exp (-(Real.pi) * x) * 1 := hh2
      _ = 52 * Real.exp (-(Real.pi) * x) := mul_one _
  linarith [hh, hF41]

/-! ## THE 1110 KERNEL: BOTH HALVES -/

/-- THE SMALL-T HALF: the 1110 kernel `t -> t * (gauss1110 t - 1)` is
integrable on `(0, 1]`. The kernel is not sign-definite, so the bound is
two-sided absolute value: the thetaFour cube lies in `[-1, 1]` (the
absolute sandwich cubed), so
`-3 <= t * (gauss1110 t - 1) <= 3` -- the upper side through the R233
blow-up law `thetaT <= 1 + t^{-1/2}` with `t * t^{-1/2} = sqrt t <= 1`,
the lower side through the same law read from below. A bounded kernel
on a finite volume. -/
theorem kernel1110_integrable_small :
    IntegrableOn (fun t => t * (gauss1110 t - 1)) (Ioc (0:ℝ) 1)
      MeasureTheory.volume := by
  have hvol : MeasureTheory.volume (Ioc (0:ℝ) 1) < ⊤ := by
    rw [volume_Ioc]
    simp
  have hbnd : ∀ x ∈ Ioc (0:ℝ) 1, ‖x * (gauss1110 x - 1)‖ ≤ 3 := by
    intro x hx
    have hx0 : 0 < x := (Set.mem_Ioc.mp hx).1
    have hx1 : x ≤ 1 := (Set.mem_Ioc.mp hx).2
    have hTn : 0 ≤ thetaT x := thetaT_nonneg hx0
    have hT := thetaT_blowup hx0 hx1
    -- the cube sandwich: thetaFour^3 in [-1, 1]
    have habspow : |thetaFour x| ≤ 1 := abs_thetaFour_le_one hx0
    have hF3 : thetaFour x ^ 3 ≤ 1 := by
      have hθ1 : thetaFour x ≤ 1 := (thetaFour_bounds hx0).1
      have hθn : -1 ≤ thetaFour x := by
        have h := abs_le.mp habspow
        linarith
      have hθp2 : thetaFour x ^ 2 ≤ 1 := by
        have habs2 : |thetaFour x| * |thetaFour x| ≤ 1 * 1 :=
          mul_le_mul habspow habspow (abs_nonneg _) zero_le_one
        calc thetaFour x ^ 2 = |thetaFour x| ^ 2 := (sq_abs _).symm
          _ = |thetaFour x| * |thetaFour x| := pow_two _
          _ ≤ 1 * 1 := habs2
          _ = 1 := one_mul _
      have hrw3 : thetaFour x ^ 3 = thetaFour x * thetaFour x ^ 2 := by ring
      rw [hrw3]
      have hc := mul_le_mul hθ1 hθp2 (sq_nonneg (thetaFour x)) zero_le_one
      rw [one_mul] at hc
      exact hc
    have hF3m : -1 ≤ thetaFour x ^ 3 := by
      have hcomp : 0 ≤ (thetaFour x + 1) * (thetaFour x ^ 2 - thetaFour x + 1) := by
        have hp1 : 0 ≤ thetaFour x + 1 := by
          have h := abs_le.mp habspow
          linarith
        have hp2 : 0 ≤ thetaFour x ^ 2 - thetaFour x + 1 := by
          have h := sq_nonneg (thetaFour x - 1 / 2)
          nlinarith [h]
        exact mul_nonneg hp1 hp2
      have hex : (thetaFour x + 1) * (thetaFour x ^ 2 - thetaFour x + 1)
          = thetaFour x ^ 3 + 1 := by ring
      linarith [hcomp, hex]
    -- the square-root receipts (R233's small-half arithmetic mirror)
    have hs0 : Real.sqrt x ≠ 0 := (Real.sqrt_pos.mpr hx0).ne'
    have h1x : x = Real.sqrt x * Real.sqrt x := (Real.mul_self_sqrt hx0.le).symm
    have key : x * (Real.sqrt x)⁻¹ = Real.sqrt x := by
      refine mul_left_cancel₀ hs0 ?_
      rw [mul_comm x, ← mul_assoc, mul_inv_cancel₀ hs0, one_mul]
      exact h1x
    have hsqrt1 : Real.sqrt x ≤ 1 := by
      have h2 := Real.sqrt_le_sqrt hx1
      rwa [Real.sqrt_one] at h2
    -- the upper side: kernel <= sqrt x <= 1 <= 3
    have hu : x * (gauss1110 x - 1) ≤ 3 := by
      have hgcap : gauss1110 x ≤ thetaT x := by
        simp only [gauss1110]
        calc thetaFour x ^ 3 * thetaT x ≤ 1 * thetaT x :=
              mul_le_mul_of_nonneg_right hF3 hTn
          _ = thetaT x := one_mul _
      have hA : x * (gauss1110 x - 1) ≤ x * (thetaT x - 1) :=
        mul_le_mul_of_nonneg_left (by linarith) hx0.le
      have hB : x * (thetaT x - 1) = x * thetaT x - x := by ring
      have hC : x * thetaT x ≤ x + Real.sqrt x := by
        calc x * thetaT x ≤ x * (1 + (Real.sqrt x)⁻¹) :=
              mul_le_mul_of_nonneg_left hT hx0.le
          _ = x + Real.sqrt x := by rw [mul_add, mul_one, key]
      nlinarith [hA, hB, hC, hsqrt1]
    -- the lower side: kernel >= -2x - sqrt x >= -3
    have hl : -(3:ℝ) ≤ x * (gauss1110 x - 1) := by
      have hglow : -(thetaT x) - 1 ≤ gauss1110 x - 1 := by
        have hAB : (-1:ℝ) * thetaT x ≤ thetaFour x ^ 3 * thetaT x := by
          have h := mul_le_mul_of_nonneg_right hF3m hTn
          linarith [h]
        have hgg : -(thetaT x) - 1 ≤ thetaFour x ^ 3 * thetaT x - 1 := by
          linarith [hAB]
        simp only [gauss1110]
        exact hgg
      have hA : x * (-(thetaT x) - 1) ≤ x * (gauss1110 x - 1) :=
        mul_le_mul_of_nonneg_left hglow hx0.le
      have hB : x * (-(thetaT x) - 1) = -(x * thetaT x) - x := by ring
      have hC : x * thetaT x ≤ x + Real.sqrt x := by
        calc x * thetaT x ≤ x * (1 + (Real.sqrt x)⁻¹) :=
              mul_le_mul_of_nonneg_left hT hx0.le
          _ = x + Real.sqrt x := by rw [mul_add, mul_one, key]
      have hE : x ≤ 1 := hx1
      nlinarith [hA, hB, hC, hsqrt1, hE]
    rw [Real.norm_eq_abs]
    exact abs_le.mpr ⟨hl, hu⟩
  exact IntegrableOn.of_bound hvol
    (kernel1110_aemeas (Ioc (0:ℝ) 1) measurableSet_Ioc
      (fun t ht => (Set.mem_Ioc.mp ht).1))
    3
    (Filter.mem_of_superset (self_mem_ae_restrict measurableSet_Ioc) hbnd)

/-- THE LARGE-T HALF of the 1110 kernel: integrable on `(1, inf)` by the
exponential route -- the deficit law caps `|gauss1110 t - 1|` by
`22 * exp (-pi*t)`, the dominator `22 * (t * exp (-t))` is integrable
by Mathlib's `integrableOn_rpow_mul_exp_neg_rpow` at `p = s = 1` (the
R235 receipt). -/
theorem kernel1110_integrable_large :
    IntegrableOn (fun t => t * (gauss1110 t - 1)) (Ioi (1:ℝ))
      MeasureTheory.volume := by
  have hbase := integrableOn_rpow_mul_exp_neg_rpow (s := (1:ℝ)) (p := (1:ℝ))
    (by norm_num) (by norm_num)
  have hsub : Ioi (1:ℝ) ⊆ Ioi (0:ℝ) :=
    fun x hx => lt_trans (by norm_num : (0:ℝ) < 1) hx
  have hbase1 : IntegrableOn (fun t => t * Real.exp (-t)) (Ioi (1:ℝ))
      MeasureTheory.volume := by
    refine (hbase.mono_set hsub).congr_fun ?_ measurableSet_Ioi
    intro t _
    simp only [Real.rpow_one]
  have hdom0 : MeasureTheory.Integrable
      (fun t => (22:ℝ) * (t * Real.exp (-t)))
      (MeasureTheory.volume.restrict (Ioi (1:ℝ))) :=
    MeasureTheory.Integrable.const_mul hbase1 22
  have hdom : ∀ x ∈ Ioi (1:ℝ),
      ‖x * (gauss1110 x - 1)‖ ≤ ‖(22:ℝ) * (x * Real.exp (-x))‖ := by
    intro x hx
    have hx1 : (1:ℝ) < x := Set.mem_Ioi.mp hx
    have hx0 : (0:ℝ) < x := by linarith
    have habsg := gauss1110_deficit hx0 hx1.le
    have hEexp : Real.exp (-(Real.pi) * x) ≤ Real.exp (-x) := by
      refine Real.exp_le_exp.mpr ?_
      have hpione : (1:ℝ) ≤ Real.pi := by
        have h := pi_gt_three
        linarith
      nlinarith [hpione, hx0]
    have hnn2 : 0 ≤ (22:ℝ) * (x * Real.exp (-x)) :=
      mul_nonneg (by norm_num) (by positivity)
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hnn2, abs_mul,
      abs_of_nonneg hx0.le]
    calc x * |gauss1110 x - 1| ≤ x * (22 * Real.exp (-(Real.pi) * x)) :=
          mul_le_mul_of_nonneg_left habsg hx0.le
      _ ≤ x * (22 * Real.exp (-x)) :=
          mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_left hEexp (by norm_num)) hx0.le
      _ = 22 * (x * Real.exp (-x)) := by ring
  exact MeasureTheory.Integrable.mono hdom0
    (kernel1110_aemeas (Ioi (1:ℝ)) measurableSet_Ioi
      (fun t ht => lt_trans (by norm_num : (0:ℝ) < 1) (Set.mem_Ioi.mp ht)))
    (Filter.mem_of_superset (self_mem_ae_restrict measurableSet_Ioi) hdom)

/-- THE TWO HALVES of the 1110 kernel together. -/
theorem kernel1110_integrable_union :
    IntegrableOn (fun t => t * (gauss1110 t - 1)) (Ioc (0:ℝ) 1 ∪ Ioi (1:ℝ))
      MeasureTheory.volume := by
  rw [integrableOn_union]
  exact ⟨kernel1110_integrable_small, kernel1110_integrable_large⟩

/-- THE FULL 1110 KERNEL'S INTEGRABILITY: the s = 2 Mellin kernel of the
1110 arm, `t -> t * (gauss1110 t - 1)`, is integrable on the whole
half-line `(0, inf)` -- the Gaussian arm's honest object EXISTS. Its
closed-form VALUE remains the named window (w2). -/
theorem kernel1110_integrable_full :
    IntegrableOn (fun t => t * (gauss1110 t - 1)) (Ioi (0:ℝ)) volume := by
  rw [← Ioc_union_Ioi_eq_Ioi (by norm_num : (0:ℝ) ≤ 1)]
  exact kernel1110_integrable_union

/-! ## THE 1000 KERNEL: the paid large half, the named small window -/

/-- THE LARGE-T HALF of the 1000 kernel: integrable on `(1, inf)` by the
same exponential route with the 1000 deficit law (54 in place of 22).
The large half is honest; the small half is the named window (w1), the
1000 arm's true obstruction. -/
theorem kernel1000_integrable_large :
    IntegrableOn (fun t => t * (gauss1000 t - 1)) (Ioi (1:ℝ))
      MeasureTheory.volume := by
  have hbase := integrableOn_rpow_mul_exp_neg_rpow (s := (1:ℝ)) (p := (1:ℝ))
    (by norm_num) (by norm_num)
  have hsub : Ioi (1:ℝ) ⊆ Ioi (0:ℝ) :=
    fun x hx => lt_trans (by norm_num : (0:ℝ) < 1) hx
  have hbase1 : IntegrableOn (fun t => t * Real.exp (-t)) (Ioi (1:ℝ))
      MeasureTheory.volume := by
    refine (hbase.mono_set hsub).congr_fun ?_ measurableSet_Ioi
    intro t _
    simp only [Real.rpow_one]
  have hdom0 : MeasureTheory.Integrable
      (fun t => (54:ℝ) * (t * Real.exp (-t)))
      (MeasureTheory.volume.restrict (Ioi (1:ℝ))) :=
    MeasureTheory.Integrable.const_mul hbase1 54
  have hdom : ∀ x ∈ Ioi (1:ℝ),
      ‖x * (gauss1000 x - 1)‖ ≤ ‖(54:ℝ) * (x * Real.exp (-x))‖ := by
    intro x hx
    have hx1 : (1:ℝ) < x := Set.mem_Ioi.mp hx
    have hx0 : (0:ℝ) < x := by linarith
    have habsg := gauss1000_deficit hx0 hx1.le
    have hEexp : Real.exp (-(Real.pi) * x) ≤ Real.exp (-x) := by
      refine Real.exp_le_exp.mpr ?_
      have hpione : (1:ℝ) ≤ Real.pi := by
        have h := pi_gt_three
        linarith
      nlinarith [hpione, hx0]
    have hnn2 : 0 ≤ (54:ℝ) * (x * Real.exp (-x)) :=
      mul_nonneg (by norm_num) (by positivity)
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hnn2, abs_mul,
      abs_of_nonneg hx0.le]
    calc x * |gauss1000 x - 1| ≤ x * (54 * Real.exp (-(Real.pi) * x)) :=
          mul_le_mul_of_nonneg_left habsg hx0.le
      _ ≤ x * (54 * Real.exp (-x)) :=
          mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_left hEexp (by norm_num)) hx0.le
      _ = 54 * (x * Real.exp (-x)) := by ring
  exact MeasureTheory.Integrable.mono hdom0
    (kernel1000_aemeas (Ioi (1:ℝ)) measurableSet_Ioi
      (fun t ht => lt_trans (by norm_num : (0:ℝ) < 1) (Set.mem_Ioi.mp ht)))
    (Filter.mem_of_superset (self_mem_ae_restrict measurableSet_Ioi) hdom)

/-! ## THE DIFFERENCE SPINE, opened -/

/-- THE ANTISYMMETRIC FACTORED FORM of the difference, the ring identity
at the heart of the Z[i] spine:
`gauss1000 t - gauss1110 t = thetaFour t * thetaT t * (thetaT t ^ 2 - thetaFour t ^ 2)`.
The `chi_{-4}` reindexing of this spine into `r_2(n) = 4 * zeta(s) *
L(s, chi_{-4})` is the named window behind it. -/
theorem gauss1000_sub_gauss1110_eq (t : ℝ) :
    gauss1000 t - gauss1110 t
      = thetaFour t * thetaT t * (thetaT t ^ 2 - thetaFour t ^ 2) := by
  simp only [gauss1000, gauss1110]
  ring

/-- THE DIFFERENCE KERNEL on the large half: integrable on `(1, inf)`.
Both deficit laws cap the difference by `54q + 22q = 76q`, the same
exponential dominator with 76 in place. This is the honest first stone
of the difference spine's s = 2 convergence. -/
theorem kernelDiff_integrable_large :
    IntegrableOn (fun t => t * (gauss1000 t - gauss1110 t)) (Ioi (1:ℝ))
      MeasureTheory.volume := by
  have hbase := integrableOn_rpow_mul_exp_neg_rpow (s := (1:ℝ)) (p := (1:ℝ))
    (by norm_num) (by norm_num)
  have hsub : Ioi (1:ℝ) ⊆ Ioi (0:ℝ) :=
    fun x hx => lt_trans (by norm_num : (0:ℝ) < 1) hx
  have hbase1 : IntegrableOn (fun t => t * Real.exp (-t)) (Ioi (1:ℝ))
      MeasureTheory.volume := by
    refine (hbase.mono_set hsub).congr_fun ?_ measurableSet_Ioi
    intro t _
    simp only [Real.rpow_one]
  have hdom0 : MeasureTheory.Integrable
      (fun t => (76:ℝ) * (t * Real.exp (-t)))
      (MeasureTheory.volume.restrict (Ioi (1:ℝ))) :=
    MeasureTheory.Integrable.const_mul hbase1 76
  have hdom : ∀ x ∈ Ioi (1:ℝ),
      ‖x * (gauss1000 x - gauss1110 x)‖ ≤ ‖(76:ℝ) * (x * Real.exp (-x))‖ := by
    intro x hx
    have hx1 : (1:ℝ) < x := Set.mem_Ioi.mp hx
    have hx0 : (0:ℝ) < x := by linarith
    have habsg1 := gauss1000_deficit hx0 hx1.le
    have habsg2 := gauss1110_deficit hx0 hx1.le
    have hEexp : Real.exp (-(Real.pi) * x) ≤ Real.exp (-x) := by
      refine Real.exp_le_exp.mpr ?_
      have hpione : (1:ℝ) ≤ Real.pi := by
        have h := pi_gt_three
        linarith
      nlinarith [hpione, hx0]
    have h1 : |gauss1000 x - gauss1110 x|
        ≤ |gauss1000 x - 1| + |gauss1110 x - 1| := by
      have hrw : gauss1000 x - gauss1110 x
          = (gauss1000 x - 1) - (gauss1110 x - 1) := by ring
      rw [hrw, sub_eq_add_neg]
      have htri := abs_tri ((gauss1000 x) - 1) (-(gauss1110 x - 1))
      rwa [abs_neg] at htri
    have h2 : |gauss1000 x - gauss1110 x|
        ≤ 76 * Real.exp (-(Real.pi) * x) := by
      linarith [habsg1, habsg2, h1]
    have hnn2 : 0 ≤ (76:ℝ) * (x * Real.exp (-x)) :=
      mul_nonneg (by norm_num) (by positivity)
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hnn2, abs_mul,
      abs_of_nonneg hx0.le]
    calc x * |gauss1000 x - gauss1110 x|
        ≤ x * (76 * Real.exp (-(Real.pi) * x)) :=
          mul_le_mul_of_nonneg_left h2 hx0.le
      _ ≤ x * (76 * Real.exp (-x)) :=
          mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_left hEexp (by norm_num)) hx0.le
      _ = 76 * (x * Real.exp (-x)) := by ring
  exact MeasureTheory.Integrable.mono hdom0
    (kernelDiff_aemeas (Ioi (1:ℝ)) measurableSet_Ioi
      (fun t ht => lt_trans (by norm_num : (0:ℝ) < 1) (Set.mem_Ioi.mp ht)))
    (Filter.mem_of_superset (self_mem_ae_restrict measurableSet_Ioi) hdom)

/-! ## The honest objects (Theorem B floor): ZAdic1110, ZAdic1000 -/

/-- THE 1110 ARM'S HONEST OBJECT: the book's s = 2 normalization of the
1110 arm,
`ZAdic1110 = pi^2 * integral over (0, inf) of t * (gauss1110 t - 1)`.
The integral EXISTS by `kernel1110_integrable_full`; the closed-form
VALUE `-pi * G - (pi^2/24) * log 2` is the named window (w2), not
claimed here. -/
noncomputable def ZAdic1110 : ℝ :=
  Real.pi ^ 2 * ∫ x in Ioi (0:ℝ), x * (gauss1110 x - 1) ∂MeasureTheory.volume

/-- THE 1000 ARM'S HONEST OBJECT (formal, guarded by window w1):
`ZAdic1000 = pi^2 * integral over (0, inf) of t * (gauss1000 t - 1)`.
Its defining integral's CONVERGENCE is not claimed this window -- the
large half is paid (`kernel1000_integrable_large`), the small half is
window (w1) behind the thetaFour small-t death. The object stands
formally; the value is window (w2). -/
noncomputable def ZAdic1000 : ℝ :=
  Real.pi ^ 2 * ∫ x in Ioi (0:ℝ), x * (gauss1000 x - 1) ∂MeasureTheory.volume

end YangMills.DualBook

/-!
  REMAINDERS, honest and named (pre-registered for R237+):
  (w1) kernel1000_integrable_small -- attack routes: the half-lattice
       Poisson stone (order 1113's flagged IF), the Landen route
       thetaT t * thetaFour t = thetaFour (2*t) ^ 2.
  (w2) Z_1000(2) = pi*G - (pi^2/24)*log 2,  Z_1110(2) = -pi*G - (pi^2/24)*log 2.
  (w3) D1' sum bridge Theta_1000 + Theta_1110 = 2*Theta_1111(q^4).
  Bench frozen at 100.0. Scope: THIS ARITHMETIC only.
-/