/-
  PROVENANCE: YangMills.DualBook.ThetaIntegrabilityWindow (R233)
  Built by Gen, Papa's hands only, in the R233 window (Wed 2026-11-25 CT),
  opened at Papa's word after his own hand certified the R5 assembly layer
  (commit ee06e6f live on master, 5,824 green, all seven declarations on the
  three standard axioms). The preregistration (order 1102, struck upon at
  c1616) named this window's build: the first genuinely analytic rung of W1,
  the INTEGRABILITY LAYER of the real theta on the Mellin normalization's
  route.
  SCOPE: THIS ARITHMETIC only. The object: the real two-sided theta
    thetaT t = ∑' z : ℤ, exp (−π·t·z²)  (the classical θ₃ at nome exp(−πt)),
  its well-definedness for t > 0, the BLOW-UP LAW Θ(t) ≤ 1 + t^(−1/2) on
  (0,1] (via Mathlib's `integral_gaussian_Ioi` value at the half-line
  gaussian and the antitone integral test `AntitoneOn.tsum_le_integral`),
  the DECAY LAW on [1,∞) (geometric domination, `tsum_geometric_of_lt_one`),
  and THE S=2 MELLIN KERNEL INTEGRABILITY on both halves:
    t ↦ t ^ (2−1) · (Θ(t) − 1),  the honest kernel of the R69 normalization
    Z_σ(s) = [π^s/Γ(s)] ∫₀^∞ t^(s−1) (Θ_σ − 1) dt at s = 2,
  integrable on (0,1] by the blow-up bound-of-one receipt and on (1,∞) by
  the exponential decay dominator (`integrableOn_rpow_mul_exp_neg_rpow` at
  p = s = 1, the rate folded to e^(−t) since π ≥ 1).
  NOTHING ELSE IS CLAIMED. The Epstein closed-form evaluations themselves,
  the Poisson small-t layer, the E1 large-t layer, and the full Mellin
  integral evaluation REMAIN NAMED WINDOWS, never claimed here. No
  functional equation, no analytic continuation, no Clay claim of any
  kind; the bench stays frozen. The theta-bridge to the book's own theta3z
  rides the L1a window (R216, paid in the book); this module re-proves
  nothing from the book.
-/
import Mathlib.Analysis.SumIntegralComparisons
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Algebra.Order.GroupWithZero.Basic
import Mathlib.Analysis.Real.Pi.Bounds
import YangMills.DualBook.CatalanGateWindow

namespace YangMills.DualBook

open MeasureTheory Real Set

/-! ## The real theta and its well-definedness -/

/-- The real theta of the Mellin route: the two-sided integer theta
`thetaT t = ∑' z : ℤ, exp (−π·t·z²)`, the classical θ₃ at nome `exp (−πt)`.
Every term is positive; the family is summable for every `t > 0`
(`thetaT_summable` below), so the object is well-defined there. -/
noncomputable def thetaT (t : ℝ) : ℝ := ∑' (z : ℤ), Real.exp (-Real.pi * t * (z : ℝ) ^ 2)

/-- The integer family of `thetaT` as a function on ℤ. -/
private noncomputable def thetaFam (t : ℝ) (z : ℤ) : ℝ :=
  Real.exp (-Real.pi * t * (z : ℝ) ^ 2)

/-- The same family's natural face: exp (−π·t·n²) for n : ℕ. -/
private noncomputable def thetaTerm (t : ℝ) (n : ℕ) : ℝ :=
  Real.exp (-Real.pi * t * (n : ℝ) ^ 2)

/-- The real face of the family, `fun x => exp (−(π·t)·x²)`, used for the
integral test (antitone on `[0,∞)`, integrable, nonnegative). The
coefficient is spelled to match Mathlib's gaussian receipt exactly. -/
private noncomputable def thetaFace (t : ℝ) (x : ℝ) : ℝ :=
  Real.exp (-(Real.pi * t) * x ^ 2)

private theorem thetaFace_nonneg (t x : ℝ) : 0 ≤ thetaFace t x := by
  simp only [thetaFace]
  positivity

/-- The real face is antitone on `[0, ∞)`: squares order and the exponential
is antitone. -/
private theorem thetaFace_antitone (t : ℝ) (ht : 0 < t) :
    AntitoneOn (thetaFace t) (Set.Ici 0) := by
  intro x hx y hy hxy
  simp only [Set.mem_Ici] at hx hy
  have hsq : x * x ≤ y * y := by nlinarith [hxy, hx, hy]
  have hpt : 0 ≤ Real.pi * t := by positivity
  have hmul := mul_le_mul_of_nonneg_left hsq hpt
  refine Real.exp_le_exp.mpr ?_
  linarith [hmul]

/-- The real face is integrable on `(0, ∞)`: Mathlib's gaussian receipt
`integrable_exp_neg_mul_sq` at the positive coefficient `π·t`. -/
private theorem thetaFace_integrable {t : ℝ} (ht : 0 < t) :
    IntegrableOn (thetaFace t) (Set.Ioi 0) MeasureTheory.volume := by
  have h : MeasureTheory.Integrable (fun x => Real.exp (-(Real.pi * t) * x ^ 2))
      MeasureTheory.volume :=
    integrable_exp_neg_mul_sq (by positivity)
  exact h.integrableOn

/-- The natural face is summable, by the integral test on the real face. -/
private theorem thetaTerm_summable {t : ℝ} (ht : 0 < t) :
    Summable (thetaTerm t) := by
  have h := AntitoneOn.summable_of_integrableOn_Ioi_zero (thetaFace_antitone t ht)
    (thetaFace_integrable ht) (fun x _ => thetaFace_nonneg t x)
  exact h.congr (fun n => by simp only [thetaFace, thetaTerm]; congr 1; ring)

/-- WELL-DEFINEDNESS: the integer family is summable for every `t > 0`, the
integral test on the natural face plus the even-family ℕ/−ℕ split. -/
theorem thetaT_summable {t : ℝ} (ht : 0 < t) : Summable (thetaFam t) := by
  have h1 : Summable fun n : ℕ => thetaTerm t n := thetaTerm_summable ht
  refine Summable.of_nat_of_neg ?_ ?_
  · refine h1.congr (fun n => by
      simp only [thetaTerm, thetaFam]
      exact_mod_cast rfl)
  · refine h1.congr (fun n => by
      simp only [thetaTerm, thetaFam]
      congr 1
      push_cast
      ring)

/-! ## The value split: Θ(t) = 1 + 2 · ∑'_{n ≥ 1} exp (−πtn²) -/

/-- The value split: `thetaT t = 1 + 2 * ∑' n, exp (−π·t·(n+1)²)`, the
two-sided theta as the constant 1 plus twice the positive tail. Rides the
`tsum_int_eq_zero_add_two_mul_tsum_pnat` twin split (the family is even) and
`tsum_pnat_eq_tsum_succ` for the ℕ+ face. -/
private theorem thetaT_split {t : ℝ} (ht : 0 < t) :
    thetaT t = 1 + 2 * ∑' (n : ℕ), thetaTerm t (n + 1) := by
  have heven : Function.Even (thetaFam t) := by
    intro z
    simp only [thetaFam]
    congr 1
    push_cast
    ring
  have h0 : thetaFam t 0 = 1 := by simp only [thetaFam]; norm_num
  have hc : ∀ m : ℕ, thetaFam t ((m : ℕ) : ℤ) = thetaTerm t m := by
    intro m
    simp only [thetaFam, thetaTerm]
    push_cast
    ring
  have hsplit := tsum_int_eq_zero_add_two_mul_tsum_pnat heven (thetaT_summable ht)
  rw [two_nsmul, ← two_mul] at hsplit
  have hpnat := tsum_pnat_eq_tsum_succ
    (f := fun (m : ℕ) => thetaFam t ((m : ℕ) : ℤ))
  have hfinal : ∑' (p : ℕ+), thetaFam t ((↑(p : ℕ) : ℕ) : ℤ) =
      ∑' (n : ℕ), thetaTerm t (n + 1) := by
    rw [hpnat]
    exact tsum_congr (fun n => by rw [hc (n + 1)])
  show ∑' (z : ℤ), thetaFam t z = 1 + 2 * ∑' (n : ℕ), thetaTerm t (n + 1)
  rw [hsplit, h0, hfinal]

/-- The theta is a measurable object through its positive tail: the ℕ-tsum
`fun t => ∑' n, thetaTerm t (n + 1)` is measurable, a countable tsum of
measurable exponentials (`Measurable.tsum`, the ℕ family; the kernel
restricts to these coordinates via the value split, so the ℤ-tsum itself
is never unfolded for measurability). -/
private theorem tailT_measurable :
    Measurable (fun (t : ℝ) => ∑' (n : ℕ), thetaTerm t (n + 1)) := by
  have h : ∀ (n : ℕ), Measurable (fun (t : ℝ) => thetaTerm t (n + 1)) := by
    intro n
    simp only [thetaTerm]
    fun_prop
  exact Measurable.tsum (f := fun (n : ℕ) => fun (t : ℝ) => thetaTerm t (n + 1)) h

/-- The s = 2 Mellin kernel is strongly measurable on any measurable set
where the split's hypothesis `0 < t` holds everywhere: on such a set the
kernel coincides pointwise with `t ↦ t · (2 · ∑' n, exp (−πt(n+1)²))`, a
measurable expression by `tailT_measurable`. -/
private theorem kernel_aemeas (s : Set ℝ) (ms : MeasurableSet s)
    (hs : ∀ t ∈ s, (0:ℝ) < t) :
    AEStronglyMeasurable (fun t => t * (thetaT t - 1))
      (MeasureTheory.volume.restrict s) := by
  have hmeas : Measurable (fun t => t * (2 * ∑' (n : ℕ), thetaTerm t (n + 1))) :=
    measurable_id.mul (measurable_const.mul tailT_measurable)
  have hptwise : ∀ t ∈ s,
      t * (2 * ∑' (n : ℕ), thetaTerm t (n + 1)) = t * (thetaT t - 1) := by
    intro t ht'
    rw [thetaT_split (hs t ht')]
    ring
  exact hmeas.aestronglyMeasurable.congr
    (Filter.mem_of_superset (self_mem_ae_restrict ms) hptwise)

/-! ## The blow-up law: Θ(t) ≤ 1 + t^(−1/2) on (0, 1] -/

/-- The 1/√t normalization of the gaussian constant: the π cancels. -/
private theorem sqrt_pi_div (t : ℝ) (ht : 0 < t) :
    Real.sqrt (Real.pi / (Real.pi * t)) = (Real.sqrt t)⁻¹ := by
  have hsp : Real.sqrt Real.pi ≠ 0 := (Real.sqrt_pos.mpr Real.pi_pos).ne'
  rw [sqrt_div (by positivity), Real.sqrt_mul (by positivity), div_eq_mul_inv,
    mul_inv, ← mul_assoc, mul_inv_cancel₀ hsp, one_mul]

/-- THE BLOW-UP LAW: for `0 < t ≤ 1` the theta obeys `Θ(t) ≤ 1 + t^(−1/2)`,
the small-t half of the s-split's engine. The positive tail is bounded by the
half-line gaussian value (∫₀^∞ exp (−πt x²) dx = 1/(2√t)) through the
antitone integral test. -/
theorem thetaT_blowup {t : ℝ} (ht : 0 < t) (ht1 : t ≤ 1) :
    thetaT t ≤ 1 + (Real.sqrt t)⁻¹ := by
  have hnum := AntitoneOn.tsum_le_integral (thetaFace_antitone t ht)
    (thetaFace_integrable ht) (fun x _ => thetaFace_nonneg t x)
  have hcongr : ∑' (n : ℕ), thetaTerm t n = ∑' (n : ℕ), thetaFace t (n : ℝ) :=
    tsum_congr (fun n => by simp only [thetaTerm, thetaFace]; congr 1; ring)
  rw [← hcongr] at hnum
  simp only [thetaFace] at hnum
  rw [integral_gaussian_Ioi, sqrt_pi_div t ht] at hnum
  have hz : Real.exp (-(Real.pi * t) * (0:ℝ) ^ 2) = 1 := by simp
  rw [hz] at hnum
  have h0 : thetaTerm t 0 = 1 := by simp only [thetaTerm]; norm_num
  have htail := (thetaTerm_summable ht).tsum_eq_zero_add
  rw [h0] at htail
  have hS : ∑' (n : ℕ), thetaTerm t (n + 1) ≤ (Real.sqrt t)⁻¹ / 2 := by
    linarith
  rw [thetaT_split ht]
  linarith

/-! ## The decay law: Θ(t) ≤ 1 + 2·q/(1−q) with q = exp (−πt), on [1, ∞) -/

/-- THE DECAY LAW: for `1 ≤ t` the theta obeys the geometric bound
`Θ(t) ≤ 1 + 2q/(1−q)` with `q = exp (−πt)`: the tail is dominated by the
shifted geometric series at ratio `q < 1`. -/
theorem thetaT_decay {t : ℝ} (ht1 : (1:ℝ) ≤ t) :
    thetaT t ≤ 1 + 2 * Real.exp (-(Real.pi) * t) / (1 - Real.exp (-(Real.pi) * t)) := by
  have ht : 0 < t := by linarith
  have hq0 : 0 < Real.exp (-(Real.pi) * t) := Real.exp_pos _
  have hq1 : Real.exp (-(Real.pi) * t) < 1 := by
    have h1 : Real.exp (-(Real.pi) * t) < Real.exp (0:ℝ) :=
      Real.exp_lt_exp.mpr (by nlinarith [Real.pi_pos, ht])
    simpa using h1
  have hpt : ∀ n : ℕ, thetaTerm t (n + 1) ≤ Real.exp (-(Real.pi) * t) ^ (n + 1) := by
    intro n
    have hn1 : (1:ℝ) ≤ ((n + 1 : ℕ) : ℝ) := by
      have h2 : ((1:ℕ) : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := Nat.cast_le.mpr (by omega)
      simpa using h2
    have hsq : ((n + 1 : ℕ) : ℝ) ≤ ((n + 1 : ℕ) : ℝ) ^ 2 := by nlinarith [hn1]
    have hmono : Real.exp (-Real.pi * t * ((n + 1 : ℕ) : ℝ) ^ 2) ≤
        Real.exp (-(Real.pi * t) * ((n + 1 : ℕ) : ℝ)) := by
      refine Real.exp_le_exp.mpr ?_
      have hkey : Real.pi * t * ((n + 1 : ℕ) : ℝ) ≤
          Real.pi * t * ((n + 1 : ℕ) : ℝ) ^ 2 :=
        mul_le_mul_of_nonneg_left hsq (by positivity)
      nlinarith [hkey]
    have hpow : Real.exp (-(Real.pi * t) * ((n + 1 : ℕ) : ℝ)) =
        Real.exp (-(Real.pi) * t) ^ (n + 1) := by
      rw [← Real.exp_natCast_mul]
      congr 1
      ring
    simp only [thetaTerm]
    rw [← hpow]
    exact hmono
  have hsumtail : Summable (fun n : ℕ => thetaTerm t (n + 1)) :=
    (summable_nat_add_iff 1).mpr (thetaTerm_summable ht)
  have hgeom : Summable (fun n : ℕ => Real.exp (-(Real.pi) * t) ^ n) :=
    summable_geometric_of_lt_one hq0.le hq1
  have hsum2 : Summable (fun n : ℕ => Real.exp (-(Real.pi) * t) ^ (n + 1)) :=
    (summable_nat_add_iff 1).mpr hgeom
  have hle := Summable.tsum_le_tsum hpt hsumtail hsum2
  have hval : ∑' (n : ℕ), Real.exp (-(Real.pi) * t) ^ (n + 1) =
      Real.exp (-(Real.pi) * t) * (1 - Real.exp (-(Real.pi) * t))⁻¹ := by
    have hcong2 : ∀ n : ℕ, Real.exp (-(Real.pi) * t) ^ (n + 1) =
        Real.exp (-(Real.pi) * t) * Real.exp (-(Real.pi) * t) ^ n := fun n => by
      ring
    rw [tsum_congr hcong2]
    have h1 := hgeom.tsum_mul_left (Real.exp (-(Real.pi) * t))
    rw [h1, tsum_geometric_of_lt_one hq0.le hq1]
  have hS := hle.trans_eq hval
  rw [thetaT_split ht, div_eq_mul_inv]
  have hrw : 2 * Real.exp (-(Real.pi) * t) * (1 - Real.exp (-(Real.pi) * t))⁻¹ =
      2 * (Real.exp (-(Real.pi) * t) * (1 - Real.exp (-(Real.pi) * t))⁻¹) := by ring
  rw [hrw]
  linarith

/-! ## The s = 2 Mellin kernel integrability, both halves -/

private theorem thetaT_ge_one {t : ℝ} (ht : 0 < t) : 1 ≤ thetaT t := by
  rw [thetaT_split ht]
  have hS : 0 ≤ ∑' (n : ℕ), thetaTerm t (n + 1) :=
    tsum_nonneg (fun n => by simp only [thetaTerm]; positivity)
  linarith

/-- THE SMALL-T HALF: the `s = 2` Mellin kernel `t ↦ t · (Θ(t) − 1)` is
integrable on `(0, 1]`. The kernel is nonnegative there (the theta owns its
constant 1) and bounded by √t ≤ 1 via the blow-up law: the honest small-t
half of `Z_σ(2)`'s convergence, paid on the R69 normalization's own route. -/
theorem mellin_s2_half_small :
    IntegrableOn (fun t => t * (thetaT t - 1)) (Ioc (0:ℝ) 1) MeasureTheory.volume := by
  have hvol : MeasureTheory.volume (Ioc (0:ℝ) 1) < ⊤ := by
    rw [volume_Ioc]
    simp
  have hbnd : ∀ x ∈ Ioc (0:ℝ) 1, ‖x * (thetaT x - 1)‖ ≤ 1 := by
    intro x hx
    have hx0 : 0 < x := (Set.mem_Ioc.mp hx).1
    have hx1 : x ≤ 1 := (Set.mem_Ioc.mp hx).2
    have hge : 1 ≤ thetaT x := thetaT_ge_one hx0
    have hnn : 0 ≤ x * (thetaT x - 1) := mul_nonneg hx0.le (by linarith)
    rw [Real.norm_eq_abs, abs_of_nonneg hnn]
    have hle := thetaT_blowup hx0 hx1
    have hb : x * (thetaT x - 1) ≤ x * (Real.sqrt x)⁻¹ :=
      mul_le_mul_of_nonneg_left (by linarith) hx0.le
    have hs0 : Real.sqrt x ≠ 0 := (Real.sqrt_pos.mpr hx0).ne'
    have h1 : x = Real.sqrt x * Real.sqrt x := (Real.mul_self_sqrt hx0.le).symm
    have key : x * (Real.sqrt x)⁻¹ = Real.sqrt x := by
      refine mul_left_cancel₀ hs0 ?_
      rw [mul_comm x, ← mul_assoc, mul_inv_cancel₀ hs0, one_mul]
      exact h1
    have hsqrt1 : Real.sqrt x ≤ 1 := by
      have h2 := Real.sqrt_le_sqrt hx1
      rwa [Real.sqrt_one] at h2
    exact (hb.trans_eq key).trans hsqrt1
  exact IntegrableOn.of_bound hvol
    (kernel_aemeas (Ioc (0:ℝ) 1) measurableSet_Ioc (fun t ht => (Set.mem_Ioc.mp ht).1)) 1
    (Filter.mem_of_superset (self_mem_ae_restrict measurableSet_Ioc) hbnd)

/-- THE LARGE-T HALF: the `s = 2` Mellin kernel is integrable on `(1, ∞)`.
The decay law gives `Θ(t) − 1 ≤ 2q/(1−q)` with `q = exp (−πt) ≤ exp (−t)`
(since π ≥ 1), so the kernel is dominated by
`(2/(1 − e^{−π})) · t · e^{−t}` on `(1, ∞)`, itself integrable by Mathlib's
`integrableOn_rpow_mul_exp_neg_rpow` at `p = s = 1`. The honest large-t half of `Z_σ(2)`'s convergence. -/
theorem mellin_s2_half_large :
    IntegrableOn (fun t => t * (thetaT t - 1)) (Ioi (1:ℝ)) MeasureTheory.volume := by
  have hCexp : Real.exp (-Real.pi) < 1 := by
    have h : Real.exp (-Real.pi) < Real.exp (0:ℝ) :=
      Real.exp_lt_exp.mpr (by nlinarith [Real.pi_pos])
    rwa [Real.exp_zero] at h
  have hCpos : 0 < 1 - Real.exp (-Real.pi) := by linarith
  have hpione : (1:ℝ) ≤ Real.pi := by
    have h := pi_gt_three
    linarith
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
      (fun t => (2 / (1 - Real.exp (-Real.pi))) * (t * Real.exp (-t)))
      (MeasureTheory.volume.restrict (Ioi (1:ℝ))) :=
    MeasureTheory.Integrable.const_mul hbase1 (2 / (1 - Real.exp (-Real.pi)))
  have hC2 : (0:ℝ) < 2 / (1 - Real.exp (-Real.pi)) := div_pos (by norm_num) hCpos
  have hdom : ∀ x ∈ Ioi (1:ℝ),
      ‖x * (thetaT x - 1)‖ ≤ ‖(2 / (1 - Real.exp (-Real.pi))) * (x * Real.exp (-x))‖ := by
    intro x hx
    have hx1 : (1:ℝ) < x := Set.mem_Ioi.mp hx
    have hx0 : (0:ℝ) < x := by linarith
    have hge : 1 ≤ thetaT x := thetaT_ge_one hx0
    have hnn1 : 0 ≤ x * (thetaT x - 1) := mul_nonneg hx0.le (by linarith)
    have hnn2 : 0 ≤ (2 / (1 - Real.exp (-Real.pi))) * (x * Real.exp (-x)) :=
      mul_nonneg hC2.le (by positivity)
    rw [Real.norm_eq_abs, abs_of_nonneg hnn1, Real.norm_eq_abs, abs_of_nonneg hnn2]
    have hle := thetaT_decay (le_of_lt hx1)
    have hqp : 0 < Real.exp (-(Real.pi) * x) := Real.exp_pos _
    have hque : Real.exp (-(Real.pi) * x) ≤ Real.exp (-x) := by
      refine Real.exp_le_exp.mpr ?_
      nlinarith [hpione, hx0]
    have hqt : Real.exp (-(Real.pi) * x) ≤ Real.exp (-Real.pi) := by
      refine Real.exp_le_exp.mpr ?_
      nlinarith [Real.pi_pos, hx1]
    have hd1 : 1 - Real.exp (-Real.pi) ≤ 1 - Real.exp (-(Real.pi) * x) := by linarith
    have hd1pos : 0 < 1 - Real.exp (-(Real.pi) * x) := by linarith
    have hmid : thetaT x - 1 ≤
        2 * Real.exp (-(Real.pi) * x) / (1 - Real.exp (-(Real.pi) * x)) := by linarith
    have hdiv : 2 * Real.exp (-(Real.pi) * x) / (1 - Real.exp (-(Real.pi) * x)) ≤
        2 * Real.exp (-x) / (1 - Real.exp (-Real.pi)) := by
      rw [div_le_div_iff₀ hd1pos hCpos]
      have h2qe : 2 * Real.exp (-(Real.pi) * x) ≤ 2 * Real.exp (-x) := by linarith
      exact mul_le_mul h2qe hd1 hCpos.le (by positivity)
    have hfull : thetaT x - 1 ≤ 2 * Real.exp (-x) / (1 - Real.exp (-Real.pi)) :=
      hmid.trans hdiv
    have hxx : x * (thetaT x - 1) ≤ x * (2 * Real.exp (-x) / (1 - Real.exp (-Real.pi))) :=
      mul_le_mul_of_nonneg_left hfull hx0.le
    have hE : x * (2 * Real.exp (-x) / (1 - Real.exp (-Real.pi))) =
        (2 / (1 - Real.exp (-Real.pi))) * (x * Real.exp (-x)) := by ring
    exact hxx.trans_eq hE
  exact MeasureTheory.Integrable.mono hdom0
    (kernel_aemeas (Ioi (1:ℝ)) measurableSet_Ioi
      (fun t ht => lt_trans (by norm_num : (0:ℝ) < 1) (Set.mem_Ioi.mp ht)))
    (Filter.mem_of_superset (self_mem_ae_restrict measurableSet_Ioi) hdom)

/-- THE CAPSTONE: the `s = 2` Mellin kernel of the R69 normalization is
integrable on both halves of the honest split, `(0, 1]` and `(1, ∞)`. The two
deep analytic grafts of R5 (the Epstein closed-form evaluations, the full
Mellin integral evaluation) remain named windows beyond this receipt. -/
theorem mellin_s2_integrable :
    IntegrableOn (fun t => t * (thetaT t - 1)) (Ioc (0:ℝ) 1) MeasureTheory.volume ∧
    IntegrableOn (fun t => t * (thetaT t - 1)) (Ioi (1:ℝ)) MeasureTheory.volume :=
  ⟨mellin_s2_half_small, mellin_s2_half_large⟩

end YangMills.DualBook
