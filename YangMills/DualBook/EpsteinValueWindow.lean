/-
YANGMILLS DUAL BOOK — R241: THE EPSTEIN VALUE WINDOW (W2-E + W2-F).

The R240 stone sealed the evaluation tools (`EpsteinEvalWindow.lean`:
eta(2), the alternating-harmonic limit, the per-piece Lambert integral
1/(12 j^2), and the per-term triangle bound). This window spends them on
the tail and the assembly:

  W2-E (tail-integration bound): the integrated tail of the Lambert
         series beyond the 2K-th term vanishes like O(1/(K+1)) —
         |int x*L(x) - int x*(sum_{m<2K} lamTerm m x)| <= 1/(12(K+1)) —
         by PAIRING consecutive terms (the pair family kills the
         divergent triangle of the single terms: int |x lamTerm| is
         harmonic, int |x pairFam| is zeta) and ONE dominated swap of
         the pair family, licensed by the absolute summability of the
         integral norms, receipt 4/(pi^2 (p+1)^2).
  W2-F (assembly): conditional on the single named Lambert-Jacobi
         `HasSum` hypothesis (W2-A, `LambJacobiHyp` below, never
         claimed), the honest object of the 1111 arm closes:
             ZAdic1111 = -(2/3) * pi^2 * log 2,
         and the R239 unconditional cascade (`JacobiAnchorsTime.lean`)
         immediately cashes out
             ZAdic1100 = (1/4)  ZAdic1111 = -(1/6)  * pi^2 * log 2,
             ZAdic1000 + ZAdic1110 = (1/8) ZAdic1111 = -(1/12) * pi^2 * log 2.

HONEST AMENDMENT (pre-registration vs delivery, recorded in the open at
the R241 opener): the pre-registration said "NO double-sum swap" for
W2-E. The working license performs exactly ONE dominated swap — the
pair family's integral norms are absolutely summable, and that receipt
IS the tail bound's content. The pointwise-geometric no-swap route was
proven lossy on paper (the middle-region bound is O(1) and the
coefficient-geometric tsums are absent from the vintage). The amendment
is stated here, in the ledger, and in the certificate.

WITNESS (bench, frozen; R240 probes `r240_probe1`/`r240_probe2` carry
the theta-vs-lambert agreement to 4.6e-16 and the Simpson values):
  ZAdic1111 (Simpson)     = -4.56072564257 (12 d.p.)
  -(2/3) pi^2 log 2       = -4.56072564257 (12 d.p.)
  -(1/6)  pi^2 log 2       = -1.14018141064 (12 d.p.)
  -(1/12) pi^2 log 2       = -0.57009070532 (12 d.p.)

HOUSE LAW (pre-registered at the R241 opener, c1687): zero sorry; axioms
[propext, Classical.choice, Quot.sound] only; scope THIS ARITHMETIC only
(the Lambert-Jacobi identity rides as a NAMED hypothesis, never
claimed); bench frozen at 100.0; plain-text .lean on the card; the Clay
crossing is never claimed; no push (the sibling court seals).
-/
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.SumIntegralComparisons
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.Gamma
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.NumberTheory.ZetaValues
import Mathlib.Topology.Algebra.InfiniteSum.Module
import Mathlib.Topology.Algebra.InfiniteSum.NatInt
import YangMills.DualBook.EpsteinEvalWindow
import YangMills.DualBook.JacobiAnchorsTime

set_option maxHeartbeats 512000

namespace YangMills.DualBook

open MeasureTheory Real Set Topology

/-! ## Section 0: the named hypothesis and the Lambert family -/

/-- The Lambert series term, byte-same as the (private) house definition
in `EpsteinEvalWindow.lean`, restated here so the family is local:
`(m+1) q^{m+1} / (1 + q^{m+1})` with alternating sign, `q = e^{-pi x}`. -/
private noncomputable def lamTerm (m : ℕ) (x : ℝ) : ℝ :=
  (-1 : ℝ) ^ (m + 1) * (((m + 1 : ℕ) : ℝ))
    * Real.exp (-Real.pi * ((m + 1 : ℕ) : ℝ) * x)
    / (1 + Real.exp (-Real.pi * ((m + 1 : ℕ) : ℝ) * x))

/-- THE NAMED WINDOW (W2-A): the Lambert-Jacobi identity for the fourth
power of theta-4,
  thetaFour t ^ 4 - 1 = 8 * sum'_m lamTerm m t     (t > 0),
stated in `HasSum` form so it carries summability of the Lambert family.
NEVER CLAIMED in this window: it is the single hypothesis the assembly
rides; every other input is paid unconditionally below. -/
def LambJacobiHyp : Prop :=
  ∀ t : ℝ, 0 < t → HasSum (fun m : ℕ => lamTerm m t) ((thetaFour t ^ 4 - 1) / 8)

/-- Own helper (kept off the vintage-name lottery):
`exp (n * t) = exp t ^ n` (byte-same as the house helper). -/
private theorem exp_pow_self (n : ℕ) (t : ℝ) : Real.exp (n * t) = Real.exp t ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    have h1 : ((n + 1 : ℕ) : ℝ) * t = (n : ℝ) * t + t := by
      push_cast
      ring
    rw [h1, Real.exp_add, ih, pow_succ]

/-- Exponent folding: `e^{-pi n x} = E^n` with `E = e^{-pi x}` (byte-same
as the house helper in `EpsteinEvalWindow.lean`). -/
private theorem exp_pow_nat (n : ℕ) (x : ℝ) :
    Real.exp (-Real.pi * ((n : ℕ) : ℝ) * x) = Real.exp (-Real.pi * x) ^ n := by
  have h1 : (-Real.pi * ((n : ℕ) : ℝ) * x) = ((n : ℕ) : ℝ) * (-Real.pi * x) := by ring
  rw [h1, exp_pow_self]

/-- The small-`y` bound: `1 - e^{-y} <= y` for `y >= 0`, straight from
`1 + x <= exp x` (with `x = -y`). -/
private theorem one_sub_exp_neg_le {y : ℝ} (hy : 0 ≤ y) : 1 - Real.exp (-y) ≤ y := by
  have h : (-y) + 1 ≤ Real.exp (-y) := Real.add_one_le_exp (-y)
  linarith

/-! ## Section 1: Gamma-evaluated exponential integrals (house wrappers) -/

/-- `int_0^inf x e^{-b x} dx = 1/b^2` for `b > 0` (house wrapper, paid
since the Mellin window). -/
private theorem integral_exp_neg_mul {b : ℝ} (hb : 0 < b) :
    ∫ x in Ioi (0 : ℝ), x * Real.exp (-b * x) ∂volume = 1 / b ^ 2 := by
  have h := integral_rpow_mul_exp_neg_mul_rpow (p := 1) (q := 1) (b := b)
    (by norm_num) (by norm_num) hb
  simp only [Real.rpow_one, div_one, mul_one] at h
  have h21 : (1 : ℝ) + 1 = 2 := by norm_num
  rw [h21] at h
  -- `Real.Gamma_two` does not exist in this vintage; pay it from the
  -- recurrence: Gamma (1 + 1) = 1 * Gamma 1 = 1.
  have hG : Real.Gamma (2 : ℝ) = 1 := by
    rw [(show (2 : ℝ) = 1 + 1 by norm_num), Real.Gamma_add_one one_ne_zero, Real.Gamma_one,
      one_mul]
  rw [h, hG, mul_one, Real.rpow_neg hb.le, Real.rpow_two, inv_eq_one_div]

/-- **NEW this window**: `int_0^inf x^2 e^{-b x} dx = 2/b^3` for `b > 0`,
from the same Mathlib source at `p = 1, q = 2` with `Gamma 3 = 2`
(paid from the recurrence: Gamma (2 + 1) = 2 * Gamma 2 = 2). -/
private theorem integral_exp_neg_mul_two {b : ℝ} (hb : 0 < b) :
    ∫ x in Ioi (0 : ℝ), x ^ 2 * Real.exp (-b * x) ∂volume = 2 / b ^ 3 := by
  have h := integral_rpow_mul_exp_neg_mul_rpow (p := 1) (q := 2) (b := b)
    (by norm_num) (by norm_num) hb
  simp only [Real.rpow_one, Real.rpow_two, div_one, mul_one] at h
  have h31 : (2 : ℝ) + 1 = 3 := by norm_num
  rw [h31] at h
  -- h : ∫ x, x ^ 2 * exp (-b * x) = b ^ (-(3:ℝ)) * Gamma (3:ℝ)
  have hG : Real.Gamma (3 : ℝ) = 2 := by
    rw [(show (3 : ℝ) = 2 + 1 by norm_num), Real.Gamma_add_one two_ne_zero,
      (show Real.Gamma (2 : ℝ) = 1 by
        rw [(show (2 : ℝ) = 1 + 1 by norm_num), Real.Gamma_add_one one_ne_zero,
          Real.Gamma_one, one_mul]),
      mul_one]
  have key : b ^ (-(3 : ℝ)) = 1 / b ^ 3 := by
    have he : (-(3 : ℝ)) = (-(2 : ℝ)) + (-(1 : ℝ)) := by norm_num
    rw [he, Real.rpow_add hb, Real.rpow_neg hb.le, Real.rpow_two, Real.rpow_neg hb.le,
      Real.rpow_one, inv_eq_one_div, inv_eq_one_div]
    field_simp
  rw [h, hG, key]
  field_simp

/-- Integrability receipt: `x e^{-b x}` on the half-line, `b >= 1`
(domination by the Gamma receipt `x e^{-x}`, house mono pattern). -/
private theorem integrable_x_exp_neg_mul {b : ℝ} (hb : 1 ≤ b) :
    IntegrableOn (fun x : ℝ => x * Real.exp (-b * x)) (Ioi (0 : ℝ)) volume := by
  have hrec := integrableOn_rpow_mul_exp_neg_rpow (s := (1 : ℝ)) (p := (1 : ℝ))
    (by norm_num) (by norm_num)
  have hdom0 : MeasureTheory.Integrable
      (fun x : ℝ => x * Real.exp (-x)) (MeasureTheory.volume.restrict (Ioi (0 : ℝ))) :=
    hrec.congr_fun (fun x _ => by simp only [Real.rpow_one]) measurableSet_Ioi
  have hdom : ∀ x ∈ Ioi (0 : ℝ),
      ‖x * Real.exp (-b * x)‖ ≤ ‖x * Real.exp (-x)‖ := by
    intro x hx
    have hx0 : 0 ≤ x := (Set.mem_Ioi.mp hx).le
    rw [Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_nonneg (by positivity : (0:ℝ) ≤ x * Real.exp (-b * x)),
      abs_of_nonneg (by positivity : (0:ℝ) ≤ x * Real.exp (-x))]
    have hd3 : Real.exp (-b * x) ≤ Real.exp (-x) := by
      refine Real.exp_le_exp.mpr ?_
      nlinarith [hb, hx0]
    exact mul_le_mul_of_nonneg_left hd3 hx0
  have hmeas : AEStronglyMeasurable (fun x : ℝ => x * Real.exp (-b * x))
      (MeasureTheory.volume.restrict (Ioi (0 : ℝ))) :=
    (by fun_prop : Measurable (fun x : ℝ => x * Real.exp (-b * x))).aestronglyMeasurable
  exact MeasureTheory.Integrable.mono hdom0 hmeas
    (Filter.mem_of_superset (self_mem_ae_restrict measurableSet_Ioi) hdom)

/-- Integrability receipt: `x^2 e^{-b x}` on the half-line, `b >= 1`. -/
private theorem integrable_xsq_exp_neg_mul {b : ℝ} (hb : 1 ≤ b) :
    IntegrableOn (fun x : ℝ => x ^ 2 * Real.exp (-b * x)) (Ioi (0 : ℝ)) volume := by
  have hrec := integrableOn_rpow_mul_exp_neg_rpow (s := (2 : ℝ)) (p := (1 : ℝ))
    (by norm_num) (by norm_num)
  have hdom0 : MeasureTheory.Integrable
      (fun x : ℝ => x ^ 2 * Real.exp (-x)) (MeasureTheory.volume.restrict (Ioi (0 : ℝ))) := by
    refine hrec.congr_fun (fun x _ => ?_) measurableSet_Ioi
    simp only [Real.rpow_one, Real.rpow_two]
  have hdom : ∀ x ∈ Ioi (0 : ℝ),
      ‖x ^ 2 * Real.exp (-b * x)‖ ≤ ‖x ^ 2 * Real.exp (-x)‖ := by
    intro x hx
    have hx0 : 0 ≤ x := (Set.mem_Ioi.mp hx).le
    rw [Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_nonneg (by positivity : (0:ℝ) ≤ x ^ 2 * Real.exp (-b * x)),
      abs_of_nonneg (by positivity : (0:ℝ) ≤ x ^ 2 * Real.exp (-x))]
    have hd3 : Real.exp (-b * x) ≤ Real.exp (-x) := by
      refine Real.exp_le_exp.mpr ?_
      nlinarith [hb, hx0]
    exact mul_le_mul_of_nonneg_left hd3 (sq_nonneg x)
  have hmeas : AEStronglyMeasurable (fun x : ℝ => x ^ 2 * Real.exp (-b * x))
      (MeasureTheory.volume.restrict (Ioi (0 : ℝ))) :=
    (by fun_prop : Measurable (fun x : ℝ => x ^ 2 * Real.exp (-b * x))).aestronglyMeasurable
  exact MeasureTheory.Integrable.mono hdom0 hmeas
    (Filter.mem_of_superset (self_mem_ae_restrict measurableSet_Ioi) hdom)
private theorem setIntegral_congr {s : Set ℝ} (hs : MeasurableSet s)
    {f g : ℝ → ℝ} (h : ∀ x ∈ s, f x = g x) :
    ∫ x in s, f x ∂volume = ∫ x in s, g x ∂volume :=
  setIntegral_congr_fun hs h

private theorem setIntegral_add {s : Set ℝ} (hs : MeasurableSet s)
    {f g : ℝ → ℝ} (hf : IntegrableOn f s volume) (hg : IntegrableOn g s volume) :
    ∫ x in s, f x + g x ∂volume
      = ∫ x in s, f x ∂volume + ∫ x in s, g x ∂volume :=
  integral_add (μ := volume.restrict s) hf hg

private theorem setIntegral_sub {s : Set ℝ} (hs : MeasurableSet s)
    {f g : ℝ → ℝ} (hf : IntegrableOn f s volume) (hg : IntegrableOn g s volume) :
    ∫ x in s, f x - g x ∂volume
      = ∫ x in s, f x ∂volume - ∫ x in s, g x ∂volume :=
  integral_sub (μ := volume.restrict s) hf hg

private theorem setIntegral_const_mul {s : Set ℝ} (hs : MeasurableSet s)
    {f : ℝ → ℝ} (r : ℝ) (hf : IntegrableOn f s volume) :
    ∫ x in s, r * f x ∂volume = r * ∫ x in s, f x ∂volume :=
  integral_const_mul (μ := volume.restrict s) r f

private theorem setIntegral_abs_le {s : Set ℝ} (hs : MeasurableSet s)
    {f : ℝ → ℝ} (hf : IntegrableOn f s volume) :
    |∫ x in s, f x ∂volume| ≤ ∫ x in s, |f x| ∂volume := by
  have h1 : ‖∫ x in s, f x ∂volume‖ ≤ ∫ x in s, ‖f x‖ ∂volume :=
    norm_integral_le_integral_norm (μ := volume.restrict s) f
  simp only [Real.norm_eq_abs] at h1
  exact h1

/-- Monotonicity for set integrals, via the indicator bridge and
`integral_nonneg` on the difference (no `integral_mono` needed). -/
private theorem setIntegral_mono {s : Set ℝ} (hs : MeasurableSet s)
    {f g : ℝ → ℝ} (hf : IntegrableOn f s volume) (hg : IntegrableOn g s volume)
    (hle : ∀ x ∈ s, f x ≤ g x) :
    ∫ x in s, f x ∂volume ≤ ∫ x in s, g x ∂volume :=
  setIntegral_mono_on hf hg hs hle

private theorem integrableOn_sum_range {s : Set ℝ} (hs : MeasurableSet s)
    {N : ℕ} {F : ℕ → ℝ → ℝ} (hF : ∀ m < N, IntegrableOn (F m) s volume) :
    IntegrableOn (fun x => ∑ m ∈ Finset.range N, F m x) s volume := by
  induction N with
  | zero => simp only [Finset.range_zero, Finset.sum_empty]; exact integrableOn_zero
  | succ N ih =>
    have hF' : ∀ m < N, IntegrableOn (F m) s volume :=
      fun m hm => hF m (by omega)
    have hFN : IntegrableOn (F N) s volume := hF N (Nat.lt_succ_self N)
    have hFS : IntegrableOn (fun x => ∑ m ∈ Finset.range N, F m x) s volume := ih hF'
    have heq : (fun x => ∑ m ∈ Finset.range (N + 1), F m x)
        = fun x => (∑ m ∈ Finset.range N, F m x) + F N x := by
      funext x
      rw [Finset.sum_range_succ]
    rw [heq]
    exact hFS.add hFN

private theorem setIntegral_sum_range {s : Set ℝ} (hs : MeasurableSet s)
    {N : ℕ} {F : ℕ → ℝ → ℝ} (hF : ∀ m < N, IntegrableOn (F m) s volume) :
    ∫ x in s, ∑ m ∈ Finset.range N, F m x ∂volume
      = ∑ m ∈ Finset.range N, ∫ x in s, F m x ∂volume := by
  induction N with
  | zero => simp
  | succ N ih =>
    have hF' : ∀ m < N, IntegrableOn (F m) s volume :=
      fun m hm => hF m (by omega)
    have hFN : IntegrableOn (F N) s volume := hF N (Nat.lt_succ_self N)
    have hFS : IntegrableOn (fun x => ∑ m ∈ Finset.range N, F m x) s volume :=
      integrableOn_sum_range hs hF'
    have hkey : ∀ x ∈ s, ∑ m ∈ Finset.range (N + 1), F m x
        = (∑ m ∈ Finset.range N, F m x) + F N x := fun x _ => Finset.sum_range_succ ..
    rw [setIntegral_congr hs hkey, setIntegral_add hs hFS hFN, ih hF',
      Finset.sum_range_succ]

/-! ## Section 3: the pair family — signs, algebra, absolute bound -/

/-- The even-slot sign: `(-1)^(2p) = 1`. -/
private theorem neg_one_pow_two_mul (p : ℕ) : (-1 : ℝ) ^ (2 * p) = 1 := by
  rw [pow_mul, neg_one_sq, one_pow]

/-- The odd-slot sign: `(-1)^(2p+1) = -1`. -/
private theorem neg_one_pow_two_mul_add_one (p : ℕ) : (-1 : ℝ) ^ (2 * p + 1) = -1 := by
  rw [show (2 * p + 1 : ℕ) = (2 * p) + 1 by omega, pow_add, neg_one_pow_two_mul, one_mul,
    pow_one]

/-- The paired even sign in unfolded form: `(-1)^((2p+1)+1) = 1`. -/
private theorem neg_one_pow_two_mul_add_one_add_one (p : ℕ) :
    (-1 : ℝ) ^ ((2 * p + 1 : ℕ) + 1) = 1 := by
  rw [pow_add, neg_one_pow_two_mul_add_one, pow_one]
  norm_num

/-- The pair family: two consecutive Lambert terms, taken together —
the triangle-inequality divergence of the single terms dies here. -/
private noncomputable def pairFam (p : ℕ) (x : ℝ) : ℝ :=
  lamTerm (2 * p) x + lamTerm (2 * p + 1) x

/-- THE PAIR ALGEBRA (load-bearing): over the common denominator the
pair's numerator is `u * [A (E-1) + E + E u]` with `A = 2p+1`,
`u = e^{-pi(2p+1) x}`, `E = e^{-pi x}`, `v = E u`. -/
private theorem pairFam_eq (p : ℕ) (x : ℝ) :
    pairFam p x
      = Real.exp (-Real.pi * ((2 * p + 1 : ℕ) : ℝ) * x)
        * (((2 * p + 1 : ℕ) : ℝ) * (Real.exp (-Real.pi * x) - 1)
          + Real.exp (-Real.pi * x)
          + Real.exp (-Real.pi * x) * Real.exp (-Real.pi * ((2 * p + 1 : ℕ) : ℝ) * x))
        / ((1 + Real.exp (-Real.pi * ((2 * p + 1 : ℕ) : ℝ) * x))
          * (1 + Real.exp (-Real.pi * ((2 * p + 2 : ℕ) : ℝ) * x))) := by
  have hE : (0 : ℝ) < Real.exp (-Real.pi * x) := Real.exp_pos _
  have hu : (0 : ℝ) < Real.exp (-Real.pi * ((2 * p + 1 : ℕ) : ℝ) * x) := Real.exp_pos _
  have hv : (0 : ℝ) < Real.exp (-Real.pi * ((2 * p + 2 : ℕ) : ℝ) * x) := Real.exp_pos _
  have hvE : Real.exp (-Real.pi * ((2 * p + 2 : ℕ) : ℝ) * x)
      = Real.exp (-Real.pi * x) * Real.exp (-Real.pi * ((2 * p + 1 : ℕ) : ℝ) * x) := by
    rw [← Real.exp_add]
    congr 1
    push_cast
    ring
  have hB : ((2 * p + 2 : ℕ) : ℝ) = ((2 * p + 1 : ℕ) : ℝ) + 1 := by
    push_cast
    ring
  have hzero1 : (0 : ℝ) < 1 + Real.exp (-Real.pi * x)
      * Real.exp (-Real.pi * ((2 * p + 1 : ℕ) : ℝ) * x) := by positivity
  simp only [pairFam, lamTerm] at *
  rw [hvE, hB]
  rw [neg_one_pow_two_mul_add_one, neg_one_pow_two_mul_add_one_add_one]
  field_simp
  ring

/-- THE ABSTRACT FRACTION BOUND: with `A >= 0`, `E, u >= 0`, `v > 0`,
`E <= 1`, `1 - E <= P` and `v = E * u`, the pair fraction is bounded by
`|u (A (E-1) + E + E u) / ((1+u)(1+v))| <= A P u + E u + E u^2`. -/
private theorem pair_frac_abs_bound {A E u v P : ℝ}
    (hA0 : 0 ≤ A) (hE : 0 ≤ E) (hu : 0 ≤ u) (hv : 0 < v)
    (hE1 : E ≤ 1) (h1E : 1 - E ≤ P) (hveq : v = E * u) :
    |u * (A * (E - 1) + E + E * u) / ((1 + u) * (1 + v))|
      ≤ A * P * u + E * u + E * u * u := by
  have hden : (1 : ℝ) ≤ (1 + u) * (1 + v) := by nlinarith [hu, hv.le]
  have hEm1 : E - 1 ≤ 0 := by linarith
  have habsN : |A * (E - 1) + E + E * u| ≤ A * (1 - E) + E + E * u := by
    have h1 : |A * (E - 1)| = A * (1 - E) := by
      rw [abs_mul, abs_of_nonpos hEm1, abs_of_nonneg hA0]
      ring
    have h2 : 0 ≤ E + E * u := by nlinarith [hE, hu]
    have h3 : |E + E * u| = E + E * u := abs_of_nonneg h2
    rw [show A * (E - 1) + E + E * u = A * (E - 1) + (E + E * u) by ring,
      show A * (1 - E) + E + E * u = A * (1 - E) + (E + E * u) by ring]
    refine (abs_add_le _ _).trans_eq ?_
    rw [h1, h3]
  have hNN : 0 ≤ |A * (E - 1) + E + E * u| := abs_nonneg _
  rw [abs_div, abs_mul, abs_mul, abs_of_nonneg hu,
    abs_of_nonneg (by nlinarith : (0 : ℝ) ≤ 1 + u),
    abs_of_nonneg (by nlinarith : (0 : ℝ) ≤ 1 + v)]
  have hstep1 : u * |A * (E - 1) + E + E * u| / ((1 + u) * (1 + v))
      ≤ u * |A * (E - 1) + E + E * u| := by
    have ht : 0 ≤ u * |A * (E - 1) + E + E * u| := mul_nonneg hu hNN
    have hB1 : 0 ≤ (1 + u) * (1 + v) - 1 := by nlinarith [hu, hv.le]
    rw [div_le_iff₀ (by nlinarith [hu, hv.le] : (0 : ℝ) < (1 + u) * (1 + v))]
    nlinarith [ht, hB1]
  have hstep2 : u * |A * (E - 1) + E + E * u|
      ≤ u * (A * (1 - E) + E + E * u) :=
    mul_le_mul_of_nonneg_left habsN hu
  have hstep3 : u * (A * (1 - E) + E + E * u) ≤ A * P * u + E * u + E * u * u := by
    have hA : A * (1 - E) * u ≤ A * P * u :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h1E hA0) hu
    have hexp : u * (A * (1 - E) + E + E * u)
        = A * (1 - E) * u + E * u + E * u * u := by ring
    rw [hexp]
    linarith
  exact hstep1.trans (hstep2.trans hstep3)

/-- THE ABSOLUTE PAIR BOUND: `|pairFam p x| <= A pi x u + v + uv` with
`A = 2p+1`, `u = e^{-pi A x}`, `v = e^{-pi (A+1) x}` and `uv` the product
strand — the pair algebra plus `1 - E <= pi x`, all denominators `>= 1`. -/
private theorem abs_pairFam_le (p : ℕ) {x : ℝ} (hx : 0 ≤ x) :
    |pairFam p x| ≤ ((2 * p + 1 : ℕ) : ℝ) * Real.pi * x
        * Real.exp (-Real.pi * ((2 * p + 1 : ℕ) : ℝ) * x)
      + Real.exp (-Real.pi * ((2 * p + 2 : ℕ) : ℝ) * x)
      + Real.exp (-Real.pi * ((4 * p + 3 : ℕ) : ℝ) * x) := by
  have hπ : (0 : ℝ) < Real.pi := Real.pi_pos
  have hπx : 0 ≤ Real.pi * x := mul_nonneg hπ.le hx
  have hEpos : (0 : ℝ) < Real.exp (-Real.pi * x) := Real.exp_pos _
  have hE1 : Real.exp (-Real.pi * x) ≤ 1 := by
    have h : Real.exp (-Real.pi * x) ≤ Real.exp 0 :=
      Real.exp_le_exp.mpr (by nlinarith [hπ, hx])
    simpa using h
  have h1E : 1 - Real.exp (-Real.pi * x) ≤ Real.pi * x := by
    have h := Real.add_one_le_exp (-Real.pi * x)
    nlinarith [h, hπx]
  have hvE : Real.exp (-Real.pi * ((2 * p + 2 : ℕ) : ℝ) * x)
      = Real.exp (-Real.pi * x) * Real.exp (-Real.pi * ((2 * p + 1 : ℕ) : ℝ) * x) := by
    rw [← Real.exp_add]
    congr 1
    push_cast
    ring
  have hvu : Real.exp (-Real.pi * ((2 * p + 2 : ℕ) : ℝ) * x)
      * Real.exp (-Real.pi * ((2 * p + 1 : ℕ) : ℝ) * x)
      = Real.exp (-Real.pi * ((4 * p + 3 : ℕ) : ℝ) * x) := by
    rw [← Real.exp_add]
    congr 1
    push_cast
    ring
  have hbound := pair_frac_abs_bound
    (A := ((2 * p + 1 : ℕ) : ℝ)) (E := Real.exp (-Real.pi * x))
    (u := Real.exp (-Real.pi * ((2 * p + 1 : ℕ) : ℝ) * x))
    (v := Real.exp (-Real.pi * ((2 * p + 2 : ℕ) : ℝ) * x))
    (P := Real.pi * x)
    (Nat.cast_nonneg _) (hEpos.le : (0 : ℝ) ≤ Real.exp (-Real.pi * x))
    (by positivity : (0 : ℝ) ≤ Real.exp (-Real.pi * ((2 * p + 1 : ℕ) : ℝ) * x))
    (Real.exp_pos _)
    (hE1) (h1E) (hvE)
  rw [pairFam_eq p x]
  refine hbound.trans_eq ?_
  rw [← hvE, hvu]
  ring

/-! ## Section 4: integrability and exact values of the pair integrals -/

/-- Domination receipt for the Lambert quotient: `x e^{-pi j x}/(1+e^{-pi j x})`
is integrable on the half-line — the denominator exceeds 1 and the top is
dominated by `x e^{-pi j x}` (house mono pattern, `pi j >= 1`). -/
private theorem integrable_x_exp_div {j : ℕ} (hj : 0 < j) :
    IntegrableOn (fun x : ℝ => x * Real.exp (-Real.pi * ((j : ℕ) : ℝ) * x)
      / (1 + Real.exp (-Real.pi * ((j : ℕ) : ℝ) * x))) (Ioi (0 : ℝ)) volume := by
  have hpione : (1 : ℝ) ≤ Real.pi := by
    have := pi_gt_three
    linarith
  have hb : (1 : ℝ) ≤ Real.pi * ((j : ℕ) : ℝ) := by
    have hn : (1 : ℝ) ≤ ((j : ℕ) : ℝ) := by exact_mod_cast hj
    nlinarith [hpione, hn]
  have hbase := integrable_x_exp_neg_mul hb
  have hdom : ∀ x ∈ Ioi (0 : ℝ),
      ‖x * Real.exp (-Real.pi * ((j : ℕ) : ℝ) * x)
        / (1 + Real.exp (-Real.pi * ((j : ℕ) : ℝ) * x))‖
      ≤ ‖x * Real.exp (-(Real.pi * ((j : ℕ) : ℝ)) * x)‖ := by
    intro x hx
    have hx0 : 0 ≤ x := (Set.mem_Ioi.mp hx).le
    have hnn : 0 ≤ x * Real.exp (-Real.pi * ((j : ℕ) : ℝ) * x)
        / (1 + Real.exp (-Real.pi * ((j : ℕ) : ℝ) * x)) := by
      apply div_nonneg <;> positivity
    rw [Real.norm_eq_abs, abs_of_nonneg hnn, Real.norm_eq_abs,
      abs_of_nonneg (by positivity : (0 : ℝ) ≤ x * Real.exp (-(Real.pi * ((j : ℕ) : ℝ)) * x))]
    have hshape : x * Real.exp (-Real.pi * ((j : ℕ) : ℝ) * x)
        = x * Real.exp (-(Real.pi * ((j : ℕ) : ℝ)) * x) := by
      congr 1
      ring
    rw [hshape]
    rw [div_le_iff₀ (by positivity : (0 : ℝ) < 1 + Real.exp (-Real.pi * ((j : ℕ) : ℝ) * x))]
    nlinarith [mul_nonneg hx0
        (by positivity : (0 : ℝ) ≤ Real.exp (-(Real.pi * ((j : ℕ) : ℝ)) * x)),
      (by positivity : (0 : ℝ) ≤ Real.exp (-Real.pi * ((j : ℕ) : ℝ) * x))]
  have hmeas : AEStronglyMeasurable (fun x : ℝ => x * Real.exp (-Real.pi * ((j : ℕ) : ℝ) * x)
      / (1 + Real.exp (-Real.pi * ((j : ℕ) : ℝ) * x)))
      (MeasureTheory.volume.restrict (Ioi (0 : ℝ))) :=
    (by fun_prop : Measurable (fun x : ℝ => x * Real.exp (-Real.pi * ((j : ℕ) : ℝ) * x)
      / (1 + Real.exp (-Real.pi * ((j : ℕ) : ℝ) * x)))).aestronglyMeasurable
  exact MeasureTheory.Integrable.mono hbase hmeas
    (Filter.mem_of_superset (self_mem_ae_restrict measurableSet_Ioi) hdom)

/-- `x lamTerm m x` integrable: dominated by the signed constant times the
plain exponential receipt scaled by `m+1` (the quotient's denominator
exceeds 1, `|(-1)^(m+1)| = 1`). -/
private theorem integrable_x_mul_lamTerm (m : ℕ) :
    IntegrableOn (fun x => x * lamTerm m x) (Ioi (0 : ℝ)) volume := by
  have hpione : (1 : ℝ) ≤ Real.pi := by
    have := pi_gt_three
    linarith
  have hb : (1 : ℝ) ≤ Real.pi * ((m + 1 : ℕ) : ℝ) := by
    have hn : (1 : ℝ) ≤ ((m + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.succ_pos m
    nlinarith [hpione, hn]
  have hbase := integrable_x_exp_neg_mul hb
  have hgscaled := MeasureTheory.Integrable.const_mul hbase
    (((m + 1 : ℕ) : ℝ) * ((-1 : ℝ) ^ (m + 1)))
  have hmeas : AEStronglyMeasurable (fun x => x * lamTerm m x)
      (MeasureTheory.volume.restrict (Ioi (0 : ℝ))) := by
    unfold lamTerm
    exact (by fun_prop : Measurable (fun x : ℝ => x * ((-1 : ℝ) ^ (m + 1)
      * (((m + 1 : ℕ) : ℝ)) * Real.exp (-Real.pi * ((m + 1 : ℕ) : ℝ) * x)
      / (1 + Real.exp (-Real.pi * ((m + 1 : ℕ) : ℝ) * x))))).aestronglyMeasurable
  have hdom : ∀ x ∈ Ioi (0 : ℝ), ‖x * lamTerm m x‖
      ≤ ‖(((m + 1 : ℕ) : ℝ) * ((-1 : ℝ) ^ (m + 1)))
        * (x * Real.exp (-(Real.pi * ((m + 1 : ℕ) : ℝ)) * x))‖ := by
    intro x hx
    have hx0 : 0 ≤ x := (Set.mem_Ioi.mp hx).le
    have hsign : |((-1 : ℝ) ^ (m + 1))| = 1 := by
      simp [abs_pow]
    have habs : |x * lamTerm m x| = ((m + 1 : ℕ) : ℝ)
      * (x * Real.exp (-Real.pi * ((m + 1 : ℕ) : ℝ) * x)
        / (1 + Real.exp (-Real.pi * ((m + 1 : ℕ) : ℝ) * x))) := by
      unfold lamTerm
      rw [abs_mul, abs_div, abs_mul, abs_mul, abs_of_nonneg hx0, hsign,
        one_mul, abs_of_nonneg (Nat.cast_nonneg _),
        abs_of_nonneg (by positivity : (0 : ℝ) ≤ Real.exp (-Real.pi * ((m + 1 : ℕ) : ℝ) * x)),
        abs_of_nonneg (by positivity : (0 : ℝ) ≤ 1 + Real.exp (-Real.pi * ((m + 1 : ℕ) : ℝ) * x))]
      ring
    have habsR : |(((m + 1 : ℕ) : ℝ) * ((-1 : ℝ) ^ (m + 1)))
        * (x * Real.exp (-(Real.pi * ((m + 1 : ℕ) : ℝ)) * x))|
        = ((m + 1 : ℕ) : ℝ)
          * (x * Real.exp (-(Real.pi * ((m + 1 : ℕ) : ℝ)) * x)) := by
      rw [abs_mul, abs_mul, abs_mul, abs_of_nonneg (Nat.cast_nonneg _), hsign, mul_one,
        abs_of_nonneg hx0,
        abs_of_nonneg (by positivity : (0 : ℝ) ≤ Real.exp (-(Real.pi * ((m + 1 : ℕ) : ℝ)) * x))]
    have hshape : x * Real.exp (-Real.pi * ((m + 1 : ℕ) : ℝ) * x)
        = x * Real.exp (-(Real.pi * ((m + 1 : ℕ) : ℝ)) * x) := by
      congr 1
      ring
    have hkey : ((m + 1 : ℕ) : ℝ)
        * (x * Real.exp (-(Real.pi * ((m + 1 : ℕ) : ℝ)) * x)
          / (1 + Real.exp (-Real.pi * ((m + 1 : ℕ) : ℝ) * x)))
        ≤ ((m + 1 : ℕ) : ℝ)
          * (x * Real.exp (-(Real.pi * ((m + 1 : ℕ) : ℝ)) * x)) := by
      have hq : x * Real.exp (-(Real.pi * ((m + 1 : ℕ) : ℝ)) * x)
          / (1 + Real.exp (-Real.pi * ((m + 1 : ℕ) : ℝ) * x))
          ≤ x * Real.exp (-(Real.pi * ((m + 1 : ℕ) : ℝ)) * x) := by
        rw [div_le_iff₀ (by positivity : (0 : ℝ) < 1 + Real.exp (-Real.pi * ((m + 1 : ℕ) : ℝ) * x))]
        nlinarith [mul_nonneg hx0
          (by positivity : (0 : ℝ) ≤ Real.exp (-(Real.pi * ((m + 1 : ℕ) : ℝ)) * x)),
          (by positivity : (0 : ℝ) ≤ Real.exp (-Real.pi * ((m + 1 : ℕ) : ℝ) * x))]
      exact mul_le_mul_of_nonneg_left hq (Nat.cast_nonneg _)
    rw [Real.norm_eq_abs, Real.norm_eq_abs, habs, habsR, hshape]
    exact hkey
  exact MeasureTheory.Integrable.mono hgscaled hmeas
    (Filter.mem_of_superset (self_mem_ae_restrict measurableSet_Ioi) hdom)

/-- `x pairFam p x` integrable: the sum of the two Lambert receipts. -/
private theorem integrable_x_mul_pairFam (p : ℕ) :
    IntegrableOn (fun x => x * pairFam p x) (Ioi (0 : ℝ)) volume := by
  have hI1 := integrable_x_mul_lamTerm (2 * p)
  have hI2 := integrable_x_mul_lamTerm (2 * p + 1)
  refine (hI1.add hI2).congr_fun (fun x hx => ?_) measurableSet_Ioi
  show x * lamTerm (2 * p) x + x * lamTerm (2 * p + 1) x = x * pairFam p x
  show x * lamTerm (2 * p) x + x * lamTerm (2 * p + 1) x
      = x * (lamTerm (2 * p) x + lamTerm (2 * p + 1) x)
  ring

/-- Exact value of the Lambert term integral:
`int x lamTerm m x = (-1)^(m+1) / (12 (m+1))` — the house Lambert value
`int x e^{-pi j x}/(1+e^{-pi j x}) = 1/(12 j^2)` scaled by `j = m+1`. -/
private theorem integral_x_mul_lamTerm (m : ℕ) :
    ∫ x in Ioi (0 : ℝ), x * lamTerm m x ∂volume
      = (-1 : ℝ) ^ (m + 1) / (12 * ((m + 1 : ℕ) : ℝ)) := by
  have hj : 0 < m + 1 := Nat.succ_pos m
  have hval := integral_exp_div_one_add hj
  have hcongr : ∀ x ∈ Ioi (0 : ℝ), x * lamTerm m x
      = ((-1 : ℝ) ^ (m + 1) * (((m + 1 : ℕ) : ℝ)))
        * (x * Real.exp (-Real.pi * ((m + 1 : ℕ) : ℝ) * x)
          / (1 + Real.exp (-Real.pi * ((m + 1 : ℕ) : ℝ) * x))) :=
    fun x hx => by unfold lamTerm; ring
  rw [setIntegral_congr measurableSet_Ioi hcongr,
    setIntegral_const_mul measurableSet_Ioi _ (integrable_x_exp_div hj), hval]
  have hj0 : ((m + 1 : ℕ) : ℝ) ≠ 0 := by
    exact_mod_cast Nat.succ_ne_zero m
  field_simp

/-- Exact value of the pair integral:
`int x pairFam p x = (1/12)(1/(2p+2) - 1/(2p+1))` — the cash-out target
`c p` of the W2-E tail bound. -/
private theorem integral_x_pairFam (p : ℕ) :
    ∫ x in Ioi (0 : ℝ), x * pairFam p x ∂volume
      = (1 / 12) * (1 / ((2 * p + 2 : ℕ) : ℝ) - 1 / ((2 * p + 1 : ℕ) : ℝ)) := by
  have hI1 := integrable_x_mul_lamTerm (2 * p)
  have hI2 := integrable_x_mul_lamTerm (2 * p + 1)
  have hcongr : ∀ x ∈ Ioi (0 : ℝ), x * pairFam p x
      = x * lamTerm (2 * p) x + x * lamTerm (2 * p + 1) x :=
    fun x hx => by
      unfold pairFam
      ring
  rw [setIntegral_congr measurableSet_Ioi hcongr,
    setIntegral_add measurableSet_Ioi hI1 hI2,
    integral_x_mul_lamTerm (2 * p), integral_x_mul_lamTerm (2 * p + 1),
    neg_one_pow_two_mul_add_one p, neg_one_pow_two_mul_add_one_add_one p,
    show ((2 * p + 1 : ℕ) + 1) = 2 * p + 2 by omega]
  ring

/-! ## Section 4.5: the norm-integral bound — the swap's license receipt -/

/-- The absolute pair integrand is integrable: dominated by the three
explicit exponential pieces (the pair algebra's bound times `x`,
in the lemma shape `-(pi * c) * x`). -/
private theorem integrable_abs_x_mul_pairFam (p : ℕ) :
    IntegrableOn (fun x : ℝ => |x * pairFam p x|) (Ioi (0 : ℝ)) volume := by
  have hpione : (1 : ℝ) ≤ Real.pi := by
    have := pi_gt_three
    linarith
  have hn1 : (1 : ℝ) ≤ ((p + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.succ_pos p
  have hA : (1 : ℝ) ≤ ((2 * p + 1 : ℕ) : ℝ) := by
    have h2 : ((p + 1 : ℕ) : ℝ) ≤ ((2 * p + 1 : ℕ) : ℝ) :=
      by exact_mod_cast (by omega : (p + 1 : ℕ) ≤ 2 * p + 1)
    linarith
  have hB : (1 : ℝ) ≤ ((2 * p + 2 : ℕ) : ℝ) := by
    have h2 : ((p + 1 : ℕ) : ℝ) ≤ ((2 * p + 2 : ℕ) : ℝ) :=
      by exact_mod_cast (by omega : (p + 1 : ℕ) ≤ 2 * p + 2)
    linarith
  have hC : (1 : ℝ) ≤ ((4 * p + 3 : ℕ) : ℝ) := by
    have h2 : ((p + 1 : ℕ) : ℝ) ≤ ((4 * p + 3 : ℕ) : ℝ) :=
      by exact_mod_cast (by omega : (p + 1 : ℕ) ≤ 4 * p + 3)
    linarith
  have hπA : (1 : ℝ) ≤ Real.pi * ((2 * p + 1 : ℕ) : ℝ) := by nlinarith [hpione, hA]
  have hπB : (1 : ℝ) ≤ Real.pi * ((2 * p + 2 : ℕ) : ℝ) := by nlinarith [hpione, hB]
  have hπC : (1 : ℝ) ≤ Real.pi * ((4 * p + 3 : ℕ) : ℝ) := by nlinarith [hpione, hC]
  have h1 := integrable_xsq_exp_neg_mul hπA
  have h2 := integrable_x_exp_neg_mul hπB
  have h3 := integrable_x_exp_neg_mul hπC
  have hD : MeasureTheory.Integrable
      (fun x : ℝ => ((2 * p + 1 : ℕ) : ℝ) * Real.pi * (x ^ 2
          * Real.exp (-(Real.pi * ((2 * p + 1 : ℕ) : ℝ)) * x))
        + (x * Real.exp (-(Real.pi * ((2 * p + 2 : ℕ) : ℝ)) * x)
          + x * Real.exp (-(Real.pi * ((4 * p + 3 : ℕ) : ℝ)) * x)))
      (MeasureTheory.volume.restrict (Ioi (0 : ℝ))) :=
    (h1.const_mul (((2 * p + 1 : ℕ) : ℝ) * Real.pi)).add (h2.add h3)
  have hmeas : AEStronglyMeasurable (fun x : ℝ => |x * pairFam p x|)
      (MeasureTheory.volume.restrict (Ioi (0 : ℝ))) := by
    unfold pairFam lamTerm
    fun_prop
  have hdom : ∀ x ∈ Ioi (0 : ℝ),
      ‖|x * pairFam p x|‖
      ≤ ‖((2 * p + 1 : ℕ) : ℝ) * Real.pi * (x ^ 2
          * Real.exp (-(Real.pi * ((2 * p + 1 : ℕ) : ℝ)) * x))
        + (x * Real.exp (-(Real.pi * ((2 * p + 2 : ℕ) : ℝ)) * x)
          + x * Real.exp (-(Real.pi * ((4 * p + 3 : ℕ) : ℝ)) * x))‖ := by
    intro x hx
    have hx0 : 0 ≤ x := (Set.mem_Ioi.mp hx).le
    have hb := abs_pairFam_le p hx0
    have e1 : Real.exp (-Real.pi * ((2 * p + 1 : ℕ) : ℝ) * x)
        = Real.exp (-(Real.pi * ((2 * p + 1 : ℕ) : ℝ)) * x) := by congr 1; ring
    have e2 : Real.exp (-Real.pi * ((2 * p + 2 : ℕ) : ℝ) * x)
        = Real.exp (-(Real.pi * ((2 * p + 2 : ℕ) : ℝ)) * x) := by congr 1; ring
    have e3 : Real.exp (-Real.pi * ((4 * p + 3 : ℕ) : ℝ) * x)
        = Real.exp (-(Real.pi * ((4 * p + 3 : ℕ) : ℝ)) * x) := by congr 1; ring
    rw [e1, e2, e3] at hb
    rw [Real.norm_eq_abs, Real.norm_eq_abs]
    rw [abs_abs]
    rw [abs_mul, abs_of_nonneg hx0]
    have hstep : x * |pairFam p x|
        ≤ ((2 * p + 1 : ℕ) : ℝ) * Real.pi * (x ^ 2
          * Real.exp (-(Real.pi * ((2 * p + 1 : ℕ) : ℝ)) * x))
        + (x * Real.exp (-(Real.pi * ((2 * p + 2 : ℕ) : ℝ)) * x)
          + x * Real.exp (-(Real.pi * ((4 * p + 3 : ℕ) : ℝ)) * x)) := by
      have hmul : x * |pairFam p x|
          ≤ x * (((2 * p + 1 : ℕ) : ℝ) * Real.pi * x
            * Real.exp (-(Real.pi * ((2 * p + 1 : ℕ) : ℝ)) * x)
            + Real.exp (-(Real.pi * ((2 * p + 2 : ℕ) : ℝ)) * x)
            + Real.exp (-(Real.pi * ((4 * p + 3 : ℕ) : ℝ)) * x)) :=
        mul_le_mul_of_nonneg_left hb hx0
      have hexp : x * (((2 * p + 1 : ℕ) : ℝ) * Real.pi * x
            * Real.exp (-(Real.pi * ((2 * p + 1 : ℕ) : ℝ)) * x)
            + Real.exp (-(Real.pi * ((2 * p + 2 : ℕ) : ℝ)) * x)
            + Real.exp (-(Real.pi * ((4 * p + 3 : ℕ) : ℝ)) * x))
          = ((2 * p + 1 : ℕ) : ℝ) * Real.pi * (x ^ 2
            * Real.exp (-(Real.pi * ((2 * p + 1 : ℕ) : ℝ)) * x))
            + (x * Real.exp (-(Real.pi * ((2 * p + 2 : ℕ) : ℝ)) * x)
              + x * Real.exp (-(Real.pi * ((4 * p + 3 : ℕ) : ℝ)) * x)) := by
        ring
      exact hmul.trans_eq hexp
    exact hstep.trans (le_abs_self _)
  exact MeasureTheory.Integrable.mono hD hmeas
    (Filter.mem_of_superset (self_mem_ae_restrict measurableSet_Ioi) hdom)

/-! ## Section 7: the regrouped alternating harmonic (Piece 3) -/

/-- The doubling map tends to infinity (self-supplied; absent from the
name lottery). -/
private theorem tendsto_two_mul :
    Filter.Tendsto (fun K : ℕ => 2 * K) Filter.atTop Filter.atTop :=
  (Filter.tendsto_atTop_atTop).mpr (fun b => ⟨b, fun a ha => by omega⟩)

/-- Piece 3: the alternating harmonic regrouped into consecutive pairs
converges to `log 2` — the `K`-th pair partial sum is exactly the `2K`-th
alternating partial sum, and the pair family is absolutely summable. -/
private theorem hasSum_pair_harmonic :
    HasSum (fun p : ℕ => 1 / ((2 * p + 1 : ℕ) : ℝ) - 1 / ((2 * p + 2 : ℕ) : ℝ))
      (Real.log 2) := by
  -- the shifted zeta dominates the pair norms
  have hzshift : Summable (fun p : ℕ => 1 / (((p + 1 : ℕ) : ℝ) ^ 2)) :=
    hasSum_zeta_two.summable.comp_injective
      (f := fun n : ℕ => (1 : ℝ) / ((n : ℕ) : ℝ) ^ 2)
      (i := fun p : ℕ => p + 1)
      (by
        intro a b hab
        have h' : a + 1 = b + 1 := hab
        omega)
  have hdom : ∀ p : ℕ,
      ‖(1 / ((2 * p + 1 : ℕ) : ℝ) - 1 / ((2 * p + 2 : ℕ) : ℝ))‖
        ≤ 1 / (((p + 1 : ℕ) : ℝ) ^ 2) := by
    intro p
    rw [Real.norm_eq_abs]
    have h1 : (0 : ℝ) < ((2 * p + 1 : ℕ) : ℝ) := by positivity
    have h2 : (0 : ℝ) < ((2 * p + 2 : ℕ) : ℝ) := by positivity
    have hAB : ((2 * p + 1 : ℕ) : ℝ) < ((2 * p + 2 : ℕ) : ℝ) := by
      exact_mod_cast (by omega : (2 * p + 1 : ℕ) < 2 * p + 2)
    have hlt : 1 / ((2 * p + 2 : ℕ) : ℝ) < 1 / ((2 * p + 1 : ℕ) : ℝ) :=
      (one_div_lt_one_div h2 h1).mpr hAB
    rw [abs_of_pos
      (by rw [sub_pos]
          exact hlt :
        (0 : ℝ) < 1 / ((2 * p + 1 : ℕ) : ℝ) - 1 / ((2 * p + 2 : ℕ) : ℝ))]
    rw [div_sub_div (1 : ℝ) (1 : ℝ) (ne_of_gt h1) (ne_of_gt h2), one_mul, mul_one]
    have hBA : ((2 * p + 2 : ℕ) : ℝ) - ((2 * p + 1 : ℕ) : ℝ) = 1 := by
      push_cast
      ring
    rw [hBA]
    rw [one_div_le_one_div
      (by positivity : (0 : ℝ) < ((2 * p + 1 : ℕ) : ℝ) * ((2 * p + 2 : ℕ) : ℝ))
      (by positivity : (0 : ℝ) < ((p + 1 : ℕ) : ℝ) ^ 2)]
    push_cast
    have hp : (0 : ℝ) ≤ ((p : ℕ) : ℝ) := Nat.cast_nonneg p
    nlinarith [sq_nonneg ((p : ℕ) : ℝ)]
  have hsumm : Summable (fun p : ℕ =>
      ‖(1 / ((2 * p + 1 : ℕ) : ℝ) - 1 / ((2 * p + 2 : ℕ) : ℝ))‖) :=
    Summable.of_norm_bounded hzshift
      (fun p => by rw [norm_norm]; exact hdom p)
  refine (hasSum_iff_tendsto_nat_of_summable_norm hsumm).mpr ?_
  -- the pair partial sums are the even alternating partial sums
  have hid : ∀ K : ℕ,
      ∑ p ∈ Finset.range K, (1 / ((2 * p + 1 : ℕ) : ℝ) - 1 / ((2 * p + 2 : ℕ) : ℝ))
      = ∑ n ∈ Finset.range (2 * K), (-1 : ℝ) ^ n / (((n + 1 : ℕ) : ℝ)) := by
    intro K
    induction K with
    | zero => simp
    | succ k ih =>
      have h1 : (2 * (k + 1) : ℕ) = 2 * k + 1 + 1 := by omega
      rw [Finset.sum_range_succ, ih, h1, Finset.sum_range_succ,
        Finset.sum_range_succ, add_assoc]
      have hpair : ((-1 : ℝ) ^ (2 * k) / (((2 * k + 1 : ℕ) : ℝ))
          + (-1 : ℝ) ^ (2 * k + 1) / (((2 * k + 1 + 1 : ℕ) : ℝ)))
          = 1 / ((2 * k + 1 : ℕ) : ℝ) - 1 / ((2 * k + 2 : ℕ) : ℝ) := by
        rw [neg_one_pow_two_mul k, neg_one_pow_two_mul_add_one k]
        push_cast
        ring
      rw [hpair]
  exact (Filter.tendsto_congr hid).mpr (tendsto_altHarmonic.comp tendsto_two_mul)

/-! ## Section 5: strand summability, the pair-range identity, and the
pointwise Lambert/pair tsum equality -/

/-- The zeta shift `sum'_p 1/(p+1)^2` (the same summability the pair
harmonic rides; standalone so Sections 6 and 8 can reuse it). -/
private theorem summable_zeta_shift :
    Summable (fun p : ℕ => 1 / (((p + 1 : ℕ) : ℝ) ^ 2)) :=
  hasSum_zeta_two.summable.comp_injective
    (f := fun n : ℕ => (1 : ℝ) / ((n : ℕ) : ℝ) ^ 2)
    (i := fun p : ℕ => p + 1)
    (by
      intro a b hab
      have h' : a + 1 = b + 1 := hab
      omega)

/-- Pointwise Lambert term bound: the denominator exceeds 1, so the
alternating term is dominated by its numerator strand. -/
private theorem abs_lamTerm_le (m : ℕ) (t : ℝ) :
    |lamTerm m t| ≤ ((m + 1 : ℕ) : ℝ)
      * Real.exp (-Real.pi * ((m + 1 : ℕ) : ℝ) * t) := by
  have hE : (0 : ℝ) ≤ Real.exp (-Real.pi * ((m + 1 : ℕ) : ℝ) * t) :=
    (Real.exp_pos _).le
  have h1 : |(-1 : ℝ) ^ (m + 1)| = 1 := by
    rw [abs_pow, abs_neg, abs_one, one_pow]
  unfold lamTerm
  rw [abs_div, abs_mul, abs_mul, h1, one_mul, abs_of_nonneg (Nat.cast_nonneg _),
    abs_of_nonneg hE,
    abs_of_nonneg (show (0 : ℝ) ≤ 1
      + Real.exp (-Real.pi * ((m + 1 : ℕ) : ℝ) * t) by positivity)]
  have hnn : (0 : ℝ) ≤ ((m + 1 : ℕ) : ℝ)
      * Real.exp (-Real.pi * ((m + 1 : ℕ) : ℝ) * t) :=
    mul_nonneg (Nat.cast_nonneg _) hE
  rw [div_le_iff₀ (show (0 : ℝ) < 1
      + Real.exp (-Real.pi * ((m + 1 : ℕ) : ℝ) * t) by positivity)]
  nlinarith [mul_nonneg hnn hE]

/-- The Lambert family is absolutely summable at every `t > 0`: the
strand `(m+1) E^(m+1)` folds into `E` times the geometric-zeta strands. -/
private theorem summable_lamTerm_norm {t : ℝ} (ht : 0 < t) :
    Summable (fun m : ℕ => ‖lamTerm m t‖) := by
  have hr : (0 : ℝ) < Real.exp (-Real.pi * t) := Real.exp_pos _
  have hr1 : Real.exp (-Real.pi * t) < 1 := by
    have h : Real.exp (-Real.pi * t) < Real.exp (0 : ℝ) :=
      Real.exp_lt_exp.mpr (by nlinarith [Real.pi_pos, ht])
    simpa using h
  have hrr : |Real.exp (-Real.pi * t)| < 1 := by
    rw [abs_of_nonneg hr.le]
    exact hr1
  have hA0 : Summable (fun m : ℕ =>
      ((m : ℕ) ^ 1 : ℝ) * Real.exp (-Real.pi * t) ^ m) :=
    summable_pow_mul_geometric_of_norm_lt_one 1 hrr
  have hA : Summable (fun m : ℕ =>
      (m : ℝ) * Real.exp (-Real.pi * t) ^ m) := by
    have heq : (fun m : ℕ => (m : ℝ) * Real.exp (-Real.pi * t) ^ m)
        = fun m : ℕ => ((m : ℕ) ^ 1 : ℝ) * Real.exp (-Real.pi * t) ^ m := by
      funext m
      simp only [Nat.cast_one, pow_one]
    rw [heq]
    exact hA0
  have hB : Summable (fun m : ℕ => Real.exp (-Real.pi * t) ^ m) :=
    summable_geometric_of_abs_lt_one hrr
  have hg : Summable (fun m : ℕ =>
      Real.exp (-Real.pi * t) * ((m : ℝ) * Real.exp (-Real.pi * t) ^ m
        + Real.exp (-Real.pi * t) ^ m)) := by
    have h := (hA.mul_left (Real.exp (-Real.pi * t))).add
      (hB.mul_left (Real.exp (-Real.pi * t)))
    have heq : (fun m : ℕ => Real.exp (-Real.pi * t) * ((m : ℝ)
          * Real.exp (-Real.pi * t) ^ m
          + Real.exp (-Real.pi * t) ^ m))
        = fun m : ℕ => Real.exp (-Real.pi * t)
          * ((m : ℝ) * Real.exp (-Real.pi * t) ^ m)
          + Real.exp (-Real.pi * t) * (Real.exp (-Real.pi * t) ^ m) := by
      funext m
      ring
    rw [heq]
    exact h
  refine Summable.of_norm_bounded hg (fun m => ?_)
  simp only [Real.norm_eq_abs, abs_abs]
  have hle := abs_lamTerm_le m t
  rw [exp_pow_nat (m + 1) t] at hle
  have hdist : ((m + 1 : ℕ) : ℝ) * Real.exp (-Real.pi * t) ^ (m + 1)
      = Real.exp (-Real.pi * t) * ((m : ℝ) * Real.exp (-Real.pi * t) ^ m
        + Real.exp (-Real.pi * t) ^ m) := by
    push_cast
    rw [pow_add, pow_one]
    ring
  exact hle.trans_eq hdist

/-- The pair family is absolutely summable at every `t > 0`: the pair
algebra's bound folds into `pi t`-scaled `(E^2)`- and `(E^4)`-strands. -/
private theorem summable_pairFam_norm {t : ℝ} (ht : 0 < t) :
    Summable (fun p : ℕ => ‖pairFam p t‖) := by
  have hr : (0 : ℝ) < Real.exp (-Real.pi * t) := Real.exp_pos _
  have hr1 : Real.exp (-Real.pi * t) < 1 := by
    have h : Real.exp (-Real.pi * t) < Real.exp (0 : ℝ) :=
      Real.exp_lt_exp.mpr (by nlinarith [Real.pi_pos, ht])
    simpa using h
  have hrr : |Real.exp (-Real.pi * t)| < 1 := by
    rw [abs_of_nonneg hr.le]
    exact hr1
  have hrr2 : |Real.exp (-Real.pi * t) ^ 2| < 1 := by
    rw [abs_pow]
    nlinarith [hrr, abs_nonneg (Real.exp (-Real.pi * t))]
  have hrr4 : |Real.exp (-Real.pi * t) ^ 4| < 1 := by
    have he : (Real.exp (-Real.pi * t) ^ 2) ^ 2
        = Real.exp (-Real.pi * t) ^ 4 := by
      rw [← pow_mul]
    rw [← he, abs_pow]
    nlinarith [hrr2, abs_nonneg (Real.exp (-Real.pi * t) ^ 2)]
  have hA0 : Summable (fun p : ℕ =>
      ((p : ℕ) ^ 1 : ℝ) * (Real.exp (-Real.pi * t) ^ 2) ^ p) :=
    summable_pow_mul_geometric_of_norm_lt_one 1 hrr2
  have hA : Summable (fun p : ℕ =>
      (p : ℝ) * (Real.exp (-Real.pi * t) ^ 2) ^ p) := by
    have heq : (fun p : ℕ => (p : ℝ) * (Real.exp (-Real.pi * t) ^ 2) ^ p)
        = fun p : ℕ => ((p : ℕ) ^ 1 : ℝ)
          * (Real.exp (-Real.pi * t) ^ 2) ^ p := by
      funext p
      simp only [Nat.cast_one, pow_one]
    rw [heq]
    exact hA0
  have hB2 : Summable (fun p : ℕ =>
      (Real.exp (-Real.pi * t) ^ 2) ^ p) :=
    summable_geometric_of_abs_lt_one hrr2
  have hB4 : Summable (fun p : ℕ =>
      (Real.exp (-Real.pi * t) ^ 4) ^ p) :=
    summable_geometric_of_abs_lt_one hrr4
  have hg : Summable (fun p : ℕ =>
      Real.pi * t * (2 * Real.exp (-Real.pi * t))
        * ((p : ℝ) * (Real.exp (-Real.pi * t) ^ 2) ^ p)
      + ((Real.pi * t * Real.exp (-Real.pi * t)
          + Real.exp (-Real.pi * t) ^ 2)
          * (Real.exp (-Real.pi * t) ^ 2) ^ p
        + Real.exp (-Real.pi * t) ^ 3
          * (Real.exp (-Real.pi * t) ^ 4) ^ p)) :=
    (hA.mul_left (Real.pi * t * (2 * Real.exp (-Real.pi * t)))).add
      ((hB2.mul_left (Real.pi * t * Real.exp (-Real.pi * t)
        + Real.exp (-Real.pi * t) ^ 2)).add
        (hB4.mul_left (Real.exp (-Real.pi * t) ^ 3)))
  refine Summable.of_norm_bounded hg (fun p => ?_)
  simp only [Real.norm_eq_abs, abs_abs]
  have hb := abs_pairFam_le p ht.le
  rw [exp_pow_nat (2 * p + 1) t, exp_pow_nat (2 * p + 2) t,
    exp_pow_nat (4 * p + 3) t] at hb
  calc |pairFam p t|
      ≤ ((2 * p + 1 : ℕ) : ℝ) * Real.pi * t
          * Real.exp (-Real.pi * t) ^ (2 * p + 1)
        + Real.exp (-Real.pi * t) ^ (2 * p + 2)
        + Real.exp (-Real.pi * t) ^ (4 * p + 3) := hb
    _ = Real.pi * t * (2 * Real.exp (-Real.pi * t))
          * ((p : ℝ) * (Real.exp (-Real.pi * t) ^ 2) ^ p)
        + ((Real.pi * t * Real.exp (-Real.pi * t)
            + Real.exp (-Real.pi * t) ^ 2)
            * (Real.exp (-Real.pi * t) ^ 2) ^ p
          + Real.exp (-Real.pi * t) ^ 3
            * (Real.exp (-Real.pi * t) ^ 4) ^ p) := by
        have e1 : (Real.exp (-Real.pi * t)) ^ ((2 * p + 1 : ℕ))
            = Real.exp (-Real.pi * t)
              * ((Real.exp (-Real.pi * t) ^ 2) ^ p) := by
          rw [pow_add, pow_mul, pow_one]
          ring
        have e2 : (Real.exp (-Real.pi * t)) ^ ((2 * p + 2 : ℕ))
            = (Real.exp (-Real.pi * t) ^ 2)
              * ((Real.exp (-Real.pi * t) ^ 2) ^ p) := by
          rw [pow_add, pow_mul]
          ring
        have e3 : (Real.exp (-Real.pi * t)) ^ ((4 * p + 3 : ℕ))
            = (Real.exp (-Real.pi * t) ^ 3)
              * ((Real.exp (-Real.pi * t) ^ 4) ^ p) := by
          rw [pow_add, pow_mul]
          ring
        rw [e1, e2, e3]
        push_cast
        ring

/-- The pair-range identity: the `2K`-th Lambert partial sum is the `K`-th
pair partial sum (the regrouping the whole window rides). -/
private theorem pair_sum_range (K : ℕ) (x : ℝ) :
    ∑ m ∈ Finset.range (2 * K), lamTerm m x
      = ∑ p ∈ Finset.range K, pairFam p x := by
  induction K with
  | zero => simp
  | succ k ih =>
    have h2 : (2 * (k + 1) : ℕ) = 2 * k + 2 := by omega
    have hp : pairFam k x = lamTerm (2 * k) x + lamTerm (2 * k + 1) x := rfl
    rw [h2, Finset.sum_range_succ, Finset.sum_range_succ, ih,
      Finset.sum_range_succ, hp]
    ring

/-- The regrouped series: the pair family sums to the same value as the
Lambert family (unconditional — both are absolutely summable, and the
pair partial sums are the even Lambert partial sums). -/
private theorem hasSum_pairFam {t : ℝ} (ht : 0 < t) :
    HasSum (fun p : ℕ => pairFam p t) (∑' m, lamTerm m t) := by
  have hLnorm := summable_lamTerm_norm ht
  have hL : Summable (fun m : ℕ => lamTerm m t) :=
    Summable.of_norm_bounded hLnorm (fun m => le_rfl)
  have hPnorm := summable_pairFam_norm ht
  have htend := (hasSum_iff_tendsto_nat_of_summable_norm hLnorm).mp
    (Summable.hasSum hL)
  have hcomp := htend.comp tendsto_two_mul
  have hpair := (Filter.tendsto_congr (fun K => pair_sum_range K t)).mp hcomp
  exact (hasSum_iff_tendsto_nat_of_summable_norm hPnorm).mpr hpair

/-- Pointwise tsum equality: the pair and Lambert families agree in the
infinite sum (unconditional). -/
private theorem pairFam_tsum_eq {t : ℝ} (ht : 0 < t) :
    (∑' p, pairFam p t) = (∑' m, lamTerm m t) :=
  (hasSum_pairFam ht).tsum_eq

/-! ## Section 6: the norm-integral bound, its summability, and the swap -/

/-- The swap's license, in closed form: `int |x pairFam p x| <=
4/(pi^2 (p+1)^2)` — the three Gamma-evaluated pieces of the pair
algebra's bound, coarsely dominated by four shifted zetas. -/
private theorem integral_abs_x_mul_pairFam_le (p : ℕ) :
    ∫ x in Ioi (0 : ℝ), |x * pairFam p x| ∂volume
      ≤ 4 / (Real.pi ^ 2 * ((p + 1 : ℕ) : ℝ) ^ 2) := by
  have hpione : (1 : ℝ) ≤ Real.pi := by
    have := pi_gt_three
    linarith
  have hn1 : (1 : ℝ) ≤ ((p + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.succ_pos p
  have hA1 : (1 : ℝ) ≤ ((2 * p + 1 : ℕ) : ℝ) := by
    have h2 : ((p + 1 : ℕ) : ℝ) ≤ ((2 * p + 1 : ℕ) : ℝ) :=
      by exact_mod_cast (by omega : (p + 1 : ℕ) ≤ 2 * p + 1)
    linarith
  have hB1 : (1 : ℝ) ≤ ((2 * p + 2 : ℕ) : ℝ) := by
    have h2 : ((p + 1 : ℕ) : ℝ) ≤ ((2 * p + 2 : ℕ) : ℝ) :=
      by exact_mod_cast (by omega : (p + 1 : ℕ) ≤ 2 * p + 2)
    linarith
  have hC1 : (1 : ℝ) ≤ ((4 * p + 3 : ℕ) : ℝ) := by
    have h2 : ((p + 1 : ℕ) : ℝ) ≤ ((4 * p + 3 : ℕ) : ℝ) :=
      by exact_mod_cast (by omega : (p + 1 : ℕ) ≤ 4 * p + 3)
    linarith
  have hπA : (1 : ℝ) ≤ Real.pi * ((2 * p + 1 : ℕ) : ℝ) := by nlinarith [hpione, hA1]
  have hπB : (1 : ℝ) ≤ Real.pi * ((2 * p + 2 : ℕ) : ℝ) := by nlinarith [hpione, hB1]
  have hπC : (1 : ℝ) ≤ Real.pi * ((4 * p + 3 : ℕ) : ℝ) := by nlinarith [hpione, hC1]
  have hπApos : (0 : ℝ) < Real.pi * ((2 * p + 1 : ℕ) : ℝ) := by linarith
  have hπBpos : (0 : ℝ) < Real.pi * ((2 * p + 2 : ℕ) : ℝ) := by linarith
  have hπCpos : (0 : ℝ) < Real.pi * ((4 * p + 3 : ℕ) : ℝ) := by linarith
  -- the dominator's integrability (the 4.5 receipt)
  have hDint : IntegrableOn (fun x : ℝ => ((2 * p + 1 : ℕ) : ℝ) * Real.pi
      * (x ^ 2 * Real.exp (-(Real.pi * ((2 * p + 1 : ℕ) : ℝ)) * x))
      + (x * Real.exp (-(Real.pi * ((2 * p + 2 : ℕ) : ℝ)) * x)
        + x * Real.exp (-(Real.pi * ((4 * p + 3 : ℕ) : ℝ)) * x)))
      (Ioi (0 : ℝ)) volume :=
    (integrable_xsq_exp_neg_mul hπA).const_mul (((2 * p + 1 : ℕ) : ℝ) * Real.pi)
      |>.add ((integrable_x_exp_neg_mul hπB).add (integrable_x_exp_neg_mul hπC))
  -- pointwise domination (the 4.5 arithmetic)
  have hdom : ∀ x ∈ Ioi (0 : ℝ),
      |x * pairFam p x| ≤ ((2 * p + 1 : ℕ) : ℝ) * Real.pi
      * (x ^ 2 * Real.exp (-(Real.pi * ((2 * p + 1 : ℕ) : ℝ)) * x))
      + (x * Real.exp (-(Real.pi * ((2 * p + 2 : ℕ) : ℝ)) * x)
        + x * Real.exp (-(Real.pi * ((4 * p + 3 : ℕ) : ℝ)) * x)) := by
    intro x hx
    have hx0 : 0 ≤ x := (Set.mem_Ioi.mp hx).le
    have hb := abs_pairFam_le p hx0
    have e1 : Real.exp (-Real.pi * ((2 * p + 1 : ℕ) : ℝ) * x)
        = Real.exp (-(Real.pi * ((2 * p + 1 : ℕ) : ℝ)) * x) := by congr 1; ring
    have e2 : Real.exp (-Real.pi * ((2 * p + 2 : ℕ) : ℝ) * x)
        = Real.exp (-(Real.pi * ((2 * p + 2 : ℕ) : ℝ)) * x) := by congr 1; ring
    have e3 : Real.exp (-Real.pi * ((4 * p + 3 : ℕ) : ℝ) * x)
        = Real.exp (-(Real.pi * ((4 * p + 3 : ℕ) : ℝ)) * x) := by congr 1; ring
    rw [e1, e2, e3] at hb
    rw [abs_mul, abs_of_nonneg hx0]
    have hmul : x * |pairFam p x|
        ≤ x * (((2 * p + 1 : ℕ) : ℝ) * Real.pi * x
          * Real.exp (-(Real.pi * ((2 * p + 1 : ℕ) : ℝ)) * x)
          + Real.exp (-(Real.pi * ((2 * p + 2 : ℕ) : ℝ)) * x)
          + Real.exp (-(Real.pi * ((4 * p + 3 : ℕ) : ℝ)) * x)) :=
      mul_le_mul_of_nonneg_left hb hx0
    have hexp : x * (((2 * p + 1 : ℕ) : ℝ) * Real.pi * x
          * Real.exp (-(Real.pi * ((2 * p + 1 : ℕ) : ℝ)) * x)
          + Real.exp (-(Real.pi * ((2 * p + 2 : ℕ) : ℝ)) * x)
          + Real.exp (-(Real.pi * ((4 * p + 3 : ℕ) : ℝ)) * x))
        = ((2 * p + 1 : ℕ) : ℝ) * Real.pi
          * (x ^ 2 * Real.exp (-(Real.pi * ((2 * p + 1 : ℕ) : ℝ)) * x))
        + (x * Real.exp (-(Real.pi * ((2 * p + 2 : ℕ) : ℝ)) * x)
          + x * Real.exp (-(Real.pi * ((4 * p + 3 : ℕ) : ℝ)) * x)) := by
      ring
    exact hmul.trans_eq hexp
  have habs := integrable_abs_x_mul_pairFam p
  have hmono := setIntegral_mono measurableSet_Ioi habs hDint hdom
  -- the named integrability receipts (ascribed, so the rewrites bind cleanly)
  have hSqInt : IntegrableOn (fun x : ℝ => x ^ 2
      * Real.exp (-(Real.pi * ((2 * p + 1 : ℕ) : ℝ)) * x)) (Ioi (0 : ℝ)) volume :=
    integrable_xsq_exp_neg_mul hπA
  have hApInt : IntegrableOn (fun x : ℝ => ((2 * p + 1 : ℕ) : ℝ) * Real.pi
      * (x ^ 2 * Real.exp (-(Real.pi * ((2 * p + 1 : ℕ) : ℝ)) * x)))
      (Ioi (0 : ℝ)) volume :=
    (integrable_xsq_exp_neg_mul hπA).const_mul (((2 * p + 1 : ℕ) : ℝ) * Real.pi)
  have hBInt : IntegrableOn (fun x : ℝ => x
      * Real.exp (-(Real.pi * ((2 * p + 2 : ℕ) : ℝ)) * x)) (Ioi (0 : ℝ)) volume :=
    integrable_x_exp_neg_mul hπB
  have hCInt : IntegrableOn (fun x : ℝ => x
      * Real.exp (-(Real.pi * ((4 * p + 3 : ℕ) : ℝ)) * x)) (Ioi (0 : ℝ)) volume :=
    integrable_x_exp_neg_mul hπC
  have hBCInt : IntegrableOn (fun x : ℝ => x
      * Real.exp (-(Real.pi * ((2 * p + 2 : ℕ) : ℝ)) * x)
      + x * Real.exp (-(Real.pi * ((4 * p + 3 : ℕ) : ℝ)) * x))
      (Ioi (0 : ℝ)) volume := hBInt.add hCInt
  -- evaluate the dominator's integral
  have hDval : ∫ x in Ioi (0 : ℝ), ((2 * p + 1 : ℕ) : ℝ) * Real.pi
      * (x ^ 2 * Real.exp (-(Real.pi * ((2 * p + 1 : ℕ) : ℝ)) * x))
      + (x * Real.exp (-(Real.pi * ((2 * p + 2 : ℕ) : ℝ)) * x)
        + x * Real.exp (-(Real.pi * ((4 * p + 3 : ℕ) : ℝ)) * x)) ∂volume
      = ((2 * p + 1 : ℕ) : ℝ) * Real.pi
          * (2 / (Real.pi * ((2 * p + 1 : ℕ) : ℝ)) ^ 3)
        + (1 / (Real.pi * ((2 * p + 2 : ℕ) : ℝ)) ^ 2
          + 1 / (Real.pi * ((4 * p + 3 : ℕ) : ℝ)) ^ 2) := by
    rw [setIntegral_add measurableSet_Ioi hApInt hBCInt,
      setIntegral_add measurableSet_Ioi hBInt hCInt,
      setIntegral_const_mul measurableSet_Ioi
        (((2 * p + 1 : ℕ) : ℝ) * Real.pi) hSqInt,
      integral_exp_neg_mul_two hπApos,
      integral_exp_neg_mul hπBpos,
      integral_exp_neg_mul hπCpos]
  -- the numeric cash-out
  have hq : ((p + 1 : ℕ) : ℝ) ≤ ((2 * p + 1 : ℕ) : ℝ) :=
    by exact_mod_cast (by omega : (p + 1 : ℕ) ≤ 2 * p + 1)
  have hqb : ((p + 1 : ℕ) : ℝ) ≤ ((2 * p + 2 : ℕ) : ℝ) :=
    by exact_mod_cast (by omega : (p + 1 : ℕ) ≤ 2 * p + 2)
  have hqc : ((p + 1 : ℕ) : ℝ) ≤ ((4 * p + 3 : ℕ) : ℝ) :=
    by exact_mod_cast (by omega : (p + 1 : ℕ) ≤ 4 * p + 3)
  have hq0 : (0 : ℝ) ≤ ((p + 1 : ℕ) : ℝ) := Nat.cast_nonneg _
  have hπ : (0 : ℝ) < Real.pi := Real.pi_pos
  have hqπpos : (0 : ℝ) < Real.pi * ((p + 1 : ℕ) : ℝ) :=
    mul_pos hπ (by positivity)
  have s1 : ((2 * p + 1 : ℕ) : ℝ) * Real.pi
      * (2 / (Real.pi * ((2 * p + 1 : ℕ) : ℝ)) ^ 3)
      = 2 / (Real.pi * ((2 * p + 1 : ℕ) : ℝ)) ^ 2 := by
    have hpos : (0 : ℝ) < Real.pi * ((2 * p + 1 : ℕ) : ℝ) := hπApos
    field_simp
  have mono1 : 2 / (Real.pi * ((2 * p + 1 : ℕ) : ℝ)) ^ 2
      ≤ 2 / (Real.pi * ((p + 1 : ℕ) : ℝ)) ^ 2 := by
    have hple : Real.pi * ((p + 1 : ℕ) : ℝ)
        ≤ Real.pi * ((2 * p + 1 : ℕ) : ℝ) :=
      mul_le_mul_of_nonneg_left hq hπ.le
    have haπpos : (0 : ℝ) < Real.pi * ((2 * p + 1 : ℕ) : ℝ) := hπApos
    have hs : (Real.pi * ((p + 1 : ℕ) : ℝ)) ^ 2
        ≤ (Real.pi * ((2 * p + 1 : ℕ) : ℝ)) ^ 2 := by
      nlinarith [hple, hqπpos, haπpos, sq_nonneg (Real.pi * ((p + 1 : ℕ) : ℝ))]
    rw [div_le_div_iff₀
      (by positivity : (0 : ℝ) < (Real.pi * ((2 * p + 1 : ℕ) : ℝ)) ^ 2)
      (by positivity : (0 : ℝ) < (Real.pi * ((p + 1 : ℕ) : ℝ)) ^ 2)]
    linarith [hs]
  have mono2 : 1 / (Real.pi * ((2 * p + 2 : ℕ) : ℝ)) ^ 2
      ≤ 1 / (Real.pi * ((p + 1 : ℕ) : ℝ)) ^ 2 := by
    have hple : Real.pi * ((p + 1 : ℕ) : ℝ)
        ≤ Real.pi * ((2 * p + 2 : ℕ) : ℝ) :=
      mul_le_mul_of_nonneg_left hqb hπ.le
    have hbπpos : (0 : ℝ) < Real.pi * ((2 * p + 2 : ℕ) : ℝ) := hπBpos
    have hs : (Real.pi * ((p + 1 : ℕ) : ℝ)) ^ 2
        ≤ (Real.pi * ((2 * p + 2 : ℕ) : ℝ)) ^ 2 := by
      nlinarith [hple, hqπpos, hbπpos, sq_nonneg (Real.pi * ((p + 1 : ℕ) : ℝ))]
    exact (one_div_le_one_div
      (by positivity : (0 : ℝ) < (Real.pi * ((2 * p + 2 : ℕ) : ℝ)) ^ 2)
      (by positivity : (0 : ℝ) < (Real.pi * ((p + 1 : ℕ) : ℝ)) ^ 2)).mpr hs
  have mono3 : 1 / (Real.pi * ((4 * p + 3 : ℕ) : ℝ)) ^ 2
      ≤ 1 / (Real.pi * ((p + 1 : ℕ) : ℝ)) ^ 2 := by
    have hple : Real.pi * ((p + 1 : ℕ) : ℝ)
        ≤ Real.pi * ((4 * p + 3 : ℕ) : ℝ) :=
      mul_le_mul_of_nonneg_left hqc hπ.le
    have hcπpos : (0 : ℝ) < Real.pi * ((4 * p + 3 : ℕ) : ℝ) := hπCpos
    have hs : (Real.pi * ((p + 1 : ℕ) : ℝ)) ^ 2
        ≤ (Real.pi * ((4 * p + 3 : ℕ) : ℝ)) ^ 2 := by
      nlinarith [hple, hqπpos, hcπpos, sq_nonneg (Real.pi * ((p + 1 : ℕ) : ℝ))]
    exact (one_div_le_one_div
      (by positivity : (0 : ℝ) < (Real.pi * ((4 * p + 3 : ℕ) : ℝ)) ^ 2)
      (by positivity : (0 : ℝ) < (Real.pi * ((p + 1 : ℕ) : ℝ)) ^ 2)).mpr hs
  have hfinal : 2 / (Real.pi * ((p + 1 : ℕ) : ℝ)) ^ 2
      + (1 / (Real.pi * ((p + 1 : ℕ) : ℝ)) ^ 2
        + 1 / (Real.pi * ((p + 1 : ℕ) : ℝ)) ^ 2)
      = 4 / (Real.pi ^ 2 * ((p + 1 : ℕ) : ℝ) ^ 2) := by
    have hpos : (0 : ℝ) < Real.pi * ((p + 1 : ℕ) : ℝ) := hqπpos
    field_simp
    ring
  have hfin : ((2 * p + 1 : ℕ) : ℝ) * Real.pi
      * (2 / (Real.pi * ((2 * p + 1 : ℕ) : ℝ)) ^ 3)
      + (1 / (Real.pi * ((2 * p + 2 : ℕ) : ℝ)) ^ 2
        + 1 / (Real.pi * ((4 * p + 3 : ℕ) : ℝ)) ^ 2)
      ≤ 4 / (Real.pi ^ 2 * ((p + 1 : ℕ) : ℝ) ^ 2) := by
    rw [s1]
    have hstep := add_le_add mono1 (add_le_add mono2 mono3)
    exact hstep.trans_eq hfinal
  exact (hmono.trans_eq hDval).trans hfin

/-- The license is summable: the integral norms of the pair family form
a shifted-zeta family. -/
private theorem summable_integral_abs_x_mul_pairFam :
    Summable (fun p : ℕ => ∫ x in Ioi (0 : ℝ), |x * pairFam p x| ∂volume) := by
  have hz : Summable (fun p : ℕ => (4 / Real.pi ^ 2)
      * (1 / (((p + 1 : ℕ) : ℝ) ^ 2))) :=
    summable_zeta_shift.mul_left (4 / Real.pi ^ 2)
  refine Summable.of_norm_bounded hz (fun p => ?_)
  rw [Real.norm_eq_abs]
  have hnn : (0 : ℝ) ≤ ∫ x in Ioi (0 : ℝ), |x * pairFam p x| ∂volume :=
    integral_nonneg (fun x => abs_nonneg (x * pairFam p x))
  rw [abs_of_nonneg hnn]
  have heq : 4 / (Real.pi ^ 2 * ((p + 1 : ℕ) : ℝ) ^ 2)
      = (4 / Real.pi ^ 2) * (1 / (((p + 1 : ℕ) : ℝ) ^ 2)) := by
    have hpos : (0 : ℝ) < Real.pi ^ 2 * ((p + 1 : ℕ) : ℝ) ^ 2 := by positivity
    field_simp
  exact (integral_abs_x_mul_pairFam_le p).trans_eq heq

/-- THE SWAP (W2-E's engine): the pair integrals sum to the integral of
the pair tsum — Mathlib's dominated exchange, licensed by the summable
integral norms (the receipt of Section 6's bound). -/
private theorem hasSum_integral_x_mul_pairFam :
    HasSum (fun p : ℕ => ∫ x in Ioi (0 : ℝ), x * pairFam p x ∂volume)
      (∫ x in Ioi (0 : ℝ), x * (∑' p, pairFam p x) ∂volume) := by
  have h := hasSum_integral_of_summable_integral_norm
    (F := fun p : ℕ => fun x : ℝ => x * pairFam p x)
    (μ := MeasureTheory.volume.restrict (Ioi (0 : ℝ)))
    (fun p => integrable_x_mul_pairFam p)
    (summable_integral_abs_x_mul_pairFam)
  have hIeq : (∫ x in Ioi (0 : ℝ), x * (∑' p, pairFam p x) ∂volume)
      = (∫ x in Ioi (0 : ℝ), ∑' p, x * pairFam p x ∂volume) := by
    rw [setIntegral_congr measurableSet_Ioi
      (fun x hx => (tsum_mul_left).symm : ∀ x ∈ Ioi (0 : ℝ),
        x * (∑' p, pairFam p x) = ∑' p, x * pairFam p x)]
  rw [hIeq]
  exact h

/-! ## Section 8: W2-E — the integrated tail bound -/

/-- The vanishing leg of the telescope: `1/(2 (J + K)) -> 0`
(self-supplied, the `Metric.tendsto_atTop` + `exists_nat_gt` idiom
from the house `tendsto_altHarmonic` proof). -/
private theorem tendsto_one_over_two_add (K : ℕ) :
    Filter.Tendsto (fun J : ℕ => 1 / ((2 * (J + K) : ℕ) : ℝ))
      Filter.atTop (𝓝 (0 : ℝ)) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨M, hM⟩ := exists_nat_gt (1 / ε)
  have hMpos : (0 : ℝ) < (M : ℝ) := by
    have h1 : (0 : ℝ) < 1 / ε := div_pos (by norm_num) hε
    linarith
  have hM1 : (1 : ℕ) ≤ M := by
    have h0 : (0 : ℕ) < M := by exact_mod_cast hMpos
    omega
  refine ⟨M, fun J hJ => ?_⟩
  have hpos : (0 : ℝ) < ((2 * (J + K) : ℕ) : ℝ) :=
    by exact_mod_cast (by omega : (0 : ℕ) < 2 * (J + K))
  have hle : 1 / ((2 * (J + K) : ℕ) : ℝ) ≤ 1 / (M : ℝ) :=
    (one_div_le_one_div
      (by exact_mod_cast (by omega : (0 : ℕ) < 2 * (J + K)))
      (by exact_mod_cast (by omega : (0 : ℕ) < M))).mpr
      (by exact_mod_cast (by omega : (M : ℕ) ≤ 2 * (J + K)))
  have h1 : (1 : ℝ) < ε * (M : ℝ) := by
    have h2 : ε * ((1 / ε : ℝ)) < ε * (M : ℝ) := mul_lt_mul_of_pos_left hM hε
    rw [one_div, mul_inv_cancel₀ hε.ne'] at h2
    exact h2
  have hfin : 1 / (M : ℝ) < ε := (div_lt_iff₀ hMpos).mpr h1
  rw [Real.dist_eq, sub_zero, abs_of_pos (div_pos (by norm_num) hpos)]
  exact hle.trans_lt hfin

/-- The telescope terms are nonnegative (the first denominator is the
smaller one; both are positive from `K >= 1`). -/
private theorem tel2_nonneg {n K : ℕ} (hK : 1 ≤ K) :
    (0 : ℝ) ≤ 1 / ((2 * (n + K) : ℕ) : ℝ)
      - 1 / (((2 * (n + K) : ℕ) + 2 : ℕ) : ℝ) := by
  rw [sub_nonneg]
  exact (one_div_le_one_div
    (by exact_mod_cast Nat.succ_pos ((2 * (n + K) : ℕ) + 1))
    (by exact_mod_cast (by omega : (0 : ℕ) < 2 * (n + K)))).mpr
    (by exact_mod_cast ((Nat.le_succ (2 * (n + K))).trans
      (Nat.le_succ ((2 * (n + K) : ℕ) + 1))))

/-- The telescope's partial-sum identity: the first `J` even-Harmonic
steps sum to `1/(2K) - 1/(2 (J + K))` (induction; the running
`1/(2 (j + K))` cancels against each new term). -/
private theorem tel2_sum_range (K J : ℕ) :
    ∑ j ∈ Finset.range J,
        (1 / ((2 * (j + K) : ℕ) : ℝ)
          - 1 / (((2 * (j + K) : ℕ) + 2 : ℕ) : ℝ))
      = 1 / ((2 * K : ℕ) : ℝ) - 1 / ((2 * (J + K) : ℕ) : ℝ) := by
  induction J with
  | zero => simp
  | succ j ih =>
    rw [Finset.sum_range_succ, ih]
    have hc : ((2 * ((j + 1) + K) : ℕ) : ℝ)
        = (((2 * (j + K) : ℕ) + 2 : ℕ) : ℝ) := by
      exact_mod_cast (by omega :
        (2 * ((j + 1) + K) : ℕ) = (2 * (j + K) : ℕ) + 2)
    rw [hc]
    ring

/-- The telescope sums: the even-Harmonic differences converge to
`1/(2K)` (norm-summability by the shifted-zeta domination; the limit by
the partial-sum identity and the vanishing leg). -/
private theorem tel2_hasSum (K : ℕ) (hK : 1 ≤ K) :
    HasSum (fun n : ℕ =>
      1 / ((2 * (n + K) : ℕ) : ℝ)
        - 1 / (((2 * (n + K) : ℕ) + 2 : ℕ) : ℝ))
      (1 / ((2 * K : ℕ) : ℝ)) := by
  -- the zeta-shift dominator at the offset
  have hz : Summable (fun n : ℕ => 1 / (((n + K + 1 : ℕ) : ℝ) ^ 2)) :=
    summable_zeta_shift.comp_injective (f := fun p : ℕ => 1 / (((p + 1 : ℕ) : ℝ) ^ 2))
      (i := fun n : ℕ => n + K)
      (by intro a b hab; have h' : a + K = b + K := hab; omega)
  have hdom : ∀ n : ℕ, ‖(1 / ((2 * (n + K) : ℕ) : ℝ)
      - 1 / (((2 * (n + K) : ℕ) + 2 : ℕ) : ℝ))‖
      ≤ 1 / (((n + K + 1 : ℕ) : ℝ) ^ 2) := by
    intro n
    have hm1 : (1 : ℝ) ≤ ((n + K : ℕ) : ℝ) := by exact_mod_cast (by omega)
    have hmpos : (0 : ℝ) < ((n + K : ℕ) : ℝ) := by linarith
    have hc1 : ((2 * (n + K) : ℕ) : ℝ) = 2 * ((n + K : ℕ) : ℝ) := by push_cast; ring
    have hc2 : (((2 * (n + K) : ℕ) + 2 : ℕ) : ℝ)
        = 2 * ((n + K : ℕ) : ℝ) + 2 := by push_cast; ring
    have hc3 : ((n + K + 1 : ℕ) : ℝ) = ((n + K : ℕ) : ℝ) + 1 := by push_cast; ring
    rw [Real.norm_eq_abs, abs_of_nonneg (tel2_nonneg hK), hc1, hc2, hc3]
    have hsplit : 1 / (2 * ((n + K : ℕ) : ℝ))
        - 1 / (2 * ((n + K : ℕ) : ℝ) + 2)
        = 2 / ((2 * ((n + K : ℕ) : ℝ)) * (2 * ((n + K : ℕ) : ℝ) + 2)) := by
      field_simp
      ring
    rw [hsplit]
    rw [div_le_div_iff₀
      (by positivity : (0 : ℝ) < (2 * ((n + K : ℕ) : ℝ))
        * (2 * ((n + K : ℕ) : ℝ) + 2))
      (by positivity : (0 : ℝ) < (((n + K : ℕ) : ℝ) + 1) ^ 2)]
    nlinarith [sq_nonneg ((n + K : ℕ) : ℝ), hm1, hmpos]
  -- the NORMED summability (what the iff demands)
  have hdomN : ∀ n : ℕ,
      ‖‖(1 / ((2 * (n + K) : ℕ) : ℝ)
        - 1 / (((2 * (n + K) : ℕ) + 2 : ℕ) : ℝ))‖‖
      ≤ 1 / (((n + K + 1 : ℕ) : ℝ) ^ 2) := by
    intro n
    rw [norm_norm]
    exact hdom n
  have hEsumN : Summable (fun n : ℕ =>
      ‖(1 / ((2 * (n + K) : ℕ) : ℝ)
        - 1 / (((2 * (n + K) : ℕ) + 2 : ℕ) : ℝ))‖) :=
    Summable.of_norm_bounded hz hdomN
  refine (hasSum_iff_tendsto_nat_of_summable_norm hEsumN).mpr ?_
  have hc : Filter.Tendsto (fun n : ℕ => 1 / ((2 * K : ℕ) : ℝ)
      - 1 / ((2 * (n + K) : ℕ) : ℝ)) Filter.atTop
      (𝓝 (1 / ((2 * K : ℕ) : ℝ))) := by
    have h1 := (tendsto_one_over_two_add K).sub_const (1 / ((2 * K : ℕ) : ℝ))
    rw [zero_sub] at h1
    simpa only [neg_sub, neg_neg] using h1.neg
  exact (Filter.tendsto_congr (fun n => (tel2_sum_range K n).symm)).mp hc

/-- The exact absolute value of the pair integral: the alternating
sign makes the piece negative, so the absolute value is the positive
odd-step difference. -/
private theorem abs_integral_x_pairFam (p : ℕ) :
    |∫ x in Ioi (0 : ℝ), x * pairFam p x ∂volume|
      = (1 / 12) * (1 / ((2 * p + 1 : ℕ) : ℝ)
        - 1 / ((2 * p + 2 : ℕ) : ℝ)) := by
  rw [integral_x_pairFam p]
  have hlt : (1 / ((2 * p + 2 : ℕ) : ℝ)) < 1 / ((2 * p + 1 : ℕ) : ℝ) := by
    exact (one_div_lt_one_div
      (by exact_mod_cast Nat.succ_pos ((2 * p : ℕ) + 1))
      (by exact_mod_cast Nat.succ_pos (2 * p))).mpr
      (by exact_mod_cast Nat.lt_succ_self (2 * p + 1))
  rw [abs_of_neg (mul_neg_of_pos_of_neg (by norm_num) (by linarith))]
  ring

/-- The per-piece tail license: the absolute pair integral is dominated
by the even-step telescope difference (`p >= 1` keeps `1/(2p)` honest). -/
private theorem abs_integral_x_pairFam_le (p : ℕ) (hp : 1 ≤ p) :
    |∫ x in Ioi (0 : ℝ), x * pairFam p x ∂volume|
      ≤ (1 / 12) * (1 / ((2 * p : ℕ) : ℝ)
        - 1 / (((2 * p : ℕ) + 2 : ℕ) : ℝ)) := by
  rw [abs_integral_x_pairFam p]
  have hkey : 1 / ((2 * p + 1 : ℕ) : ℝ) ≤ 1 / ((2 * p : ℕ) : ℝ) := by
    have hpos0 : (0 : ℝ) < ((2 * p : ℕ) : ℝ) :=
      by exact_mod_cast (by omega : (0 : ℕ) < 2 * p)
    have hpos1 : (0 : ℝ) < ((2 * p + 1 : ℕ) : ℝ) :=
      by exact_mod_cast (by omega : (0 : ℕ) < 2 * p + 1)
    exact (one_div_le_one_div hpos1 hpos0).mpr
      (by exact_mod_cast (by omega : (2 * p : ℕ) ≤ (2 * p + 1 : ℕ)))
  have hinner : 1 / ((2 * p + 1 : ℕ) : ℝ) - 1 / ((2 * p + 2 : ℕ) : ℝ)
      ≤ 1 / ((2 * p : ℕ) : ℝ) - 1 / (((2 * p : ℕ) + 2 : ℕ) : ℝ) :=
    sub_le_sub_right hkey _
  exact mul_le_mul_of_nonneg_left hinner (by norm_num)

/-- W2-E (THE INTEGRATED TAIL BOUND, unconditional): the integrated tail
of the Lambert series beyond the `2K`-th term vanishes like `O(1/(K+1))`
— the pair-tail's absolute sum is dominated by the scaled even-Harmonic
telescope `(1/12) * (1/(2K))`, cashed at the coarser pre-registered
constant `1/(12 (K+1))`. Receipt: one dominated swap of the pair family
(`hasSum_integral_x_mul_pairFam`), the tail split
(`hasSum_nat_add_iff`), and the one-shot norm bound
(`tsum_of_norm_bounded`) against the telescope's `HasSum`. -/
theorem lambert_integrated_tail_bound (K : ℕ) (hK : 1 ≤ K) :
    |∫ x in Ioi (0 : ℝ), x * (∑' m, lamTerm m x) ∂volume
      - ∫ x in Ioi (0 : ℝ), x * (∑ m ∈ Finset.range (2 * K), lamTerm m x) ∂volume|
      ≤ 1 / (12 * ((K : ℝ) + 1)) := by
  -- step 1: the Lambert tsum integral IS the pair tsum integral (pointwise)
  have hWlam : ∫ x in Ioi (0 : ℝ), x * (∑' m, lamTerm m x) ∂volume
      = ∫ x in Ioi (0 : ℝ), x * (∑' p, pairFam p x) ∂volume := by
    rw [setIntegral_congr measurableSet_Ioi
      (fun x hx => by
        show x * (∑' m, lamTerm m x) = x * (∑' p, pairFam p x)
        rw [pairFam_tsum_eq (Set.mem_Ioi.mp hx)])]
  -- step 2: the partial integral as the finite pair sum
  have hI : ∫ x in Ioi (0 : ℝ), x * (∑ m ∈ Finset.range (2 * K), lamTerm m x) ∂volume
      = ∑ p ∈ Finset.range K, ∫ x in Ioi (0 : ℝ), x * pairFam p x ∂volume := by
    rw [setIntegral_congr measurableSet_Ioi
      (fun x hx => by rw [pair_sum_range K x, Finset.mul_sum]),
      setIntegral_sum_range measurableSet_Ioi
        (fun p _hp => integrable_x_mul_pairFam p)]
  -- step 3: the tail HasSum (the swap + hasSum_nat_add_iff)
  have hadd : HasSum (fun p : ℕ => ∫ x in Ioi (0 : ℝ), x * pairFam p x ∂volume)
      ((∫ x in Ioi (0 : ℝ), x * (∑' p, pairFam p x) ∂volume
        - ∑ p ∈ Finset.range K, ∫ x in Ioi (0 : ℝ), x * pairFam p x ∂volume)
      + ∑ p ∈ Finset.range K, ∫ x in Ioi (0 : ℝ), x * pairFam p x ∂volume) := by
    have hreq : (∫ x in Ioi (0 : ℝ), x * (∑' p, pairFam p x) ∂volume
        - ∑ p ∈ Finset.range K, ∫ x in Ioi (0 : ℝ), x * pairFam p x ∂volume)
        + ∑ p ∈ Finset.range K, ∫ x in Ioi (0 : ℝ), x * pairFam p x ∂volume
        = ∫ x in Ioi (0 : ℝ), x * (∑' p, pairFam p x) ∂volume := by ring
    rw [hreq]
    exact hasSum_integral_x_mul_pairFam
  have htail : HasSum (fun n : ℕ => ∫ x in Ioi (0 : ℝ), x * pairFam (n + K) x ∂volume)
      (∫ x in Ioi (0 : ℝ), x * (∑' p, pairFam p x) ∂volume
        - ∑ p ∈ Finset.range K, ∫ x in Ioi (0 : ℝ), x * pairFam p x ∂volume) :=
    (hasSum_nat_add_iff
      (f := fun p : ℕ => ∫ x in Ioi (0 : ℝ), x * pairFam p x ∂volume) K).mpr hadd
  -- step 4: the scaled telescope HasSum (the one-line mul_left route,
  -- storm-free: HasSum.mul_left, Topology/Algebra/InfiniteSum/Ring.lean:37)
  have hE := tel2_hasSum K hK
  have hg' : HasSum (fun n : ℕ => (1 / 12) * (1 / ((2 * (n + K) : ℕ) : ℝ)
      - 1 / (((2 * (n + K) : ℕ) + 2 : ℕ) : ℝ)))
      ((1 / 12) * (1 / ((2 * K : ℕ) : ℝ))) :=
    hE.mul_left (1 / 12)
  -- step 5: the one-shot norm bound against the telescope's HasSum
  have hbound : ‖∑' n, ∫ x in Ioi (0 : ℝ), x * pairFam (n + K) x ∂volume‖
      ≤ (1 / 12) * (1 / ((2 * K : ℕ) : ℝ)) :=
    tsum_of_norm_bounded hg' (fun n => by
      rw [Real.norm_eq_abs]
      exact abs_integral_x_pairFam_le (n + K) (by omega))
  -- step 6: assembly and the final constant
  rw [hWlam, hI, ← htail.tsum_eq]
  have hbound' := hbound
  rw [Real.norm_eq_abs] at hbound'
  have hcast : ((2 * K : ℕ) : ℝ) = 2 * ((K : ℝ)) := by push_cast; ring
  rw [hcast] at hbound'
  have hKpos : (0 : ℝ) < (K : ℝ) := by exact_mod_cast (by omega : (0 : ℕ) < K)
  have hfin : (1 / 12 : ℝ) * (1 / (2 * (K : ℝ)))
      ≤ 1 / (12 * ((K : ℝ) + 1)) := by
    have h1 : (1 / 12 : ℝ) * (1 / (2 * (K : ℝ)))
        = 1 / (24 * (K : ℝ)) := by
      field_simp
      ring
    rw [h1]
    rw [div_le_div_iff₀ (mul_pos (by norm_num) hKpos)
      (mul_pos (by norm_num) (by linarith))]
    have hK' : (1 : ℝ) ≤ ((K : ℕ) : ℝ) := by exact_mod_cast hK
    have hlin : (12 : ℝ) * ((K : ℝ) + 1) = 12 * ((K : ℝ)) + 12 := by ring
    rw [hlin]
    linarith
  exact hbound'.trans hfin

/-! ## Section 9: W2-F — the assembly and the cascade cash-out -/

/-- W2-F, THE ASSEMBLY (conditional on the single named Lambert-Jacobi
`HasSum` hypothesis W2-A, `LambJacobiHyp`, never claimed): the honest
object of the 1111 arm closes — `ZAdic1111 = -(2/3) * pi^2 * log 2`.
Receipt: the dominated swap (`hasSum_integral_x_mul_pairFam`) and
`HasSum.unique` identify the integrated pair sum with the scaled
regrouped harmonic `-(1/12) * log 2` (`hasSum_pair_harmonic.mul_left`,
Section 7); the hypothesis and the pointwise regroup (`pairFam_tsum_eq`,
Section 5) identify the same integrand with
`(1/8) * x * (thetaFour x ^ 4 - 1)` pointwise on `Ioi 0`. The hypothesis
is consumed exactly once, at the pointwise identification. -/
theorem zadic1111_eq_of_lambJacobiHyp (hyp : LambJacobiHyp) :
    ZAdic1111 = -(2 / 3 : ℝ) * Real.pi ^ 2 * Real.log 2 := by
  -- step 1: the integral family has the scaled-harmonic value
  have hint : HasSum (fun p : ℕ => ∫ x in Ioi (0 : ℝ), x * pairFam p x ∂volume)
      (-(1 / 12 : ℝ) * Real.log 2) :=
    (hasSum_pair_harmonic.mul_left (-(1 / 12 : ℝ))).congr_fun
      (fun p => by rw [integral_x_pairFam p]; ring)
  -- step 2: uniqueness vs the swap
  have hW : ∫ x in Ioi (0 : ℝ), x * (∑' p, pairFam p x) ∂volume
      = -(1 / 12 : ℝ) * Real.log 2 :=
    hasSum_integral_x_mul_pairFam.unique hint
  -- step 3: the pointwise identification (the hypothesis consumed ONCE)
  have hpt : ∀ x ∈ Ioi (0 : ℝ),
      x * (∑' p, pairFam p x) = (1 / 8 : ℝ) * (x * (thetaFour x ^ 4 - 1)) := by
    intro x hx
    have hx0 : (0 : ℝ) < x := Set.mem_Ioi.mp hx
    rw [pairFam_tsum_eq hx0, (hyp x hx0).tsum_eq]
    ring
  -- step 4: the constant-scaled integral identity
  have hW' : (1 / 8 : ℝ)
      * ∫ x in Ioi (0 : ℝ), x * (thetaFour x ^ 4 - 1) ∂volume
      = -(1 / 12 : ℝ) * Real.log 2 := by
    rw [← integral_const_mul (1 / 8 : ℝ)
      (fun x : ℝ => x * (thetaFour x ^ 4 - 1)), ← hW]
    exact setIntegral_congr measurableSet_Ioi
      (fun x hx => (hpt x hx).symm)
  -- step 5: solve for the kernel integral (8 * hW' isolates it)
  have hJ : ∫ x in Ioi (0 : ℝ), x * (thetaFour x ^ 4 - 1) ∂volume
      = -(2 / 3 : ℝ) * Real.log 2 := by
    have h8 : (8 : ℝ) * ((1 / 8 : ℝ)
        * ∫ x in Ioi (0 : ℝ), x * (thetaFour x ^ 4 - 1) ∂volume)
        = ∫ x in Ioi (0 : ℝ), x * (thetaFour x ^ 4 - 1) ∂volume := by
      field_simp
    have h8' : (8 : ℝ) * (-(1 / 12 : ℝ) * Real.log 2)
        = -(2 / 3 : ℝ) * Real.log 2 := by
      field_simp
      ring
    rw [← h8, hW', h8']
  -- step 6: assemble ZAdic1111
  have hZ : ZAdic1111 = Real.pi ^ 2
      * ∫ x in Ioi (0 : ℝ), x * (thetaFour x ^ 4 - 1) ∂volume := rfl
  rw [hZ, hJ]
  ring

/-- The cascade cash-out, conditional on W2-A (STONE A composed through
the unconditional R239 anchor): `ZAdic1100 = -(1/6) * pi^2 * log 2`. -/
theorem zadic1100_eq_of_lambJacobiHyp (hyp : LambJacobiHyp) :
    ZAdic1100 = -(1 / 6 : ℝ) * Real.pi ^ 2 * Real.log 2 := by
  rw [ZAdic1100_eq_quarter_ZAdic1111_unconditional,
    zadic1111_eq_of_lambJacobiHyp hyp]
  ring

/-- The cascade cash-out, conditional on W2-A (STONE B composed through
the unconditional R239 anchors): `ZAdic1000 + ZAdic1110 = -(1/12) * pi^2
* log 2`. -/
theorem zadic1000_add_ZAdic1110_eq_of_lambJacobiHyp (hyp : LambJacobiHyp) :
    ZAdic1000 + ZAdic1110 = -(1 / 12 : ℝ) * Real.pi ^ 2 * Real.log 2 := by
  rw [ZAdic1000_add_ZAdic1110_eq_unconditional,
    zadic1111_eq_of_lambJacobiHyp hyp]
  ring

end YangMills.DualBook
