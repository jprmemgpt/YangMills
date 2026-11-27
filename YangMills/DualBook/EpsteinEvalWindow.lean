/-
YANGMILLS DUAL BOOK — R240 STONE A: THE FIRST EPSTEIN EVALUATION.

The W1 book's final cascade leg: the honest object `ZAdic1111`
(the s = 2 normalization of the 1111 arm, `ThetaAdicArm.lean`) gets its
closed-form value

  ZAdic1111 = -(2/3) * pi^2 * log 2

conditional on ONE named classical window, the Lambert-Jacobi identity
for the fourth power of theta-4 (W2-A below), which the vintage's
complex-only `Mathlib.NumberTheory.ModularForms.JacobiTheta` does not
carry. The hypothesis is stated in `HasSum` form (it therefore carries
summability of the Lambert family, which the window needs anyway); the
`tsum` form `theta4 q ^ 4 = 1 + 8 * ∑' ...` follows by `HasSum.tsum_eq`.

Every other input is paid here, unconditionally:

  W2-B:  sum' k, (-1)^k / (k+1)^2 = pi^2/12  (eta(2)), from Mathlib's
         `hasSum_zeta_two` by the even/odd parity split.
  W2-C:  the ordered partial sums of the alternating harmonic converge
         to log 2, by the exact finite geometric identity on [0,1]
         with error at most 1/(N+1). No Abel theorem, no unordered
         HasSum (the alternating harmonic is only conditionally
         convergent, so this is a TENDSTO of partial sums).
  W2-D:  each Lambert integral evaluates to
         int_0^inf x e^{-pi j x}/(1+e^{-pi j x}) dx = 1/(12 j^2),
         by the geometric expansion
         e^{-jx}/(1+e^{-jx}) = sum' (-1)^k e^{-(k+1)jx}
         swapped under `hasSum_integral_of_dominated_convergence`
         (the ENNReal-free swap tool).
  W2-E:  the N-tail of the Lambert series, integrated against x,
         vanishes like O(1/(N+1)): NO double-sum swap is ever
         performed; the tail is bounded pointwise by the elementary
         chain x * |term| = (1/pi) u e^{-u} <= (1/pi) e^{-u/2}
         (from u <= e^{u/2}, itself just 1 + t <= e^t plus a perfect
         square), summed against a geometric tail, split into two
         regions, and integrated against two Gamma-evaluated bounds.
  W2-F:  the assembly: Lambda = -(2/3) log 2, hence the closed form.

The R239 cascade (JacobiAnchorsTime.lean, master 71502f9) then cashes
three of the four arms in one shot: `ZAdic1100 = (1/4) ZAdic1111` and
`ZAdic1000 + ZAdic1110 = (1/8) ZAdic1111` are unconditional, so both
closed forms below ride the single hypothesis of the 1111 arm.

WITNESS (bench, frozen; probes `r240_probe1`/`r240_probe2`, 2026-11-26):
  t=0.10  theta4^4 = 3.633761709318716e-11, lambert = 3.633715550677152e-11
  t=0.50  theta4^4 = 0.1195180020155391,    lambert = 0.1195180020155390
  t=1.00  theta4^4 = 0.6966019648428387,    lambert = 0.6966019648428383
  (worst |diff| 4.6e-16 across the probe)
  ZAdic1111 (Simpson) = -4.56072564257 (12 d.p.)
  -(2/3) pi^2 log 2   = -4.56072564257 (12 d.p.)

HOUSE LAW (pre-registered at the R240 opener, c1672): zero sorry; axioms
[propext, Classical.choice, Quot.sound] only; scope THIS ARITHMETIC only
(the Lambert identity rides as a NAMED hypothesis, never claimed); bench
frozen at 100.0; plain-text .lean on the card; the Clay crossing is
never claimed; no push (the sibling court seals).
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
import YangMills.DualBook.ThetaAdicArm
import YangMills.DualBook.JacobiAnchorsTime

set_option maxHeartbeats 512000

namespace YangMills.DualBook

open MeasureTheory Real Set Topology

/-! ## Elementary real bounds -/

/-- `exp 1 >= 2`, straight from `1 + x <= exp x`. -/
private theorem two_le_exp_one : (2 : ℝ) ≤ Real.exp 1 := by
  have h := Real.add_one_le_exp (1 : ℝ)
  linarith

/-- The one deep trick of the window: `u <= e^{u/2}` for `u >= 0`.
For `u <= 2` this is `1 + u/2 <= e^{u/2}`; for `u >= 2` it is the
perfect square `(1 + u/4)^2 - u = (u-4)^2/16 >= 0` under
`e^{u/4} >= 1 + u/4`. -/
private theorem le_exp_half {u : ℝ} (hu : 0 ≤ u) : u ≤ Real.exp (u / 2) := by
  rcases lt_or_ge u 2 with h | h
  · have h0 : u / 2 + 1 ≤ Real.exp (u / 2) := Real.add_one_le_exp _
    have h1 : 1 + u / 2 ≤ Real.exp (u / 2) := by linarith
    have h2 : 1 - u / 2 ≥ 0 := by linarith
    linarith
  · have h2 : 1 + u / 4 ≤ Real.exp (u / 4) := by
      have := Real.add_one_le_exp (u / 4)
      linarith
    have hsplit : Real.exp (u / 2) = Real.exp (u / 4) * Real.exp (u / 4) := by
      rw [← Real.exp_add]; ring
    have hsq : (u - 4) ^ 2 ≥ 0 := sq_nonneg _
    have key : (1 + u / 4) ^ 2 - u = (u - 4) ^ 2 / 16 := by field_simp; ring
    have hnn : 0 ≤ 1 + u / 4 := by linarith
    have hmono : (1 + u / 4) * (1 + u / 4) ≤ Real.exp (u / 4) * Real.exp (u / 4) := by
      gcongr
    have hle : u ≤ (1 + u / 4) * (1 + u / 4) := by
      have := key
      nlinarith [hsq]
    rw [hsplit]
    linarith

/-- `e^{-y} < 1` for `y > 0`, i.e. `0 < 1 - e^{-y}`. -/
private theorem one_sub_exp_pos {y : ℝ} (hy : 0 < y) : 0 < 1 - Real.exp (-y) := by
  have h : Real.exp (-y) < Real.exp 0 := Real.exp_lt_exp.mpr (by linarith)
  simpa using h

/-- The small-`y` bound: `1/(1 - e^{-y}) <= (1+y)/y`, from
`1 + y <= e^y` (equivalently `e^{-y} <= 1/(1+y)`). -/
private theorem inv_one_sub_exp_neg_le {y : ℝ} (hy : 0 < y) :
    1 / (1 - Real.exp (-y)) ≤ (1 + y) / y := by
  have hy' : 0 < 1 - Real.exp (-y) := one_sub_exp_pos hy
  have hy2 : 0 < y + 1 := by linarith
  have h3 : y + 1 ≤ Real.exp y := Real.add_one_le_exp y
  have hkey : Real.exp (-y) * (y + 1) ≤ 1 := by
    have h5 : Real.exp (-y) * Real.exp y = 1 := by
      rw [← Real.exp_add]
      simp
    have h6 : Real.exp (-y) * (y + 1) ≤ Real.exp (-y) * Real.exp y :=
      mul_le_mul_of_nonneg_left h3 (Real.exp_pos (-y)).le
    exact h6.trans_eq h5
  field_simp
  nlinarith [hkey]

/-- The large-`y` bound: `1/(1 - e^{-y}) <= 2` once `y >= 1`, because
`e^{-1} <= 1/2`. -/
private theorem inv_one_sub_exp_neg_le' {y : ℝ} (hy : 1 ≤ y) :
    1 / (1 - Real.exp (-y)) ≤ 2 := by
  have hy' : 0 < 1 - Real.exp (-y) := one_sub_exp_pos (by linarith)
  have h1 : Real.exp (-y) ≤ Real.exp (-1) := Real.exp_le_exp.mpr (by linarith)
  have h2 : Real.exp (-1) ≤ 1 / 2 := by
    have h3 : (2 : ℝ) ≤ Real.exp 1 := two_le_exp_one
    have h5 : Real.exp (-1) * 2 ≤ 1 := by
      have h6 : Real.exp (-1) * Real.exp 1 = 1 := by
        rw [← Real.exp_add]
        simp
      have h7 : Real.exp (-1) * 2 ≤ Real.exp (-1) * Real.exp 1 :=
        mul_le_mul_of_nonneg_left h3 (Real.exp_pos (-1)).le
      exact h7.trans_eq h6
    rw [le_div_iff₀ (show (0 : ℝ) < 2 by norm_num)]
    exact h5
  have h3 : Real.exp (-y) ≤ 1 / 2 := h1.trans h2
  have h4 : 1 - Real.exp (-y) ≥ 1 / 2 := by linarith
  rw [div_le_iff₀ hy']
  linarith

/-- Own helper (kept off the vintage-name lottery):
`exp (n * t) = exp t ^ n`. -/
private theorem exp_pow_self (n : ℕ) (t : ℝ) : Real.exp (n * t) = Real.exp t ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    have h1 : ((n + 1 : ℕ) : ℝ) * t = (n : ℝ) * t + t := by
      push_cast
      ring
    rw [h1, Real.exp_add, ih, pow_succ]

/-! ## The Gamma-evaluated exponential integrals (house wrappers) -/

/-- `int_0^inf e^{-b x} dx = 1/b` for `b > 0`, from Mathlib's
`integral_rpow_mul_exp_neg_mul_rpow` at `p = 1, q = 0` with
`Gamma 1 = 1`. -/
private theorem integral_exp_neg {b : ℝ} (hb : 0 < b) :
    ∫ x in Ioi (0 : ℝ), Real.exp (-b * x) ∂volume = 1 / b := by
  have h := integral_rpow_mul_exp_neg_mul_rpow (p := 1) (q := 0) (b := b)
    (by norm_num) (by norm_num) hb
  simp only [Real.rpow_zero, one_mul, Real.rpow_one, zero_add, div_one, mul_one] at h
  rw [h, Real.Gamma_one, mul_one, Real.rpow_neg_one, inv_eq_one_div]

/-- `int_0^inf x e^{-b x} dx = 1/b^2` for `b > 0`, same source with
`q = 1` and `Gamma 2 = 1` (house-paid since the Mellin window). -/
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

/-! ## Set-integral helpers (indicator bridges, house style) -/

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

/-! ## W2-B: eta(2) = pi^2/12 -/

/-- The alternating square-inverse family sums to `pi^2/12`: eta(2),
paid unconditionally from Mathlib's `hasSum_zeta_two` by the even/odd
parity split (`HasSum.even_add_odd`, the L-vintage filter-carrying
form). -/
theorem hasSum_eta_two :
    HasSum (fun k : ℕ => (-1 : ℝ) ^ k / (((k + 1 : ℕ) : ℝ) ^ 2)) (Real.pi ^ 2 / 12) := by
  have hz : HasSum (fun n : ℕ => (1 : ℝ) / ((n : ℕ) : ℝ) ^ 2) (Real.pi ^ 2 / 6) :=
    hasSum_zeta_two
  -- the shifted family (n+1): same value; the prime iff variant forces a
  -- defeq check of `pi^2/6 - sum range 1` against `pi^2/6`, and the
  -- `1/0^2 = 0` field convention is NOT cheap whnf (it spiraled at 512000
  -- heartbeats in R239-era builds). The non-prime iff plus an explicit
  -- `sum range 1` rewrite keeps the zero division inside `simp`, bounded.
  have hshift : HasSum (fun k : ℕ => (1 : ℝ) / (((k + 1 : ℕ) : ℝ) ^ 2))
      (Real.pi ^ 2 / 6) := by
    have hz' : HasSum (fun n : ℕ => (1 : ℝ) / ((n : ℕ) : ℝ) ^ 2)
        (Real.pi ^ 2 / 6
          + ∑ i ∈ Finset.range 1, (1 : ℝ) / (((i : ℕ) : ℝ) ^ 2)) := by
      rw [Finset.range_one, Finset.sum_singleton,
        show (1 : ℝ) / (((0 : ℕ) : ℝ) ^ 2) = 0 by simp, add_zero]
      exact hz
    exact (hasSum_nat_add_iff
      (f := fun n : ℕ => (1 : ℝ) / ((n : ℕ) : ℝ) ^ 2) 1).mpr hz'
  -- strand summabilities
  have hSummAll : Summable (fun n : ℕ => (1 : ℝ) / ((n : ℕ) : ℝ) ^ 2) := hz.summable
  have hSummOdd : Summable (fun k : ℕ => (1 : ℝ) / (((2 * k + 1) : ℕ) : ℝ) ^ 2) :=
    hSummAll.comp_injective (f := fun n : ℕ => (1 : ℝ) / ((n : ℕ) : ℝ) ^ 2)
      (i := fun k : ℕ => 2 * k + 1)
      (by
        intro a b hab
        have h' : 2 * a + 1 = 2 * b + 1 := hab
        omega)
  -- the odd-integer strand (even members of the target family):
  -- HasSum 1/(2k+1)^2 (pi^2/8), value from the parity identity
  have hOddStrand : HasSum (fun k : ℕ => (1 : ℝ) / (((2 * k + 1) : ℕ) : ℝ) ^ 2)
      (Real.pi ^ 2 / 8) := by
    have hSummEven : Summable (fun k : ℕ => (1 : ℝ) / (((2 * k) : ℕ) : ℝ) ^ 2) :=
      hSummAll.comp_injective (f := fun n : ℕ => (1 : ℝ) / ((n : ℕ) : ℝ) ^ 2)
        (i := fun k : ℕ => 2 * k) (mul_right_injective₀ (two_ne_zero' ℕ))
    -- even strand of the zeta family: (1/4) * zeta, since 1/(2k)^2 = (1/4)/k^2
    -- (the equation is stated in `•` form to match `const_smul`, and
    -- parenthesized: `•` binds tighter than `/`)
    have hEvenFamEq : ∀ k : ℕ, (1 : ℝ) / (((2 * k) : ℕ) : ℝ) ^ 2
        = (1 / 4 : ℝ) • ((1 : ℝ) / ((k : ℕ) : ℝ) ^ 2) := by
      intro k
      rw [smul_eq_mul]
      rcases Nat.eq_zero_or_pos k with rfl | hk
      · simp [div_zero]
      · have hcast : (((2 * k) : ℕ) : ℝ) = 2 * ((k : ℕ) : ℝ) := by push_cast; ring
        rw [hcast, mul_pow]
        field_simp
        ring
    have hEven := (hz.const_smul (1 / 4 : ℝ)).congr_fun (fun k => hEvenFamEq k)
    have hEvenVal : (1 / 4 : ℝ) • (Real.pi ^ 2 / 6) = Real.pi ^ 2 / 24 := by
      rw [smul_eq_mul]
      ring
    rw [hEvenVal] at hEven
    -- the tsum parity identity, then the value
    have hOddTsum : ∑' k : ℕ, (1 : ℝ) / (((2 * k + 1) : ℕ) : ℝ) ^ 2 = Real.pi ^ 2 / 8 := by
      have hpar := tsum_even_add_odd (f := fun n : ℕ => (1 : ℝ) / ((n : ℕ) : ℝ) ^ 2)
        hSummEven hSummOdd
      rw [hEven.tsum_eq, hz.tsum_eq] at hpar
      linarith
    have h := hSummOdd.hasSum
    rw [hOddTsum] at h
    exact h
  -- the even-integer strand (odd members of the target family):
  -- HasSum -1/(2(k+1))^2 (-pi^2/24) = -(1/4) * shifted zeta
  have hEvenIntStrand : HasSum (fun k : ℕ => -((1 : ℝ) / (((2 * (k + 1)) : ℕ) : ℝ) ^ 2))
      (-(Real.pi ^ 2 / 24)) := by
    have hEq : ∀ k : ℕ, (1 : ℝ) / (((2 * (k + 1)) : ℕ) : ℝ) ^ 2
        = (1 / 4 : ℝ) • ((1 : ℝ) / (((k + 1 : ℕ) : ℝ) ^ 2)) := by
      intro k
      rw [smul_eq_mul]
      have hcast : (((2 * (k + 1)) : ℕ) : ℝ) = 2 * (((k + 1 : ℕ) : ℝ)) := by push_cast; ring
      rw [hcast, mul_pow]
      field_simp
      ring
    have hbase := (hshift.const_smul (1 / 4 : ℝ)).congr_fun (fun k => hEq k)
    have hval : (1 / 4 : ℝ) • (Real.pi ^ 2 / 6) = Real.pi ^ 2 / 24 := by
      rw [smul_eq_mul]
      ring
    rw [hval] at hbase
    exact hbase.neg
  -- assemble the target family by even_add_odd
  have hT : HasSum (fun k : ℕ => (-1 : ℝ) ^ k / (((k + 1 : ℕ) : ℝ) ^ 2))
      (Real.pi ^ 2 / 8 + -(Real.pi ^ 2 / 24)) := by
    refine HasSum.even_add_odd ?_ ?_
    · refine hOddStrand.congr_fun ?_
      intro k
      have hpow : (-1 : ℝ) ^ (2 * k) = 1 := by rw [pow_mul]; norm_num
      show (-1 : ℝ) ^ (2 * k) / ((((2 * k : ℕ) + 1 : ℕ) : ℝ) ^ 2)
          = (1 : ℝ) / (((2 * k + 1 : ℕ) : ℝ) ^ 2)
      rw [hpow]
    · refine hEvenIntStrand.congr_fun ?_
      intro k
      have hpow : (-1 : ℝ) ^ (2 * k + 1) = -1 := by
        have h1 : (-1 : ℝ) ^ (2 * k) = 1 := by rw [pow_mul]; norm_num
        rw [pow_add, h1, pow_one, one_mul]
      have hidx : ((2 * k + 1 : ℕ) + 1) = 2 * (k + 1) := by ring
      show (-1 : ℝ) ^ (2 * k + 1) / ((((2 * k + 1 : ℕ) + 1 : ℕ) : ℝ) ^ 2)
          = -((1 : ℝ) / (((2 * (k + 1)) : ℕ) : ℝ) ^ 2)
      rw [hpow, hidx, neg_div]
  have hval : Real.pi ^ 2 / 8 + -(Real.pi ^ 2 / 24) = Real.pi ^ 2 / 12 := by ring
  rw [hval] at hT
  exact hT

/-! ## W2-C: the alternating harmonic tends to log 2 -/

private theorem integral_one_add_inv :
    ∫ x in (0 : ℝ)..1, (1 + x) ⁻¹ ∂volume = Real.log 2 := by
  have hcont : ContinuousOn (fun x : ℝ => (1 + x) ⁻¹) (Set.uIcc (0 : ℝ) 1) := by
    have hc : Continuous (fun x : ℝ => 1 + x) := by continuity
    refine ContinuousOn.inv₀ hc.continuousOn ?_
    intro x hx
    have hx0 : 0 ≤ x := by
      rcases Set.mem_uIcc.mp hx with h | h
      · exact h.1
      · linarith
    show (1 : ℝ) + x ≠ 0
    linarith
  have hint : IntervalIntegrable (fun x : ℝ => (1 + x) ⁻¹) volume 0 1 :=
    hcont.intervalIntegrable
  have hderiv : ∀ x ∈ Set.uIcc (0 : ℝ) 1,
      HasDerivAt (fun y => Real.log (1 + y)) ((1 + x) ⁻¹) x := by
    intro x hx
    have hx0 : 0 ≤ x := by
      rcases Set.mem_uIcc.mp hx with h | h
      · exact h.1
      · linarith
    have hx1 : (1 : ℝ) + x ≠ 0 := by linarith
    have h1 : HasDerivAt (fun y : ℝ => 1 + y) 1 x := (hasDerivAt_id x).const_add 1
    have hlog : HasDerivAt Real.log ((1 + x) ⁻¹) (1 + x) := Real.hasDerivAt_log hx1
    have h2 := hlog.comp x h1
    simpa [Function.comp_def, mul_one] using h2
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (f := fun y => Real.log (1 + y)) (f' := fun x => (1 + x) ⁻¹) hderiv hint
  rw [hFTC, add_zero, Real.log_one, sub_zero]
  congr 1
  norm_num

private theorem integral_x_pow (N : ℕ) :
    ∫ x in (0 : ℝ)..1, x ^ N ∂volume = 1 / (((N + 1 : ℕ) : ℝ)) := by
  have hint : IntervalIntegrable (fun x : ℝ => x ^ N) volume 0 1 :=
    (continuous_id.pow _).intervalIntegrable 0 1
  have hne : (((N + 1 : ℕ) : ℝ)) ≠ 0 := by
    exact_mod_cast (Nat.succ_ne_zero N)
  have hderiv : ∀ x ∈ Set.uIcc (0 : ℝ) 1,
      HasDerivAt (fun y : ℝ => y ^ (N + 1) / (((N + 1 : ℕ) : ℝ))) (x ^ N) x := by
    intro x _
    have h2 := (hasDerivAt_pow (N + 1) x).div_const (((N + 1 : ℕ) : ℝ))
    rw [Nat.add_sub_cancel] at h2
    have h4 : (((N + 1 : ℕ) : ℝ) * x ^ N) / (((N + 1 : ℕ) : ℝ)) = x ^ N :=
      mul_div_cancel_left₀ _ hne
    rw [h4] at h2
    exact h2
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (f := fun y : ℝ => y ^ (N + 1) / (((N + 1 : ℕ) : ℝ))) (f' := fun x : ℝ => x ^ N)
      hderiv hint
  rw [hFTC]
  have h0 : ((0 : ℝ)) ^ (N + 1) = 0 := zero_pow (by exact_mod_cast (Nat.succ_ne_zero N))
  rw [h0, zero_div, sub_zero, one_pow]

/-- The exact finite geometric identity, by induction (pure ring). -/
private theorem geo_ident_prod (N : ℕ) (x : ℝ) :
    (1 + x) * ∑ n ∈ Finset.range N, (-1 : ℝ) ^ n * x ^ n
      = 1 - (-1 : ℝ) ^ N * x ^ N := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Finset.sum_range_succ, mul_add, ih]
    have h1 : (-1 : ℝ) ^ (N + 1) = (-1 : ℝ) ^ N * (-1 : ℝ) := by rw [pow_succ]
    have h2 : x ^ (N + 1) = x ^ N * x := by rw [pow_succ]
    rw [h1, h2]
    ring

/-- The division form of the finite geometric identity. -/
private theorem geo_ident_div (N : ℕ) {x : ℝ} (hx1 : (1 : ℝ) + x ≠ 0) :
    (1 + x) ⁻¹ = ∑ n ∈ Finset.range N, (-1 : ℝ) ^ n * x ^ n
      + (-1 : ℝ) ^ N * x ^ N / (1 + x) := by
  have hlhs : ((1 + x) ⁻¹ - (-1 : ℝ) ^ N * x ^ N / (1 + x)) * (1 + x)
      = 1 - (-1 : ℝ) ^ N * x ^ N := by
    rw [sub_mul, inv_mul_cancel₀ hx1, div_mul_cancel₀ _ hx1]
  have hrhs : (∑ n ∈ Finset.range N, (-1 : ℝ) ^ n * x ^ n) * (1 + x)
      = 1 - (-1 : ℝ) ^ N * x ^ N := by
    rw [mul_comm, geo_ident_prod N x]
  have hcancel : (1 + x) ⁻¹ - (-1 : ℝ) ^ N * x ^ N / (1 + x)
      = ∑ n ∈ Finset.range N, (-1 : ℝ) ^ n * x ^ n :=
    mul_left_injective₀ hx1 (by
      show ((1 + x)⁻¹ - (-1 : ℝ) ^ N * x ^ N / (1 + x)) * (1 + x)
          = (∑ n ∈ Finset.range N, (-1 : ℝ) ^ n * x ^ n) * (1 + x)
      rw [hlhs, hrhs])
  linarith

private theorem integral_sum_range_pow (N : ℕ) :
    ∫ x in (0 : ℝ)..1, ∑ n ∈ Finset.range N, (-1 : ℝ) ^ n * x ^ n ∂volume
      = ∑ n ∈ Finset.range N, (-1 : ℝ) ^ n / (((n + 1 : ℕ) : ℝ)) := by
  induction N with
  | zero => simp
  | succ N ih =>
    have hintS : IntervalIntegrable
        (fun x : ℝ => ∑ n ∈ Finset.range N, (-1 : ℝ) ^ n * x ^ n) volume 0 1 :=
      Continuous.intervalIntegrable
        (continuous_finsetSum _ fun n _ => by fun_prop) 0 1
    have hintN : IntervalIntegrable (fun x : ℝ => (-1 : ℝ) ^ N * x ^ N) volume 0 1 :=
      Continuous.intervalIntegrable (by fun_prop) 0 1
    have hsplit : ∀ x : ℝ, ∑ n ∈ Finset.range (N + 1), (-1 : ℝ) ^ n * x ^ n
        = (∑ n ∈ Finset.range N, (-1 : ℝ) ^ n * x ^ n) + (-1 : ℝ) ^ N * x ^ N :=
      fun x => Finset.sum_range_succ ..
    rw [intervalIntegral.integral_congr (fun x _ => hsplit x),
      intervalIntegral.integral_add hintS hintN, ih,
      intervalIntegral.integral_const_mul,
      integral_x_pow N,
      Finset.sum_range_succ]
    have hsign : ((-1 : ℝ) ^ N) * (1 / (((N + 1 : ℕ) : ℝ)))
        = (-1 : ℝ) ^ N / (((N + 1 : ℕ) : ℝ)) := by
      rw [mul_one_div]
    rw [hsign]

/-- The alternating harmonic partial sums tend to log 2: an ORDERED
convergence statement (the family is only conditionally convergent, so
no unordered `HasSum` exists), by the exact finite geometric identity
on [0,1] with error at most 1/(N+1). -/
theorem tendsto_altHarmonic :
    Filter.Tendsto (fun N => ∑ n ∈ Finset.range N, (-1 : ℝ) ^ n / (((n + 1 : ℕ) : ℝ)))
      Filter.atTop (𝓝 (Real.log 2)) := by
  have habsone : ∀ N : ℕ, |((-1 : ℝ) ^ N)| ≤ 1 := by
    intro N
    rw [abs_pow]
    norm_num
  have hkey : ∀ N : ℕ,
      |∑ n ∈ Finset.range N, (-1 : ℝ) ^ n / (((n + 1 : ℕ) : ℝ)) - Real.log 2|
        ≤ 1 / (((N + 1 : ℕ) : ℝ)) := by
    intro N
    have hx0of : ∀ x ∈ Set.uIcc (0 : ℝ) 1, 0 ≤ x := by
      intro x hx
      rcases Set.mem_uIcc.mp hx with h | h
      · exact h.1
      · linarith
    have hcont1 : ContinuousOn (fun x : ℝ => (1 + x) ⁻¹) (Set.uIcc (0 : ℝ) 1) := by
      have hc : Continuous fun x : ℝ => 1 + x := by continuity
      refine ContinuousOn.inv₀ hc.continuousOn ?_
      intro x hx
      have hx0 : 0 ≤ x := hx0of x hx
      show (1 : ℝ) + x ≠ 0
      linarith
    have hint1 : IntervalIntegrable (fun x : ℝ => (1 + x) ⁻¹) volume 0 1 :=
      hcont1.intervalIntegrable
    have hintS : IntervalIntegrable
        (fun x : ℝ => ∑ n ∈ Finset.range N, (-1 : ℝ) ^ n * x ^ n) volume 0 1 :=
      Continuous.intervalIntegrable
        (continuous_finsetSum _ fun n _ => by fun_prop) 0 1
    have hcontT : ContinuousOn
        (fun x : ℝ => (-1 : ℝ) ^ N * x ^ N / (1 + x)) (Set.uIcc (0 : ℝ) 1) := by
      have hcT1 : Continuous fun x : ℝ => (-1 : ℝ) ^ N * x ^ N := by continuity
      have hcT2 : Continuous fun x : ℝ => 1 + x := by continuity
      refine ContinuousOn.div hcT1.continuousOn hcT2.continuousOn ?_
      intro x hx
      have hx0 : 0 ≤ x := hx0of x hx
      show (1 : ℝ) + x ≠ 0
      linarith
    have hintT : IntervalIntegrable
        (fun x : ℝ => (-1 : ℝ) ^ N * x ^ N / (1 + x)) volume 0 1 :=
      hcontT.intervalIntegrable
    have hcontP : ContinuousOn (fun x : ℝ => x ^ N / (1 + x)) (Set.uIcc (0 : ℝ) 1) := by
      have hcP1 : Continuous fun x : ℝ => x ^ N := by continuity
      have hcP2 : Continuous fun x : ℝ => 1 + x := by continuity
      refine ContinuousOn.div hcP1.continuousOn hcP2.continuousOn ?_
      intro x hx
      have hx0 : 0 ≤ x := hx0of x hx
      show (1 : ℝ) + x ≠ 0
      linarith
    have hintP : IntervalIntegrable (fun x : ℝ => x ^ N / (1 + x)) volume 0 1 :=
      hcontP.intervalIntegrable
    have hcontM : ContinuousOn
        (fun x : ℝ => -((-1 : ℝ) ^ N * x ^ N / (1 + x))) (Set.uIcc (0 : ℝ) 1) :=
      hcontT.neg
    have hintM : IntervalIntegrable
        (fun x : ℝ => -((-1 : ℝ) ^ N * x ^ N / (1 + x))) volume 0 1 :=
      hcontM.intervalIntegrable
    have hintX : IntervalIntegrable (fun x : ℝ => x ^ N) volume 0 1 :=
      (continuous_id.pow _).intervalIntegrable 0 1
    have hpw : ∀ x ∈ Set.uIcc (0 : ℝ) 1,
        (1 + x) ⁻¹ = (∑ n ∈ Finset.range N, (-1 : ℝ) ^ n * x ^ n)
          + (-1 : ℝ) ^ N * x ^ N / (1 + x) := by
      intro x hx
      have hx0 : 0 ≤ x := hx0of x hx
      have hx1 : (1 : ℝ) + x ≠ 0 := by linarith
      exact geo_ident_div N hx1
    -- log 2 = S N + (the tail integral)
    have hlog : Real.log 2
        = (∑ n ∈ Finset.range N, (-1 : ℝ) ^ n / (((n + 1 : ℕ) : ℝ)))
          + ∫ x in (0 : ℝ)..1, (-1 : ℝ) ^ N * x ^ N / (1 + x) ∂volume := by
      have hInt : ∫ x in (0 : ℝ)..1, (1 + x) ⁻¹ ∂volume
          = ∫ x in (0 : ℝ)..1, (∑ n ∈ Finset.range N, (-1 : ℝ) ^ n * x ^ n)
              + (-1 : ℝ) ^ N * x ^ N / (1 + x) ∂volume := by
        refine intervalIntegral.integral_congr (fun x hx => hpw x hx)
      rw [← integral_one_add_inv, hInt, intervalIntegral.integral_add hintS hintT,
        integral_sum_range_pow N]
    -- |S N - log 2| = |tail integral|, bounded by signed monotonicity
    have hTpos : ∀ x ∈ Set.Icc (0 : ℝ) 1, 0 ≤ x ^ N / (1 + x) := by
      intro x hx
      have hx0 : 0 ≤ x := (Set.mem_Icc.mp hx).1
      have hx1 : (0 : ℝ) < 1 + x := by positivity
      apply div_nonneg
      · exact pow_nonneg hx0 N
      · linarith
    have hTle : ∀ x ∈ Set.Icc (0 : ℝ) 1,
        (-1 : ℝ) ^ N * x ^ N / (1 + x) ≤ x ^ N / (1 + x) := by
      intro x hx
      have hsplit : (-1 : ℝ) ^ N * x ^ N / (1 + x)
          = ((-1 : ℝ) ^ N) * (x ^ N / (1 + x)) := by ring
      rw [hsplit]
      have hA : 0 ≤ x ^ N / (1 + x) := hTpos x hx
      have hP := abs_le.mp (habsone N)
      have key : (1 - (-1 : ℝ) ^ N) * (x ^ N / (1 + x)) ≥ 0 :=
        mul_nonneg (by linarith) hA
      have hrew : (1 - (-1 : ℝ) ^ N) * (x ^ N / (1 + x))
          = x ^ N / (1 + x) - (-1 : ℝ) ^ N * (x ^ N / (1 + x)) := by ring
      linarith
    have hmono1 : ∫ x in (0 : ℝ)..1, (-1 : ℝ) ^ N * x ^ N / (1 + x) ∂volume
        ≤ ∫ x in (0 : ℝ)..1, x ^ N / (1 + x) ∂volume :=
      intervalIntegral.integral_mono_on zero_le_one hintT hintP hTle
    have hTle' : ∀ x ∈ Set.Icc (0 : ℝ) 1,
        -((-1 : ℝ) ^ N * x ^ N / (1 + x)) ≤ x ^ N / (1 + x) := by
      intro x hx
      have hx0 : 0 ≤ x := (Set.mem_Icc.mp hx).1
      have hx1 : (0 : ℝ) < 1 + x := by linarith
      have habs1 : |((-1 : ℝ) ^ N)| = 1 := by rw [abs_pow]; norm_num
      have habsx : |x ^ N| = x ^ N := abs_of_nonneg (pow_nonneg hx0 N)
      have habsd : |1 + x| = 1 + x := abs_of_nonneg (by linarith)
      have h3 : |((-1 : ℝ) ^ N * x ^ N / (1 + x))| = x ^ N / (1 + x) := by
        rw [abs_div, abs_mul, habs1, one_mul, habsx, habsd]
      exact (le_abs_self (-((-1 : ℝ) ^ N * x ^ N / (1 + x)))).trans_eq
        ((abs_neg ((-1 : ℝ) ^ N * x ^ N / (1 + x))).trans h3)
    have hmono2 : ∫ x in (0 : ℝ)..1, -((-1 : ℝ) ^ N * x ^ N / (1 + x)) ∂volume
        ≤ ∫ x in (0 : ℝ)..1, x ^ N / (1 + x) ∂volume :=
      intervalIntegral.integral_mono_on zero_le_one hintM hintP hTle'
    have hintneg : ∫ x in (0 : ℝ)..1, -((-1 : ℝ) ^ N * x ^ N / (1 + x)) ∂volume
        = -∫ x in (0 : ℝ)..1, (-1 : ℝ) ^ N * x ^ N / (1 + x) ∂volume :=
      intervalIntegral.integral_neg
    have hPX : ∀ x ∈ Set.Icc (0 : ℝ) 1, x ^ N / (1 + x) ≤ x ^ N := by
      intro x hx
      have hx0 : 0 ≤ x := hx.1
      have hx1 : (1 : ℝ) ≤ 1 + x := by linarith
      rw [div_le_iff₀ (by linarith : (0 : ℝ) < 1 + x)]
      simpa only [mul_one] using mul_le_mul_of_nonneg_left hx1 (pow_nonneg hx0 N)
    have hmono3 : ∫ x in (0 : ℝ)..1, x ^ N / (1 + x) ∂volume
        ≤ ∫ x in (0 : ℝ)..1, x ^ N ∂volume :=
      intervalIntegral.integral_mono_on zero_le_one hintP hintX hPX
    rw [integral_x_pow N] at hmono3
    -- combine: |S N - log 2| = |tail| ≤ tail-bound ≤ 1/(N+1)
    have htail : |∫ x in (0 : ℝ)..1, (-1 : ℝ) ^ N * x ^ N / (1 + x) ∂volume|
        ≤ 1 / (((N + 1 : ℕ) : ℝ)) := by
      rw [abs_le]
      constructor
      · have h2 := hmono2.trans hmono3
        rw [hintneg] at h2
        linarith
      · exact hmono1.trans hmono3
    have hST : ∑ n ∈ Finset.range N, (-1 : ℝ) ^ n / (((n + 1 : ℕ) : ℝ)) - Real.log 2
        = -(∫ x in (0 : ℝ)..1, (-1 : ℝ) ^ N * x ^ N / (1 + x) ∂volume) := by
      rw [hlog]
      ring
    rw [hST, abs_neg]
    exact htail
  -- the metric tendsto from the explicit rate
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨M, hM⟩ := exists_nat_gt (1 / ε)
  refine ⟨M, fun N hN => ?_⟩
  have h1 : |∑ n ∈ Finset.range N, (-1 : ℝ) ^ n / (((n + 1 : ℕ) : ℝ)) - Real.log 2|
      ≤ 1 / (((N + 1 : ℕ) : ℝ)) := hkey N
  have hM' : (1 / ε : ℝ) < (M : ℝ) := by exact_mod_cast hM
  have hNM : (M : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hMN : (1 / ε : ℝ) < (N : ℝ) := by linarith
  have hNε : (1 : ℝ) < (N : ℝ) * ε := (div_lt_iff₀ hε).mp hMN
  have h2 : (1 : ℝ) / (((N + 1 : ℕ) : ℝ)) < ε := by
    have hNp : (0 : ℝ) < ((N + 1 : ℕ) : ℝ) := by exact_mod_cast (Nat.succ_pos N)
    rw [div_lt_iff₀ hNp]
    have hcast : (((N + 1 : ℕ) : ℝ)) = (N : ℝ) + 1 := by exact_mod_cast rfl
    rw [hcast, mul_add]
    nlinarith [hε, hNε]
  rw [Real.dist_eq]
  exact h1.trans_lt h2

/-! ## W2-D: the Lambert integrals `int x e^{-pi j x}/(1+e^{-pi j x}) = 1/(12 j^2)` -/

/-- The integrand family `x e^{-pi j x}/(1+e^{-pi j x})` is integrable on
`(0, inf)`: dominated by `x e^{-pi j x}` (the denominator exceeds 1),
itself dominated by `x e^{-x}` (since `pi j >= pi >= 1`), the
GaussianIntegral receipt at `p = s = 1`. -/
private theorem integrable_exp_div_family {j : ℕ} (hj : 0 < j) :
    IntegrableOn (fun x => x * Real.exp (-Real.pi * ((j : ℕ) : ℝ) * x)
        / (1 + Real.exp (-Real.pi * ((j : ℕ) : ℝ) * x))) (Ioi (0 : ℝ)) volume := by
  have hpione : (1 : ℝ) ≤ Real.pi := by
    have h := pi_gt_three
    linarith
  have hb : (0 : ℝ) < Real.pi * ((j : ℕ) : ℝ) := by positivity
  -- receipt: t * exp (-t) integrable on Ioi 0
  have hrec := integrableOn_rpow_mul_exp_neg_rpow (s := (1 : ℝ)) (p := (1 : ℝ))
    (by norm_num) (by norm_num)
  have hrec' : IntegrableOn (fun t : ℝ => t * Real.exp (-t)) (Ioi (0 : ℝ)) volume := by
    refine hrec.congr_fun (fun x hx => ?_) measurableSet_Ioi
    simp only [Real.rpow_one]
  have hdom0 : MeasureTheory.Integrable
      (fun t => t * Real.exp (-t)) (MeasureTheory.volume.restrict (Ioi (0 : ℝ))) :=
    hrec'
  have hdom : ∀ x ∈ Ioi (0 : ℝ),
      ‖x * Real.exp (-Real.pi * ((j : ℕ) : ℝ) * x)
        / (1 + Real.exp (-Real.pi * ((j : ℕ) : ℝ) * x))‖
        ≤ ‖x * Real.exp (-x)‖ := by
    intro x hx
    have hx0 : 0 < x := Set.mem_Ioi.mp hx
    have hnn : 0 ≤ x * Real.exp (-Real.pi * ((j : ℕ) : ℝ) * x)
        / (1 + Real.exp (-Real.pi * ((j : ℕ) : ℝ) * x)) := by
      apply div_nonneg
      · positivity
      · have : (0 : ℝ) < 1 + Real.exp (-Real.pi * ((j : ℕ) : ℝ) * x) := by positivity
        linarith
    rw [Real.norm_eq_abs, abs_of_nonneg hnn, Real.norm_eq_abs,
      abs_of_nonneg (by positivity : (0:ℝ) ≤ x * Real.exp (-x))]
    have hd1 : (1 : ℝ) ≤ 1 + Real.exp (-Real.pi * ((j : ℕ) : ℝ) * x) := by
      have := Real.exp_pos (-Real.pi * ((j : ℕ) : ℝ) * x)
      linarith
    have hd2 : x * Real.exp (-Real.pi * ((j : ℕ) : ℝ) * x)
        / (1 + Real.exp (-Real.pi * ((j : ℕ) : ℝ) * x))
        ≤ x * Real.exp (-Real.pi * ((j : ℕ) : ℝ) * x) := by
      rw [div_le_iff₀ (by positivity : (0:ℝ) < 1 + Real.exp (-Real.pi * ((j:ℕ):ℝ) * x))]
      nlinarith [mul_nonneg hx0.le (by positivity : (0:ℝ) ≤ Real.exp (-Real.pi * ((j:ℕ):ℝ) * x))]
    have hd3 : Real.exp (-Real.pi * ((j : ℕ) : ℝ) * x) ≤ Real.exp (-x) := by
      refine Real.exp_le_exp.mpr ?_
      have hc : (1 : ℝ) ≤ ((j : ℕ) : ℝ) := by exact_mod_cast hj
      have : (-Real.pi) * ((j : ℕ) : ℝ) * x ≤ (-1 : ℝ) * x := by
        have hpj : (1 : ℝ) ≤ Real.pi * ((j : ℕ) : ℝ) := by nlinarith [hpione, hc]
        nlinarith [hpj, hx0]
      linarith [this]
    have hd4 : x * Real.exp (-Real.pi * ((j : ℕ) : ℝ) * x) ≤ x * Real.exp (-x) :=
      mul_le_mul_of_nonneg_left hd3 hx0.le
    exact hd2.trans hd4
  have hmeas : AEStronglyMeasurable
      (fun x => x * Real.exp (-Real.pi * ((j : ℕ) : ℝ) * x)
        / (1 + Real.exp (-Real.pi * ((j : ℕ) : ℝ) * x)))
      (MeasureTheory.volume.restrict (Ioi (0 : ℝ))) :=
    (by fun_prop : Measurable
      (fun x => x * Real.exp (-Real.pi * ((j : ℕ) : ℝ) * x)
        / (1 + Real.exp (-Real.pi * ((j : ℕ) : ℝ) * x)))).aestronglyMeasurable
  exact MeasureTheory.Integrable.mono hdom0 hmeas
    (Filter.mem_of_superset (self_mem_ae_restrict measurableSet_Ioi) hdom)


/-- Pointwise geometric expansion of the Lambert kernel:
`x e^{-pi j x}/(1+e^{-pi j x}) = sum' (-1)^k x e^{-pi (k+1) j x}`,
a geometric series in `r = -e^{-pi j x}`. -/
private theorem lamGeo_hasSum {j : ℕ} (hj : 0 < j) {x : ℝ} (hx : 0 < x) :
    HasSum (fun k : ℕ => (-1 : ℝ) ^ k
        * (x * Real.exp (-Real.pi * ((k + 1 : ℕ) : ℝ) * ((j : ℕ) : ℝ) * x)))
      (x * Real.exp (-Real.pi * ((j : ℕ) : ℝ) * x)
        / (1 + Real.exp (-Real.pi * ((j : ℕ) : ℝ) * x))) := by
  have hπ : (0 : ℝ) < Real.pi := Real.pi_pos
  have hj' : (0 : ℝ) < ((j : ℕ) : ℝ) := by exact_mod_cast hj
  have hcx : (0 : ℝ) < Real.pi * ((j : ℕ) : ℝ) * x :=
    mul_pos (mul_pos hπ hj') hx
  have hneg : (-Real.pi * ((j : ℕ) : ℝ) * x) < 0 := by linarith
  have hexplt : Real.exp (-Real.pi * ((j : ℕ) : ℝ) * x) < 1 := by
    have h : Real.exp (-Real.pi * ((j : ℕ) : ℝ) * x) < Real.exp 0 :=
      Real.exp_lt_exp.mpr (by linarith)
    simpa using h
  have habs : |((-1 : ℝ) * Real.exp (-Real.pi * ((j : ℕ) : ℝ) * x))| < 1 := by
    rw [abs_mul, abs_neg, abs_one, abs_of_pos (Real.exp_pos _), one_mul]
    exact hexplt
  have hgeo := hasSum_geometric_of_abs_lt_one habs
  have hfam : ∀ k : ℕ, (-1 : ℝ) ^ k
      * (x * Real.exp (-Real.pi * ((k + 1 : ℕ) : ℝ) * ((j : ℕ) : ℝ) * x))
      = (x * Real.exp (-Real.pi * ((j : ℕ) : ℝ) * x))
        * ((-1 : ℝ) * Real.exp (-Real.pi * ((j : ℕ) : ℝ) * x)) ^ k := by
    intro k
    have h2 : Real.exp (-Real.pi * ((k + 1 : ℕ) : ℝ) * ((j : ℕ) : ℝ) * x)
        = (Real.exp (-Real.pi * ((j : ℕ) : ℝ) * x)) ^ (k + 1) := by
      have he : (-Real.pi * ((k + 1 : ℕ) : ℝ) * ((j : ℕ) : ℝ) * x)
          = ((k + 1 : ℕ) : ℝ) * (-Real.pi * ((j : ℕ) : ℝ) * x) := by ring
      rw [he, exp_pow_self]
    rw [h2, pow_succ, mul_pow]
    ring
  have hs0 := HasSum.congr_fun (HasSum.const_smul
    (x * Real.exp (-Real.pi * ((j : ℕ) : ℝ) * x)) hgeo) hfam
  have hv : (x * Real.exp (-Real.pi * ((j : ℕ) : ℝ) * x))
      • (1 - ((-1 : ℝ) * Real.exp (-Real.pi * ((j : ℕ) : ℝ) * x)))⁻¹
      = x * Real.exp (-Real.pi * ((j : ℕ) : ℝ) * x)
        / (1 + Real.exp (-Real.pi * ((j : ℕ) : ℝ) * x)) := by
    have h1 : (1 : ℝ) - ((-1 : ℝ) * Real.exp (-Real.pi * ((j : ℕ) : ℝ) * x))
        = 1 + Real.exp (-Real.pi * ((j : ℕ) : ℝ) * x) := by ring
    rw [h1, smul_eq_mul, div_eq_mul_inv]
  rw [hv] at hs0
  exact hs0

/-- `t e^{-t} <= e^{-t/2}` for `t >= 0`, from the house `u <= e^{u/2}`. -/
private theorem le_exp_neg_half_mul {t : ℝ} (ht : 0 ≤ t) :
    t * Real.exp (-t) ≤ Real.exp (-(t / 2)) := by
  have h := le_exp_half ht
  have he : (0 : ℝ) < Real.exp (-t) := Real.exp_pos _
  have hstep : t * Real.exp (-t) ≤ Real.exp (t / 2) * Real.exp (-t) :=
    mul_le_mul_of_nonneg_right h he.le
  have heq : Real.exp (t / 2) * Real.exp (-t) = Real.exp (-(t / 2)) := by
    rw [← Real.exp_add]
    ring
  exact hstep.trans_eq heq

/-- `x e^{-b x}` is integrable on `(0, inf)`: dominated by
`(1/b) e^{-b x / 2}`, itself integrable by the `exp_neg_integrableOn_Ioi`
receipt. -/
private theorem integrable_x_exp {b : ℝ} (hb : 0 < b) :
    IntegrableOn (fun x => x * Real.exp (-b * x)) (Ioi (0 : ℝ)) volume := by
  have hb2 : 0 < b / 2 := by linarith
  have hg0 := exp_neg_integrableOn_Ioi (0 : ℝ) hb2
  have hg : MeasureTheory.Integrable (fun x => (1 / b) * Real.exp (-(b / 2) * x))
      (MeasureTheory.volume.restrict (Ioi (0 : ℝ))) :=
    MeasureTheory.Integrable.const_mul hg0 (1 / b)
  have hmeas : AEStronglyMeasurable (fun x => x * Real.exp (-b * x))
      (MeasureTheory.volume.restrict (Ioi (0 : ℝ))) :=
    (by fun_prop : Measurable (fun x => x * Real.exp (-b * x))).aestronglyMeasurable
  have hdom : ∀ x ∈ Ioi (0 : ℝ),
      ‖x * Real.exp (-b * x)‖ ≤ ‖(1 / b) * Real.exp (-(b / 2) * x)‖ := by
    intro x hx
    have hx0 : 0 < x := Set.mem_Ioi.mp hx
    have hnn : 0 ≤ x * Real.exp (-b * x) := by positivity
    have hnn2 : 0 ≤ (1 / b) * Real.exp (-(b / 2) * x) := by positivity
    rw [Real.norm_eq_abs, abs_of_nonneg hnn, Real.norm_eq_abs, abs_of_nonneg hnn2]
    have key : b * x * Real.exp (-(b * x)) ≤ Real.exp (-((b * x) / 2)) :=
      le_exp_neg_half_mul (mul_nonneg hb.le hx0.le)
    have hs : x * Real.exp (-b * x) = (1 / b) * (b * x * Real.exp (-(b * x))) := by
      have hE : Real.exp (-(b * x)) = Real.exp (-b * x) := by
        congr 1
        ring
      rw [hE]
      rw [show (1 / b) * (b * x * Real.exp (-b * x))
          = (1 / b) * b * (x * Real.exp (-b * x)) from by ring,
        div_mul_cancel₀ 1 hb.ne', one_mul]
    have he : Real.exp (-((b * x) / 2)) = Real.exp (-(b / 2) * x) := by
      congr 1
      ring
    rw [he] at key
    rw [hs]
    exact mul_le_mul_of_nonneg_left key (by positivity)
  exact MeasureTheory.Integrable.mono hg hmeas
    (Filter.mem_of_superset (self_mem_ae_restrict measurableSet_Ioi) hdom)

/-- Exponent conversion for the Lambert family: `e^{-pi (n+1) j x}` is the
`(n+1)`-st power of `e^{-pi j x}`. -/
private theorem lamGeo_exp_pow {j : ℕ} (n : ℕ) (x : ℝ) :
    Real.exp (-Real.pi * ((n + 1 : ℕ) : ℝ) * ((j : ℕ) : ℝ) * x)
      = Real.exp (-Real.pi * ((j : ℕ) : ℝ) * x) ^ (n + 1) := by
  have he : (-Real.pi * ((n + 1 : ℕ) : ℝ) * ((j : ℕ) : ℝ) * x)
      = ((n + 1 : ℕ) : ℝ) * (-Real.pi * ((j : ℕ) : ℝ) * x) := by ring
  rw [he, exp_pow_self]

/-- The Lambert family equals the scaled geometric family. -/
private theorem lamGeoFam_eq {j : ℕ} (a x : ℝ) (n : ℕ) :
    a * Real.exp (-Real.pi * ((n + 1 : ℕ) : ℝ) * ((j : ℕ) : ℝ) * a)
      = (a * Real.exp (-Real.pi * ((j : ℕ) : ℝ) * a))
        * Real.exp (-Real.pi * ((j : ℕ) : ℝ) * a) ^ n := by
  rw [lamGeo_exp_pow n a, pow_succ]
  ring

/-- `|e^{-pi j a}| < 1` for `a > 0`, `j > 0`. -/
private theorem abs_exp_neg_lt_one {j : ℕ} (hj : 0 < j) {a : ℝ} (ha : 0 < a) :
    |Real.exp (-Real.pi * ((j : ℕ) : ℝ) * a)| < 1 := by
  rw [abs_of_pos (Real.exp_pos _)]
  have h1 : (0 : ℝ) < Real.pi * ((j : ℕ) : ℝ) * a :=
    mul_pos (mul_pos Real.pi_pos (by exact_mod_cast hj)) ha
  have h0 : (-Real.pi * ((j : ℕ) : ℝ) * a) < 0 := by linarith
  have h2 := Real.exp_lt_exp.mpr h0
  simpa using h2

/-- The summed bound is integrable: `G x = x e^{-pi j x}/(1 - e^{-pi j x})`
is integrable on `(0, inf)` by the two-region split at `1/c`, `c = pi j`. -/
private theorem integrable_lamBound {j : ℕ} (hj : 0 < j) :
    IntegrableOn (fun a => a * Real.exp (-Real.pi * ((j : ℕ) : ℝ) * a)
      / (1 - Real.exp (-Real.pi * ((j : ℕ) : ℝ) * a))) (Ioi (0 : ℝ)) volume := by
  have hj' : (0 : ℝ) < ((j : ℕ) : ℝ) := by exact_mod_cast hj
  have hc : (0 : ℝ) < Real.pi * ((j : ℕ) : ℝ) := mul_pos Real.pi_pos hj'
  have hc1 : (1 : ℝ) ≤ Real.pi * ((j : ℕ) : ℝ) := by
    have hπ1 : (1 : ℝ) ≤ Real.pi := by
      have h := pi_gt_three
      linarith
    have hj1 : (1 : ℝ) ≤ ((j : ℕ) : ℝ) := by exact_mod_cast hj
    simpa only [one_mul] using mul_le_mul hπ1 hj1 zero_le_one Real.pi_pos.le
  have hinvc : (0 : ℝ) < 1 / (Real.pi * ((j : ℕ) : ℝ)) := by positivity
  have hmeas : ∀ s : Set ℝ, MeasurableSet s → AEStronglyMeasurable
      (fun a => a * Real.exp (-Real.pi * ((j : ℕ) : ℝ) * a)
        / (1 - Real.exp (-Real.pi * ((j : ℕ) : ℝ) * a)))
      (MeasureTheory.volume.restrict s) := by
    intro s _
    exact (by fun_prop : Measurable (fun a => a * Real.exp (-Real.pi * ((j : ℕ) : ℝ) * a)
        / (1 - Real.exp (-Real.pi * ((j : ℕ) : ℝ) * a)))).aestronglyMeasurable
  -- region 1: Ioc 0 (1/c), bounded by 2/c
  have hR1 : IntegrableOn (fun a => a * Real.exp (-Real.pi * ((j : ℕ) : ℝ) * a)
      / (1 - Real.exp (-Real.pi * ((j : ℕ) : ℝ) * a)))
      (Set.Ioc (0 : ℝ) (1 / (Real.pi * ((j : ℕ) : ℝ)))) volume := by
    have hvol : volume (Set.Ioc (0 : ℝ) (1 / (Real.pi * ((j : ℕ) : ℝ)))) < ⊤ :=
      measure_Ioc_lt_top
    have hmeas1 : AEStronglyMeasurable (fun a => a * Real.exp (-Real.pi * ((j : ℕ) : ℝ) * a)
      / (1 - Real.exp (-Real.pi * ((j : ℕ) : ℝ) * a)))
      (MeasureTheory.volume.restrict
        (Set.Ioc (0 : ℝ) (1 / (Real.pi * ((j : ℕ) : ℝ))))) :=
      hmeas _ measurableSet_Ioc
    have hbdd : ∀ a ∈ Set.Ioc (0 : ℝ) (1 / (Real.pi * ((j : ℕ) : ℝ))),
        ‖a * Real.exp (-Real.pi * ((j : ℕ) : ℝ) * a)
          / (1 - Real.exp (-Real.pi * ((j : ℕ) : ℝ) * a))‖
        ≤ 2 / (Real.pi * ((j : ℕ) : ℝ)) := by
      intro a ha
      have ha0 : 0 < a := (Set.mem_Ioc.mp ha).1
      have hca : 0 < Real.pi * ((j : ℕ) : ℝ) * a := mul_pos hc ha0
      have hq : 0 < Real.exp (-Real.pi * ((j : ℕ) : ℝ) * a) := Real.exp_pos _
      have hq1 : Real.exp (-Real.pi * ((j : ℕ) : ℝ) * a) < 1 :=
        (abs_lt.mp (abs_exp_neg_lt_one hj ha0)).2
      -- shape bridge: the house lemmas output `exp (-(pi j a))`; the block
      -- spells `exp (-pi j a)`. Unifying the two makes whnf unfold `exp`
      -- into its Cauchy construction and spiral, so bridge once, by ring.
      have hEshape : Real.exp (-(Real.pi * ((j : ℕ) : ℝ) * a))
          = Real.exp (-Real.pi * ((j : ℕ) : ℝ) * a) := by
        congr 1
        ring
      have hpos : 0 < 1 - Real.exp (-Real.pi * ((j : ℕ) : ℝ) * a) := by
        rw [← hEshape]
        exact one_sub_exp_pos hca
      have hnn : 0 ≤ a * Real.exp (-Real.pi * ((j : ℕ) : ℝ) * a)
          / (1 - Real.exp (-Real.pi * ((j : ℕ) : ℝ) * a)) :=
        div_nonneg (mul_nonneg ha0.le hq.le) hpos.le
      rw [Real.norm_eq_abs, abs_of_nonneg hnn]
      have hsplit : a * Real.exp (-Real.pi * ((j : ℕ) : ℝ) * a)
          / (1 - Real.exp (-Real.pi * ((j : ℕ) : ℝ) * a))
          = (a * Real.exp (-Real.pi * ((j : ℕ) : ℝ) * a))
            * (1 / (1 - Real.exp (-Real.pi * ((j : ℕ) : ℝ) * a))) := by
        rw [div_eq_mul_inv, inv_eq_one_div]
      rw [hsplit]
      have hb1 : 1 / (1 - Real.exp (-Real.pi * ((j : ℕ) : ℝ) * a))
          ≤ (1 + Real.pi * ((j : ℕ) : ℝ) * a)
            / (Real.pi * ((j : ℕ) : ℝ) * a) := by
        rw [← hEshape]
        exact inv_one_sub_exp_neg_le hca
      have hca1 : Real.pi * ((j : ℕ) : ℝ) * a ≤ 1 := by
        have h1 := (Set.mem_Ioc.mp ha).2
        rw [le_div_iff₀ hc] at h1
        nlinarith [h1]
      calc (a * Real.exp (-Real.pi * ((j : ℕ) : ℝ) * a))
            * (1 / (1 - Real.exp (-Real.pi * ((j : ℕ) : ℝ) * a)))
          ≤ (a * Real.exp (-Real.pi * ((j : ℕ) : ℝ) * a))
            * ((1 + Real.pi * ((j : ℕ) : ℝ) * a)
              / (Real.pi * ((j : ℕ) : ℝ) * a)) :=
            mul_le_mul_of_nonneg_left hb1 (mul_nonneg ha0.le hq.le)
        _ = Real.exp (-Real.pi * ((j : ℕ) : ℝ) * a) * (1 + Real.pi * ((j : ℕ) : ℝ) * a)
              / (Real.pi * ((j : ℕ) : ℝ)) := by
            field_simp
        _ ≤ (1 + Real.pi * ((j : ℕ) : ℝ) * a) / (Real.pi * ((j : ℕ) : ℝ)) := by
            have hqle : Real.exp (-Real.pi * ((j : ℕ) : ℝ) * a) ≤ 1 := hq1.le
            have hnn2 : 0 ≤ 1 + Real.pi * ((j : ℕ) : ℝ) * a := by positivity
            have hinner : Real.exp (-Real.pi * ((j : ℕ) : ℝ) * a)
                * (1 + Real.pi * ((j : ℕ) : ℝ) * a)
                ≤ 1 + Real.pi * ((j : ℕ) : ℝ) * a := by
              simpa only [one_mul] using mul_le_mul_of_nonneg_right hqle hnn2
            rw [div_le_div_iff₀ hc hc]
            exact mul_le_mul_of_nonneg_right hinner hc.le
        _ ≤ 2 / (Real.pi * ((j : ℕ) : ℝ)) := by
            rw [div_le_div_iff₀ hc hc]
            nlinarith [hca1]
    exact IntegrableOn.of_bound hvol hmeas1 (2 / (Real.pi * ((j : ℕ) : ℝ)))
      (Filter.mem_of_superset (self_mem_ae_restrict measurableSet_Ioc) hbdd)
  -- region 2: Ioi (1/c), dominated by 2 * (x e^{-x})
  have hR2 : IntegrableOn (fun a => a * Real.exp (-Real.pi * ((j : ℕ) : ℝ) * a)
      / (1 - Real.exp (-Real.pi * ((j : ℕ) : ℝ) * a)))
      (Set.Ioi (1 / (Real.pi * ((j : ℕ) : ℝ)))) volume := by
    have hrec := integrableOn_rpow_mul_exp_neg_rpow (s := (1 : ℝ)) (p := (1 : ℝ))
      (by norm_num) (by norm_num)
    have hG1 : IntegrableOn (fun x => x * Real.exp (-x)) (Ioi (0 : ℝ)) volume := by
      refine hrec.congr_fun (fun x hx => ?_) measurableSet_Ioi
      simp only [Real.rpow_one]
    have hG2 : IntegrableOn (fun x => 2 * (x * Real.exp (-x))) (Ioi (0 : ℝ)) volume :=
      MeasureTheory.Integrable.const_mul hG1 2
    have hg2 : MeasureTheory.Integrable (fun x => 2 * (x * Real.exp (-x)))
        (MeasureTheory.volume.restrict
          (Set.Ioi (1 / (Real.pi * ((j : ℕ) : ℝ))))) :=
      hG2.mono_set (Ioi_subset_Ioi hinvc.le)
    have hmeas2 : AEStronglyMeasurable (fun a => a * Real.exp (-Real.pi * ((j : ℕ) : ℝ) * a)
        / (1 - Real.exp (-Real.pi * ((j : ℕ) : ℝ) * a)))
        (MeasureTheory.volume.restrict
          (Set.Ioi (1 / (Real.pi * ((j : ℕ) : ℝ))))) :=
      hmeas _ measurableSet_Ioi
    have hbdd2 : ∀ a ∈ Set.Ioi (1 / (Real.pi * ((j : ℕ) : ℝ))),
        ‖a * Real.exp (-Real.pi * ((j : ℕ) : ℝ) * a)
          / (1 - Real.exp (-Real.pi * ((j : ℕ) : ℝ) * a))‖
        ≤ ‖2 * (a * Real.exp (-a))‖ := by
      intro a ha
      have h1 : (1 : ℝ) / (Real.pi * ((j : ℕ) : ℝ)) < a := Set.mem_Ioi.mp ha
      have ha0 : 0 < a := by linarith
      have hca : 1 ≤ Real.pi * ((j : ℕ) : ℝ) * a := by
        rw [div_lt_iff₀ hc] at h1
        nlinarith [h1]
      have hq : 0 < Real.exp (-Real.pi * ((j : ℕ) : ℝ) * a) := Real.exp_pos _
      have hEshape : Real.exp (-(Real.pi * ((j : ℕ) : ℝ) * a))
          = Real.exp (-Real.pi * ((j : ℕ) : ℝ) * a) := by
        congr 1
        ring
      have hpos : 0 < 1 - Real.exp (-Real.pi * ((j : ℕ) : ℝ) * a) := by
        rw [← hEshape]
        exact one_sub_exp_pos (by linarith : (0 : ℝ) < Real.pi * ((j : ℕ) : ℝ) * a)
      have hnn : 0 ≤ a * Real.exp (-Real.pi * ((j : ℕ) : ℝ) * a)
          / (1 - Real.exp (-Real.pi * ((j : ℕ) : ℝ) * a)) :=
        div_nonneg (mul_nonneg ha0.le hq.le) hpos.le
      have hnn2 : 0 ≤ 2 * (a * Real.exp (-a)) := by positivity
      rw [Real.norm_eq_abs, abs_of_nonneg hnn, Real.norm_eq_abs, abs_of_nonneg hnn2]
      have hb2 : 1 / (1 - Real.exp (-Real.pi * ((j : ℕ) : ℝ) * a)) ≤ 2 := by
        rw [← hEshape]
        exact inv_one_sub_exp_neg_le' hca
      have hqle : Real.exp (-Real.pi * ((j : ℕ) : ℝ) * a) ≤ Real.exp (-a) := by
        refine Real.exp_le_exp.mpr ?_
        have hkey : -Real.pi * ((j : ℕ) : ℝ) * a ≤ -a := by
          have hc1' : (1 : ℝ) ≤ Real.pi * ((j : ℕ) : ℝ) := hc1
          nlinarith [ha0]
        linarith
      have hsplit : a * Real.exp (-Real.pi * ((j : ℕ) : ℝ) * a)
          / (1 - Real.exp (-Real.pi * ((j : ℕ) : ℝ) * a))
          = (a * Real.exp (-Real.pi * ((j : ℕ) : ℝ) * a))
            * (1 / (1 - Real.exp (-Real.pi * ((j : ℕ) : ℝ) * a))) := by
        rw [div_eq_mul_inv, inv_eq_one_div]
      rw [hsplit]
      have hstep1 := mul_le_mul_of_nonneg_left hb2 (mul_nonneg ha0.le hq.le)
      have hstep2 : a * Real.exp (-Real.pi * ((j : ℕ) : ℝ) * a) ≤ a * Real.exp (-a) :=
        mul_le_mul_of_nonneg_left hqle ha0.le
      calc (a * Real.exp (-Real.pi * ((j : ℕ) : ℝ) * a))
            * (1 / (1 - Real.exp (-Real.pi * ((j : ℕ) : ℝ) * a)))
          ≤ (a * Real.exp (-Real.pi * ((j : ℕ) : ℝ) * a)) * 2 := hstep1
        _ = 2 * (a * Real.exp (-Real.pi * ((j : ℕ) : ℝ) * a)) := by ring
        _ ≤ 2 * (a * Real.exp (-a)) := mul_le_mul_of_nonneg_left hstep2 (by norm_num)
    exact MeasureTheory.Integrable.mono hg2 hmeas2
      (Filter.mem_of_superset (self_mem_ae_restrict measurableSet_Ioi) hbdd2)
  have hun := (integrableOn_union).mpr ⟨hR1, hR2⟩
  rw [Set.Ioc_union_Ioi_eq_Ioi (by positivity : (0 : ℝ) ≤ 1 / (Real.pi * ((j : ℕ) : ℝ)))] at hun
  exact hun

/-- The summed DC bound `sum'_n` (indicatored `x e^{-pi (n+1) j x}`) is
integrable: pointwise the indicatored `G`, which is integrable. -/
private theorem integrable_tsum_bound {j : ℕ} (hj : 0 < j) :
    Integrable (fun a => ∑' n, (Set.Ioi (0 : ℝ)).indicator
      (fun x => x * Real.exp (-Real.pi * ((n + 1 : ℕ) : ℝ) * ((j : ℕ) : ℝ) * x)) a)
      volume := by
  have hGint := integrable_lamBound hj
  have hind := (integrable_indicator_iff measurableSet_Ioi).mpr hGint
  have hptw : ∀ a : ℝ,
      (Set.Ioi (0 : ℝ)).indicator (fun x => x * Real.exp (-Real.pi * ((j : ℕ) : ℝ) * x)
        / (1 - Real.exp (-Real.pi * ((j : ℕ) : ℝ) * x))) a
      = ∑' n, (Set.Ioi (0 : ℝ)).indicator
        (fun x => x * Real.exp (-Real.pi * ((n + 1 : ℕ) : ℝ) * ((j : ℕ) : ℝ) * x)) a := by
    intro a
    by_cases ha : a ∈ Set.Ioi (0 : ℝ)
    · simp only [Set.indicator_of_mem ha]
      have hq : |Real.exp (-Real.pi * ((j : ℕ) : ℝ) * a)| < 1 :=
        abs_exp_neg_lt_one hj (Set.mem_Ioi.mp ha)
      have hgeo := hasSum_geometric_of_abs_lt_one hq
      have hfam : ∀ n : ℕ,
          a * Real.exp (-Real.pi * ((n + 1 : ℕ) : ℝ) * ((j : ℕ) : ℝ) * a)
            = (a * Real.exp (-Real.pi * ((j : ℕ) : ℝ) * a))
              • Real.exp (-Real.pi * ((j : ℕ) : ℝ) * a) ^ n :=
        fun n => lamGeoFam_eq a a n
      have hs := HasSum.congr_fun (HasSum.const_smul
        (a * Real.exp (-Real.pi * ((j : ℕ) : ℝ) * a)) hgeo) hfam
      have hts : ∑' n : ℕ,
          a * Real.exp (-Real.pi * ((n + 1 : ℕ) : ℝ) * ((j : ℕ) : ℝ) * a)
          = (a * Real.exp (-Real.pi * ((j : ℕ) : ℝ) * a))
            • (1 - Real.exp (-Real.pi * ((j : ℕ) : ℝ) * a))⁻¹ := hs.tsum_eq
      rw [hts, smul_eq_mul, inv_eq_one_div, mul_one_div]
    · simp only [Set.indicator_of_notMem ha]
      simp
  exact hind.congr (Filter.Eventually.of_forall hptw)

/-- The dominated-convergence swap for the Lambert integral: the indicatored
family `HasSum`s onto the indicatored value. -/
private theorem lamDC_hasSum {j : ℕ} (hj : 0 < j) :
    HasSum (fun k : ℕ => ∫ a : ℝ, (Set.Ioi (0 : ℝ)).indicator
      (fun x => (-1 : ℝ) ^ k
        * (x * Real.exp (-Real.pi * ((k + 1 : ℕ) : ℝ) * ((j : ℕ) : ℝ) * x))) a ∂volume)
      (∫ a : ℝ, (Set.Ioi (0 : ℝ)).indicator
      (fun x => x * Real.exp (-Real.pi * ((j : ℕ) : ℝ) * x)
        / (1 + Real.exp (-Real.pi * ((j : ℕ) : ℝ) * x))) a ∂volume) := by
  have hFmeas : ∀ k : ℕ, AEStronglyMeasurable ((Set.Ioi (0 : ℝ)).indicator
      (fun x => (-1 : ℝ) ^ k
        * (x * Real.exp (-Real.pi * ((k + 1 : ℕ) : ℝ) * ((j : ℕ) : ℝ) * x))))
      volume := by
    intro k
    exact (Measurable.indicator (by fun_prop) measurableSet_Ioi).aestronglyMeasurable
  have hbound : ∀ k : ℕ, ∀ᵐ a ∂volume,
      ‖((Set.Ioi (0 : ℝ)).indicator
      (fun x => (-1 : ℝ) ^ k
        * (x * Real.exp (-Real.pi * ((k + 1 : ℕ) : ℝ) * ((j : ℕ) : ℝ) * x)))) a‖
      ≤ ((Set.Ioi (0 : ℝ)).indicator
      (fun x => x * Real.exp (-Real.pi * ((k + 1 : ℕ) : ℝ) * ((j : ℕ) : ℝ) * x))) a := by
    intro k
    refine Filter.Eventually.of_forall (fun a => ?_)
    have habs1 : |((-1 : ℝ) ^ k)| = 1 := by
      rw [abs_pow, abs_neg, abs_one, one_pow]
    by_cases ha : a ∈ Set.Ioi (0 : ℝ)
    · have ha0 : 0 < a := Set.mem_Ioi.mp ha
      rw [Set.indicator_of_mem ha, Set.indicator_of_mem ha, Real.norm_eq_abs, abs_mul,
        habs1, one_mul, abs_of_nonneg
        (mul_nonneg ha0.le (Real.exp_nonneg
          (-Real.pi * ((k + 1 : ℕ) : ℝ) * ((j : ℕ) : ℝ) * a)))]
    · rw [Set.indicator_of_notMem ha, Set.indicator_of_notMem ha]
      simp
  have hsumm : ∀ᵐ a ∂volume, Summable fun n =>
      ((Set.Ioi (0 : ℝ)).indicator
      (fun x => x * Real.exp (-Real.pi * ((n + 1 : ℕ) : ℝ) * ((j : ℕ) : ℝ) * x))) a := by
    refine Filter.Eventually.of_forall (fun a => ?_)
    by_cases ha : a ∈ Set.Ioi (0 : ℝ)
    · simp only [Set.indicator_of_mem ha]
      have hq : |Real.exp (-Real.pi * ((j : ℕ) : ℝ) * a)| < 1 :=
        abs_exp_neg_lt_one hj (Set.mem_Ioi.mp ha)
      have hgeo := hasSum_geometric_of_abs_lt_one hq
      have hfam : ∀ n : ℕ,
          a * Real.exp (-Real.pi * ((n + 1 : ℕ) : ℝ) * ((j : ℕ) : ℝ) * a)
            = (a * Real.exp (-Real.pi * ((j : ℕ) : ℝ) * a))
              • Real.exp (-Real.pi * ((j : ℕ) : ℝ) * a) ^ n :=
        fun n => lamGeoFam_eq a a n
      exact HasSum.summable (HasSum.congr_fun (HasSum.const_smul
        (a * Real.exp (-Real.pi * ((j : ℕ) : ℝ) * a)) hgeo) hfam)
    · simp only [Set.indicator_of_notMem ha]
      exact summable_zero
  have hInt := integrable_tsum_bound hj
  have hlim : ∀ᵐ a ∂volume, HasSum (fun k : ℕ =>
      ((Set.Ioi (0 : ℝ)).indicator
      (fun x => (-1 : ℝ) ^ k
        * (x * Real.exp (-Real.pi * ((k + 1 : ℕ) : ℝ) * ((j : ℕ) : ℝ) * x)))) a)
      (((Set.Ioi (0 : ℝ)).indicator
      (fun x => x * Real.exp (-Real.pi * ((j : ℕ) : ℝ) * x)
        / (1 + Real.exp (-Real.pi * ((j : ℕ) : ℝ) * x)))) a) := by
    refine Filter.Eventually.of_forall (fun a => ?_)
    by_cases ha : a ∈ Set.Ioi (0 : ℝ)
    · simp only [Set.indicator_of_mem ha]
      exact lamGeo_hasSum hj (Set.mem_Ioi.mp ha)
    · simp only [Set.indicator_of_notMem ha]
      exact hasSum_zero
  exact hasSum_integral_of_dominated_convergence
    (bound := fun k => (Set.Ioi (0 : ℝ)).indicator
      (fun x => x * Real.exp (-Real.pi * ((k + 1 : ℕ) : ℝ) * ((j : ℕ) : ℝ) * x)))
    hFmeas hbound hsumm hInt hlim

/-- Each indicatored Lambert piece integrates exactly. -/
private theorem lamFam_integral {j : ℕ} (hj : 0 < j) (k : ℕ) :
    ∫ a : ℝ, (Set.Ioi (0 : ℝ)).indicator
      (fun x => (-1 : ℝ) ^ k
        * (x * Real.exp (-Real.pi * ((k + 1 : ℕ) : ℝ) * ((j : ℕ) : ℝ) * x))) a ∂volume
      = (-1 : ℝ) ^ k / (Real.pi * ((k + 1 : ℕ) : ℝ) * ((j : ℕ) : ℝ)) ^ 2 := by
  have hb : (0 : ℝ) < Real.pi * ((k + 1 : ℕ) : ℝ) * ((j : ℕ) : ℝ) :=
    mul_pos (mul_pos Real.pi_pos (by exact_mod_cast (Nat.succ_pos k))) (by exact_mod_cast hj)
  have hintX : IntegrableOn (fun x => x * Real.exp
      (-Real.pi * ((k + 1 : ℕ) : ℝ) * ((j : ℕ) : ℝ) * x)) (Ioi (0 : ℝ)) volume := by
    have hexp := integrable_x_exp hb
    refine hexp.congr_fun (fun x _ => ?_) measurableSet_Ioi
    show x * Real.exp (-(Real.pi * ((k + 1 : ℕ) : ℝ) * ((j : ℕ) : ℝ)) * x)
        = x * Real.exp (-Real.pi * ((k + 1 : ℕ) : ℝ) * ((j : ℕ) : ℝ) * x)
    have he : (-(Real.pi * ((k + 1 : ℕ) : ℝ) * ((j : ℕ) : ℝ)) * x)
        = (-Real.pi * ((k + 1 : ℕ) : ℝ) * ((j : ℕ) : ℝ) * x) := by ring
    rw [he]
  have hI : ∫ x in Ioi (0 : ℝ), x * Real.exp
      (-Real.pi * ((k + 1 : ℕ) : ℝ) * ((j : ℕ) : ℝ) * x) ∂volume
      = 1 / (Real.pi * ((k + 1 : ℕ) : ℝ) * ((j : ℕ) : ℝ)) ^ 2 := by
    have hval := integral_exp_neg_mul hb
    rw [setIntegral_congr measurableSet_Ioi (fun x _ => by
      show x * Real.exp (-Real.pi * ((k + 1 : ℕ) : ℝ) * ((j : ℕ) : ℝ) * x)
          = x * Real.exp (-(Real.pi * ((k + 1 : ℕ) : ℝ) * ((j : ℕ) : ℝ)) * x)
      have he : (-(Real.pi * ((k + 1 : ℕ) : ℝ) * ((j : ℕ) : ℝ)) * x)
          = (-Real.pi * ((k + 1 : ℕ) : ℝ) * ((j : ℕ) : ℝ) * x) := by ring
      rw [he])]
    exact hval
  rw [integral_indicator measurableSet_Ioi, setIntegral_const_mul measurableSet_Ioi
      ((-1 : ℝ) ^ k) hintX, hI, mul_one_div]

/-- **The Lambert integral evaluation**: each Fourier-Lambert piece of the
theta-quotient integrates to `1/(12 j^2)`, riding `eta(2) = pi^2/12`. -/
theorem integral_exp_div_one_add {j : ℕ} (hj : 0 < j) :
    ∫ x in Ioi (0 : ℝ), x * Real.exp (-Real.pi * ((j : ℕ) : ℝ) * x)
        / (1 + Real.exp (-Real.pi * ((j : ℕ) : ℝ) * x)) ∂volume
      = 1 / (12 * ((j : ℕ) : ℝ) ^ 2) := by
  have hDC := lamDC_hasSum hj
  have hvalsplit : (∫ a : ℝ, (Set.Ioi (0 : ℝ)).indicator (fun x => x
        * Real.exp (-Real.pi * ((j : ℕ) : ℝ) * x)
        / (1 + Real.exp (-Real.pi * ((j : ℕ) : ℝ) * x))) a ∂volume)
      = ∫ x in Set.Ioi (0 : ℝ), x * Real.exp (-Real.pi * ((j : ℕ) : ℝ) * x)
        / (1 + Real.exp (-Real.pi * ((j : ℕ) : ℝ) * x)) ∂volume :=
    integral_indicator measurableSet_Ioi
  rw [hvalsplit] at hDC
  have hfamconv : ∀ k : ℕ,
      (-1 : ℝ) ^ k / (Real.pi * ((k + 1 : ℕ) : ℝ) * ((j : ℕ) : ℝ)) ^ 2
      = ∫ a : ℝ, (Set.Ioi (0 : ℝ)).indicator
      (fun x => (-1 : ℝ) ^ k
        * (x * Real.exp (-Real.pi * ((k + 1 : ℕ) : ℝ) * ((j : ℕ) : ℝ) * x))) a ∂volume :=
    fun k => (lamFam_integral hj k).symm
  have hDC2 := hDC.congr_fun hfamconv
  have heta := hasSum_eta_two
  have hscale := HasSum.const_smul (1 / (Real.pi ^ 2 * ((j : ℕ) : ℝ) ^ 2)) heta
  have hπ : Real.pi ≠ 0 := ne_of_gt Real.pi_pos
  have hjne : ((j : ℕ) : ℝ) ≠ 0 := by exact_mod_cast hj.ne'
  have hfam2 : ∀ k : ℕ,
      (-1 : ℝ) ^ k / (Real.pi * ((k + 1 : ℕ) : ℝ) * ((j : ℕ) : ℝ)) ^ 2
      = (1 / (Real.pi ^ 2 * ((j : ℕ) : ℝ) ^ 2))
        • ((-1 : ℝ) ^ k / (((k + 1 : ℕ) : ℝ) ^ 2)) := by
    intro k
    have hkne : (((k + 1 : ℕ) : ℝ)) ≠ 0 := by exact_mod_cast (Nat.succ_ne_zero k)
    rw [smul_eq_mul]
    field_simp
  have heta2 := hscale.congr_fun hfam2
  have hv : (1 / (Real.pi ^ 2 * ((j : ℕ) : ℝ) ^ 2)) • (Real.pi ^ 2 / 12)
      = 1 / (12 * ((j : ℕ) : ℝ) ^ 2) := by
    rw [smul_eq_mul]
    field_simp
  rw [hv] at heta2
  exact HasSum.unique hDC2 heta2

/-! ## W2-E stone A: the per-term tail machinery (sure keeps) -/

/-- Exponent conversion: `e^{-pi n x}` is the `n`-th power of `e^{-pi x}`. -/
private theorem exp_pow_nat (n : ℕ) (x : ℝ) :
    Real.exp (-Real.pi * ((n : ℕ) : ℝ) * x) = Real.exp (-Real.pi * x) ^ n := by
  have h1 : (-Real.pi * ((n : ℕ) : ℝ) * x) = ((n : ℕ) : ℝ) * (-Real.pi * x) := by ring
  rw [h1, exp_pow_self]

/-- The Lambert series term, in exponent form:
`(m+1) q^{m+1} / (1 + q^{m+1})` with alternating sign, `q = e^{-pi x}`. -/
private noncomputable def lamTerm (m : ℕ) (x : ℝ) : ℝ :=
  (-1 : ℝ) ^ (m + 1) * (((m + 1 : ℕ) : ℝ))
    * Real.exp (-Real.pi * ((m + 1 : ℕ) : ℝ) * x)
    / (1 + Real.exp (-Real.pi * ((m + 1 : ℕ) : ℝ) * x))

/-- The per-term bound: `x * |lamTerm m x| <= (1/pi) e^{-pi (m+1) x / 2}`,
from `u <= e^{u/2}` — the triangle-inequality bound that kills all
alternating/unimodal machinery for a single term. -/
private theorem abs_lamTerm_mul_le (m : ℕ) {x : ℝ} (hx : 0 ≤ x) :
    x * |lamTerm m x|
      ≤ (1 / Real.pi) * Real.exp (-(Real.pi * ((m + 1 : ℕ) : ℝ) * x / 2)) := by
  set E := Real.exp (-Real.pi * ((m + 1 : ℕ) : ℝ) * x) with hE
  have hEpos : (0 : ℝ) < E := Real.exp_pos _
  have hπpos : (0 : ℝ) < Real.pi := Real.pi_pos
  have hmp : (0 : ℝ) ≤ ((m + 1 : ℕ) : ℝ) := Nat.cast_nonneg _
  have habs : |lamTerm m x| = ((m + 1 : ℕ) : ℝ) * E / (1 + E) := by
    rw [lamTerm, ← hE]
    rw [abs_div, abs_mul, abs_mul, abs_pow, abs_neg, abs_one, one_pow]
    rw [abs_of_nonneg (Nat.cast_nonneg (m + 1 : ℕ)),
      abs_of_pos hEpos,
      abs_of_nonneg (by linarith : (0 : ℝ) ≤ 1 + E)]
    rw [one_mul]
  have key2 : E / (1 + E) ≤ E := by
    refine (div_le_iff₀ (by linarith : (0 : ℝ) < 1 + E)).mpr ?_
    nlinarith [sq_nonneg E]
  have key3 : Real.pi * ((m + 1 : ℕ) : ℝ) * x
      ≤ Real.exp (Real.pi * ((m + 1 : ℕ) : ℝ) * x / 2) :=
    le_exp_half (mul_nonneg (mul_nonneg hπpos.le hmp) hx)
  have key4 : Real.exp (Real.pi * ((m + 1 : ℕ) : ℝ) * x / 2)
      * Real.exp (-Real.pi * ((m + 1 : ℕ) : ℝ) * x)
      = Real.exp (-(Real.pi * ((m + 1 : ℕ) : ℝ) * x / 2)) := by
    rw [← Real.exp_add]
    ring
  have hc0 : (0 : ℝ) ≤ Real.pi * ((m + 1 : ℕ) : ℝ) * x / Real.pi :=
    div_nonneg (mul_nonneg (mul_nonneg hπpos.le hmp) hx) hπpos.le
  rw [habs]
  calc x * (((m + 1 : ℕ) : ℝ) * E / (1 + E))
      = (Real.pi * ((m + 1 : ℕ) : ℝ) * x / Real.pi) * (E / (1 + E)) := by
        field_simp
    _ ≤ (Real.pi * ((m + 1 : ℕ) : ℝ) * x / Real.pi) * E :=
        mul_le_mul_of_nonneg_left key2 hc0
    _ ≤ (Real.exp (Real.pi * ((m + 1 : ℕ) : ℝ) * x / 2) / Real.pi)
        * Real.exp (-Real.pi * ((m + 1 : ℕ) : ℝ) * x) := by
        refine mul_le_mul_of_nonneg_right ?_ hEpos.le
        rw [div_le_div_iff₀ hπpos hπpos]
        exact mul_le_mul_of_nonneg_right key3 hπpos.le
    _ = (1 / Real.pi) * Real.exp (-(Real.pi * ((m + 1 : ℕ) : ℝ) * x / 2)) := by
        rw [div_mul_eq_mul_div, key4]
        field_simp

/-- Own helper: the triangle inequality for finite partial sums
(the vintage's `Finset.abs_sum_le_sum_abs` name lottery is skipped). -/
private theorem abs_sum_range_le (f : ℕ → ℝ) (N : ℕ) :
    |∑ i ∈ Finset.range N, f i| ≤ ∑ i ∈ Finset.range N, |f i| := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Finset.sum_range_succ, Finset.sum_range_succ]
    have h1 : ∑ i ∈ Finset.range N, f i ≤ |∑ i ∈ Finset.range N, f i| :=
      le_abs_self _
    have h2 : f N ≤ |f N| := le_abs_self _
    have h5 : -(∑ i ∈ Finset.range N, f i) ≤ |∑ i ∈ Finset.range N, f i| := by
      have h := le_abs_self (-(∑ i ∈ Finset.range N, f i))
      rwa [abs_neg] at h
    have h6 : -f N ≤ |f N| := by
      have h := le_abs_self (-f N)
      rwa [abs_neg] at h
    exact abs_le.2 ⟨by linarith, add_le_add (h1.trans ih) h2⟩

end YangMills.DualBook
