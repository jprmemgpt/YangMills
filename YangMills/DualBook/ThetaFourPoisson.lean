/-
  PROVENANCE: YangMills.DualBook.ThetaFourPoisson (R237, closing w1).

  PROVED. Built green in the c1660 window (Thu 2026-11-26, Mathlib
  31ce06ea / Lean v4.37.0-rc1 vintage): lake build zero errors, zero
  sorry, zero native_decide, zero unsafe; notarized
  [propext, Classical.choice, Quot.sound] on all six public theorems
  (kernel1000_integrable_small, kernelDiff_integrable_small,
  kernel1000_integrable_union, kernelDiff_integrable_union,
  kernel1000_integrable_full, kernelDiff_integrable_full).
  This window CLOSES W1: the 1000 and diff kernels are integrable on
  the full half-line, the last open half of R236's large-t floor.
  Bench frozen at 100.0. Scope: THIS ARITHMETIC only.

  PRE-REGISTERED (order 1126, Papa's 164th ask, Gemini's relay): discharge
  window (w1), the small-t half of the 1000 kernel, through the
  half-lattice Poisson stone `thetaFour t = (√t)⁻¹ * thetaTwo (1/t)`
  (the route order 1113 flagged, the one that also banks the modular
  engine the Z_1111(2) window will need). Nothing re-proved that is
  already paid: thetaT_summable / thetaT_blowup / thetaT_nonneg (R233),
  thetaT_transform (R234), abs_thetaFour_le_one (R235),
  kernel1110_integrable_full / kernel1000_integrable_large /
  kernelDiff_integrable_large (R236) are imported and used as receipts.

  STONES OF THIS WINDOW:

  (STONE i) THE DUAL THETA (theta-2 on the time axis):
      thetaTwo u = ∑' z : ℤ, exp (−π·u·(z − 1/2)²)
  the half-lattice Gaussian sum, summable for u > 0 and strictly
  positive, with the dual gain `thetaTwo u ≤ 4·exp (−πu/4)` on
  `[1, ∞)` (each half's tail geometric in the dual variable).

  (STONE ii) THE TRANSFORM (the half-lattice Poisson stone):
      thetaFour t = (√t)⁻¹ * thetaTwo (1/t)    for t > 0,
  proved from Mathlib's `Complex.tsum_exp_neg_quadratic` at the
  character `b = I/2`: the alternating lattice is the half-shifted
  dual of itself (`Real.tsum_exp_neg_mul_int_sq` is the b = 0 face of
  the same stone, the one R234 rode for thetaT_transform). Corollary:
  thetaFour is strictly positive on the time axis.

  (STONE iii) THE SUPER-EXPONENTIAL DEATH:
      thetaFour t ≤ (√t)⁻¹ * 4 * exp (−π/(4t))    on (0, 1],
  the transform read through the dual gain: thetaFour dies faster
  than any power as t → 0, the exact opposite face of the R235
  deficit law.

  (STONE iv) WINDOW (w1) DISCHARGED:
      kernel1000 small half: |t·(gauss1000 t − 1)| ≤ 2048/9 + 1 on (0, 1]
        (the death kills thetaT^3's t^(−3/2) blow-up through
        exp(−y) ≤ (2/y)², the receipt exp(y/2) ≥ 1 + y/2 squared);
      kernel1000_integrable_full: the 1000 arm's s = 2 kernel is
        unconditionally integrable on (0, ∞) -- ZAdic1000 EXISTS;
      kernelDiff small/union/full: the factored difference spine
        t·(gauss1000 − gauss1110) is unconditionally integrable too.
  The closed-form VALUES remain the named window (w2); the Mellin
  scaling cascade (w3) is the named next window. Bench frozen at 100.0.
  Scope: THIS ARITHMETIC only.
-/
import Mathlib.Algebra.Order.GroupWithZero.Basic
import Mathlib.Algebra.Order.Monoid.Unbundled.Pow
import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Analysis.SpecialFunctions.Gaussian.PoissonSummation
import YangMills.DualBook.GaussArm

namespace YangMills.DualBook
open MeasureTheory Real Set

/-! ## Stone i: the dual theta (theta-2 on the time axis) -/

/-- THE 2-ADIC DUAL THETA: the half-lattice Gaussian sum
`thetaTwo u = ∑' z : ℤ, exp (−π·u·(z − 1/2)²)`, the dual face of
thetaFour under the Poisson transformation and the object whose
exponentially small tail (the dual gain, below) pays for thetaFour's
super-exponential small-t death. -/
noncomputable def thetaTwo (u : ℝ) : ℝ :=
  ∑' (z : ℤ), Real.exp (-Real.pi * u * ((z : ℝ) - 1 / 2) ^ 2)

/-- The half-lattice family behind thetaTwo. -/
private noncomputable def thetaTwoFam (u : ℝ) (z : ℤ) : ℝ :=
  Real.exp (-Real.pi * u * ((z : ℝ) - 1 / 2) ^ 2)

private theorem thetaTwo_eq_tsumFam (u : ℝ) :
    thetaTwo u = ∑' (z : ℤ), thetaTwoFam u z := rfl

/-- The positive half's per-term bound: `exp (−πu·(n − 1/2)²) ≤
exp (−πu/4) ^ n`, the pair `n/4 ≤ (n − 1/2)²` (case split at the
missing zero mode) feeding the geometric comparison. -/
private theorem thetaTwoPosTerm_le {u : ℝ} (hu : 0 < u) (n : ℕ) :
    Real.exp (-Real.pi * u * (((n : ℝ) - 1 / 2) ^ 2))
      ≤ Real.exp (-(Real.pi * u / 4)) ^ n := by
  have hsq : (n:ℝ)/4 ≤ ((n:ℝ) - 1/2) ^ 2 := by
    cases n with
    | zero => norm_num
    | succ n' =>
      have hm : (0:ℝ) ≤ ((n' : ℕ) : ℝ) := Nat.cast_nonneg _
      simp only [Nat.cast_add, Nat.cast_one]
      nlinarith [sq_nonneg (((n' : ℕ) : ℝ)), hm]
  have hmono : Real.exp (-Real.pi * u * (((n : ℝ) - 1 / 2) ^ 2))
      ≤ Real.exp ((n:ℝ) * -(Real.pi * u / 4)) := by
    refine Real.exp_le_exp.mpr ?_
    rw [show (n:ℝ) * -(Real.pi * u / 4) = -(Real.pi * u * ((n:ℝ) / 4)) from by ring]
    rw [show -Real.pi * u * ((n : ℝ) - 1 / 2) ^ 2 = -(Real.pi * u * ((n : ℝ) - 1 / 2) ^ 2) from by ring]
    exact neg_le_neg (mul_le_mul_of_nonneg_left hsq (mul_nonneg Real.pi_pos.le hu.le))
  rw [← Real.exp_natCast_mul n (-(Real.pi * u / 4))]
  exact hmono

/-- The negative half's per-term bound: `exp (−πu·(n + 1/2)²) ≤
exp (−πu/4) ^ n`, the pair `n/4 ≤ (n + 1/2)²` (uniform, the negative
half has no missing mode). -/
private theorem thetaTwoNegTerm_le {u : ℝ} (hu : 0 < u) (n : ℕ) :
    Real.exp (-Real.pi * u * ((((n : ℕ) : ℝ) + 1 / 2) ^ 2))
      ≤ Real.exp (-(Real.pi * u / 4)) ^ n := by
  have hsq : (n:ℝ)/4 ≤ (((n:ℕ):ℝ) + 1/2) ^ 2 := by
    have hring : (((n:ℕ):ℝ) + 1/2) ^ 2 = (n:ℝ) * (n:ℝ) + (n:ℝ) + 1/4 := by
      push_cast
      ring
    rw [hring]
    nlinarith [sq_nonneg ((n:ℝ) - 1/2)]
  have hmono : Real.exp (-Real.pi * u * ((((n : ℕ) : ℝ) + 1 / 2) ^ 2))
      ≤ Real.exp ((n:ℝ) * -(Real.pi * u / 4)) := by
    refine Real.exp_le_exp.mpr ?_
    rw [show (n:ℝ) * -(Real.pi * u / 4) = -(Real.pi * u * ((n:ℝ) / 4)) from by ring]
    rw [show -Real.pi * u * (((n : ℕ) : ℝ) + 1 / 2) ^ 2 = -(Real.pi * u * (((n : ℕ) : ℝ) + 1 / 2) ^ 2) from by ring]
    exact neg_le_neg (mul_le_mul_of_nonneg_left hsq (mul_nonneg Real.pi_pos.le hu.le))
  rw [← Real.exp_natCast_mul n (-(Real.pi * u / 4))]
  exact hmono

/-- The per-term dual bound for the positive tail face:
`exp (−πu·(n + 1/2)²) ≤ exp (−πu/4) · exp (−πu) ^ n`, the pair
`(1/4 + n) ≤ (n + 1/2)²` feeding the exponential's monotonicity and
the split `exp (a + b) = exp a · exp b` feeding the geometric
comparison. -/
private theorem thetaTwoTerm_bound {u : ℝ} (hu : 0 < u) (n : ℕ) :
    Real.exp (-Real.pi * u * (((n : ℝ) + 1 / 2) ^ 2))
      ≤ Real.exp (-(Real.pi * u / 4)) * Real.exp (-(Real.pi * u)) ^ n := by
  have hsq : (1:ℝ)/4 + (n:ℝ) ≤ ((n:ℝ) + 1/2) ^ 2 := by
    have hring : ((n:ℝ) + 1/2) ^ 2 = (n:ℝ) * (n:ℝ) + (n:ℝ) + 1/4 := by ring
    rw [hring]
    nlinarith [sq_nonneg ((n:ℝ) - 1/2)]
  have hmono : Real.exp (-Real.pi * u * (((n : ℝ) + 1 / 2) ^ 2))
      ≤ Real.exp (-(Real.pi * u / 4) + (n:ℝ) * -(Real.pi * u)) := by
    refine Real.exp_le_exp.mpr ?_
    rw [show -(Real.pi * u / 4) + (n:ℝ) * -(Real.pi * u)
        = -(Real.pi * u * (1/4 + (n:ℝ))) from by ring]
    rw [show -Real.pi * u * ((n : ℝ) + 1 / 2) ^ 2 = -(Real.pi * u * ((n : ℝ) + 1 / 2) ^ 2) from by ring]
    exact neg_le_neg (mul_le_mul_of_nonneg_left hsq (mul_nonneg Real.pi_pos.le hu.le))
  rw [← Real.exp_natCast_mul n (-(Real.pi * u)), ← Real.exp_add]
  exact hmono

/-- The per-term dual bound for the shifted negative tail face:
`exp (−πu·(n + 3/2)²) ≤ exp (−πu/4) · exp (−πu) ^ (n+1)`. -/
private theorem thetaTwoTermNeg_bound {u : ℝ} (hu : 0 < u) (n : ℕ) :
    Real.exp (-Real.pi * u * (((n : ℝ) + 1 + 1 / 2) ^ 2))
      ≤ Real.exp (-(Real.pi * u / 4)) * Real.exp (-(Real.pi * u)) ^ (n + 1) := by
  have hsq : (1:ℝ)/4 + ((n:ℝ) + 1) ≤ ((n:ℝ) + 1 + 1/2) ^ 2 := by
    have hring : ((n:ℝ) + 1 + 1/2) ^ 2
        = ((n:ℝ) + 1) * ((n:ℝ) + 1) + ((n:ℝ) + 1) + 1/4 := by ring
    rw [hring]
    nlinarith [sq_nonneg ((n:ℝ) + 1/2)]
  have hmono : Real.exp (-Real.pi * u * (((n : ℝ) + 1 + 1 / 2) ^ 2))
      ≤ Real.exp (-(Real.pi * u / 4) + ((n:ℝ) + 1) * -(Real.pi * u)) := by
    refine Real.exp_le_exp.mpr ?_
    rw [show -(Real.pi * u / 4) + ((n:ℝ) + 1) * -(Real.pi * u)
        = -(Real.pi * u * (1/4 + ((n:ℝ) + 1))) from by ring]
    rw [show -Real.pi * u * ((n : ℝ) + 1 + 1 / 2) ^ 2 = -(Real.pi * u * ((n : ℝ) + 1 + 1 / 2) ^ 2) from by ring]
    exact neg_le_neg (mul_le_mul_of_nonneg_left hsq (mul_nonneg Real.pi_pos.le hu.le))
  rw [← Real.exp_natCast_mul (n + 1) (-(Real.pi * u)), ← Real.exp_add]
  push_cast
  exact hmono

/-- The geometric ratio of the dual world lies in (0, 1). -/
private theorem dual_ratio_lt_one {u : ℝ} (hu : 0 < u) :
    0 < Real.exp (-(Real.pi * u / 4)) ∧ Real.exp (-(Real.pi * u / 4)) < 1 := by
  constructor
  · exact Real.exp_pos _
  · have hpos : 0 < Real.pi * u / 4 := by
      exact div_pos (mul_pos Real.pi_pos hu) (by norm_num)
    have h1 : Real.exp (-(Real.pi * u / 4)) < Real.exp (0:ℝ) :=
      Real.exp_lt_exp.mpr (by linarith [hpos])
    simpa using h1

/-- The positive half of the lattice family is summable. -/
private theorem thetaTwoNat_summable {u : ℝ} (hu : 0 < u) :
    Summable (fun n : ℕ => thetaTwoFam u ((n : ℕ) : ℤ)) := by
  have hq := dual_ratio_lt_one hu
  have hgeom : Summable (fun n : ℕ => Real.exp (-(Real.pi * u / 4)) ^ n) :=
    summable_geometric_of_lt_one hq.1.le hq.2
  refine Summable.of_norm_bounded hgeom ?_
  intro n
  simp only [Real.norm_eq_abs, thetaTwoFam]
  push_cast
  rw [abs_of_nonneg (Real.exp_pos _).le]
  exact thetaTwoPosTerm_le hu n

/-- The negative half of the lattice family is summable. -/
private theorem thetaTwoNegNat_summable {u : ℝ} (hu : 0 < u) :
    Summable (fun n : ℕ => thetaTwoFam u (-((n : ℕ) : ℤ))) := by
  have hq := dual_ratio_lt_one hu
  have hgeom : Summable (fun n : ℕ => Real.exp (-(Real.pi * u / 4)) ^ n) :=
    summable_geometric_of_lt_one hq.1.le hq.2
  refine Summable.of_norm_bounded hgeom ?_
  intro n
  have hcast : thetaTwoFam u (-((n : ℕ) : ℤ))
      = Real.exp (-Real.pi * u * ((((n : ℕ) : ℝ) + 1 / 2) ^ 2)) := by
    simp only [thetaTwoFam]
    push_cast
    congr 1
    ring
  simp only [Real.norm_eq_abs]
  rw [hcast, abs_of_nonneg (Real.exp_pos _).le]
  exact thetaTwoNegTerm_le hu n

/-- The dual family is summable: both halves are dominated by the
geometric series at ratio `exp (−πu/4) < 1`. -/
private theorem thetaTwoFam_summable {u : ℝ} (hu : 0 < u) :
    Summable (thetaTwoFam u) :=
  Summable.of_nat_of_neg (thetaTwoNat_summable hu) (thetaTwoNegNat_summable hu)

/-- THE DUAL THETA IS STRICTLY POSITIVE: the half-lattice sum owns a
positive term (every term is positive, the Gaussian). -/
theorem thetaTwo_pos {u : ℝ} (hu : 0 < u) : 0 < thetaTwo u := by
  have hsum : Summable (thetaTwoFam u) := thetaTwoFam_summable hu
  have hnn : ∀ z : ℤ, 0 ≤ thetaTwoFam u z := by
    intro z
    simp only [thetaTwoFam]
    positivity
  have hpos : 0 < thetaTwoFam u 1 := by
    simp only [thetaTwoFam]
    positivity
  have hle : thetaTwoFam u 1 ≤ ∑' (z : ℤ), thetaTwoFam u z := by
    have h := hsum.sum_le_tsum ({1} : Finset ℤ) (fun _ _ => hnn _)
    simpa using h
  rw [thetaTwo_eq_tsumFam]
  linarith [hle, hpos]

/-- THE DUAL GAIN: for `1 ≤ u` the dual theta obeys the exponentially
small bound `thetaTwo u ≤ 4·exp (−πu/4)`. The lattice splits into the
zero mode, the positive half and the negative half
(`tsum_int_eq_zero_add_tsum_pnat`, no evenness needed); each half's
tail is geometric at ratio `q = exp (−πu) ≤ 1/2`, summed by
`tsum_geometric_of_lt_one`. The exact mirror, on the dual side, of the
R233 blow-up law sharpened by the R234 transform. -/
theorem thetaTwo_decay {u : ℝ} (hu1 : (1:ℝ) ≤ u) :
    thetaTwo u ≤ 4 * Real.exp (-(Real.pi * u / 4)) := by
  have hu : 0 < u := by linarith
  set E : ℝ := Real.exp (-(Real.pi * u / 4)) with hEdef
  have hEpos : 0 < E := by
    rw [hEdef]
    exact Real.exp_pos _
  set q : ℝ := Real.exp (-(Real.pi * u)) with hqdef
  have hq1 : 0 < q := by
    rw [hqdef]
    exact Real.exp_pos _
  have hq2 : q < 1 := by
    rw [hqdef, Real.exp_lt_one_iff]
    have hpu : 0 < Real.pi * u := mul_pos Real.pi_pos hu
    linarith [hpu]
  have hqle : q ≤ 1/2 := by
    have h1 : q ≤ Real.exp (-(Real.pi)) := by
      rw [hqdef]
      refine Real.exp_le_exp.mpr ?_
      have hpi : 0 < Real.pi := Real.pi_pos
      nlinarith [hpi, hu1]
    have h2 : (2:ℝ) ≤ Real.exp Real.pi := by
      have h3 := Real.add_one_le_exp Real.pi
      have h4 : (1:ℝ) ≤ Real.pi := by
        have := Real.pi_gt_three
        linarith
      linarith
    have h5b : Real.exp (-(Real.pi)) = (1:ℝ)/(Real.exp Real.pi) := by
      rw [Real.exp_neg, one_div]
    have h6 : (1:ℝ)/(Real.exp Real.pi) ≤ (1:ℝ)/2 := by
      rw [div_le_div_iff₀ (Real.exp_pos _) (by norm_num)]
      linarith [h2]
    exact h1.trans (h5b ▸ h6)
  -- the zero mode
  have hf0 : thetaTwoFam u 0 = E := by
    have h : thetaTwoFam u 0 = Real.exp (-(Real.pi * u / 4)) := by
      simp only [thetaTwoFam]
      congr 1
      ring
    rwa [← hEdef] at h
  -- the positive half: geometric in n, evaluated
  have hpossum : ∑' p : ℕ+, thetaTwoFam u ((p : ℕ) : ℤ) ≤ E / (1 - q) := by
    rw [tsum_pnat_eq_tsum_succ (f := fun n : ℕ => thetaTwoFam u ((n : ℕ) : ℤ))]
    have hle : ∀ n : ℕ,
        thetaTwoFam u (((n : ℕ) + 1 : ℕ) : ℤ) ≤ E * q ^ n := by
      intro n
      have hcast : thetaTwoFam u (((n : ℕ) + 1 : ℕ) : ℤ)
          = Real.exp (-Real.pi * u * (((n : ℝ) + 1 / 2) ^ 2)) := by
        simp only [thetaTwoFam]
        push_cast
        congr 1
        ring
      rw [hcast]
      have hterm := thetaTwoTerm_bound hu n
      rw [← hEdef] at hterm
      rw [← hqdef] at hterm
      exact hterm
    have hgeom : Summable (fun n : ℕ => q ^ n) :=
      summable_geometric_of_lt_one hq1.le hq2
    have hsum1 : Summable (fun n : ℕ => thetaTwoFam u (((n : ℕ) + 1 : ℕ) : ℤ)) :=
      (summable_nat_add_iff 1).mpr (thetaTwoNat_summable hu)
    have hsum2 : Summable (fun n : ℕ => E * q ^ n) := hgeom.mul_left E
    have hval : ∑' (n : ℕ), q ^ n = 1 / (1 - q) :=
      (tsum_geometric_of_lt_one hq1.le hq2).trans (one_div (1 - q)).symm
    calc ∑' n : ℕ, thetaTwoFam u (((n : ℕ) + 1 : ℕ) : ℤ)
        ≤ ∑' n : ℕ, E * q ^ n :=
          Summable.tsum_le_tsum hle hsum1 hsum2
      _ = E * ∑' (n : ℕ), q ^ n := hgeom.tsum_mul_left E
      _ = E * (1 / (1 - q)) := by rw [hval]
      _ = E / (1 - q) := by ring
  -- the negative half: geometric in n+1, evaluated
  have hnegsum : ∑' p : ℕ+, thetaTwoFam u (-((p : ℕ) : ℤ)) ≤ E * q / (1 - q) := by
    rw [tsum_pnat_eq_tsum_succ (f := fun n : ℕ => thetaTwoFam u (-((n : ℕ) : ℤ)))]
    have hle : ∀ n : ℕ,
        thetaTwoFam u (-(((n : ℕ) + 1 : ℕ) : ℤ)) ≤ E * q ^ (n + 1) := by
      intro n
      have hcast : thetaTwoFam u (-(((n : ℕ) + 1 : ℕ) : ℤ))
          = Real.exp (-Real.pi * u * (((n : ℝ) + 1 + 1 / 2) ^ 2)) := by
        simp only [thetaTwoFam]
        push_cast
        congr 1
        ring
      rw [hcast]
      have hterm := thetaTwoTermNeg_bound hu n
      rw [← hEdef] at hterm
      rw [← hqdef] at hterm
      exact hterm
    have hgeom : Summable (fun n : ℕ => q ^ n) :=
      summable_geometric_of_lt_one hq1.le hq2
    have hshift : Summable (fun n : ℕ => q ^ (n + 1)) :=
      (summable_nat_add_iff 1).mpr hgeom
    have hsum1 : Summable
        (fun n : ℕ => thetaTwoFam u (-(((n : ℕ) + 1 : ℕ) : ℤ))) :=
      (summable_nat_add_iff 1).mpr (thetaTwoNegNat_summable hu)
    have hsum2 : Summable (fun n : ℕ => E * q ^ (n + 1)) := hshift.mul_left E
    have hval : ∑' (n : ℕ), q ^ (n + 1) = q / (1 - q) := by
      have hcong : ∀ n : ℕ, q ^ (n + 1) = q * q ^ n := fun n => by ring
      rw [tsum_congr hcong]
      rw [hgeom.tsum_mul_left q, tsum_geometric_of_lt_one hq1.le hq2]
      ring
    calc ∑' n : ℕ, thetaTwoFam u (-(((n : ℕ) + 1 : ℕ) : ℤ))
        ≤ ∑' n : ℕ, E * q ^ (n + 1) :=
          Summable.tsum_le_tsum hle hsum1 hsum2
      _ = E * ∑' (n : ℕ), q ^ (n + 1) := hshift.tsum_mul_left E
      _ = E * (q / (1 - q)) := by rw [hval]
      _ = E * q / (1 - q) := by ring
  -- assemble: E + E/(1−q) + E·q/(1−q) ≤ 4E since q ≤ 1/2
  have hqpos : (0:ℝ) < 1 - q := by nlinarith [hq2]
  have hR : 1 / (1 - q) ≤ 2 := by
    field_simp
    nlinarith [hqle]
  have hqR : q / (1 - q) ≤ 1 := by
    field_simp
    nlinarith [hqle]
  have hA2 : ∑' p : ℕ+, thetaTwoFam u ((p : ℕ) : ℤ) ≤ 2 * E := by
    have h1 : ∑' p : ℕ+, thetaTwoFam u ((p : ℕ) : ℤ) ≤ E * (1 / (1 - q)) := by
      have h := hpossum
      rwa [show E / (1 - q) = E * (1 / (1 - q)) from by ring] at h
    exact h1.trans ((mul_le_mul_of_nonneg_left hR hEpos.le).trans_eq (mul_comm E 2))
  have hB2 : ∑' p : ℕ+, thetaTwoFam u (-((p : ℕ) : ℤ)) ≤ E := by
    have h1 : ∑' p : ℕ+, thetaTwoFam u (-((p : ℕ) : ℤ)) ≤ E * (q / (1 - q)) := by
      have h := hnegsum
      rwa [show E * q / (1 - q) = E * (q / (1 - q)) from by ring] at h
    exact h1.trans ((mul_le_mul_of_nonneg_left hqR hEpos.le).trans_eq (mul_one E))
  have hsplit := tsum_int_eq_zero_add_tsum_pnat (thetaTwoFam_summable hu)
  rw [thetaTwo_eq_tsumFam, hsplit, hf0]
  linarith [hA2, hB2]

/-! ## Stone ii: the transform (the half-lattice Poisson stone) -/

/-- The Gaussian lattice family on ℤ (private mirror of R233's
receipt; the integral-free geometric route `n ≤ n²` suffices here). -/
private noncomputable def gaussFam' (t : ℝ) (z : ℤ) : ℝ :=
  Real.exp (-Real.pi * t * ((z : ℝ)) ^ 2)

/-- The Gaussian lattice family is summable, both halves geometric at
ratio `exp (−πt) < 1` through `n ≤ n²`. -/
private theorem gaussFam'_summable {t : ℝ} (ht : 0 < t) :
    Summable (gaussFam' t) := by
  have hq1 : 0 < Real.exp (-(Real.pi * t)) := Real.exp_pos _
  have hq2 : Real.exp (-(Real.pi * t)) < 1 := by
    rw [Real.exp_lt_one_iff]
    have hpt : 0 < Real.pi * t := mul_pos Real.pi_pos ht
    linarith [hpt]
  have hgeom : Summable (fun n : ℕ => Real.exp (-(Real.pi * t)) ^ n) :=
    summable_geometric_of_lt_one hq1.le hq2
  have hsq : ∀ n : ℕ, ((n:ℕ):ℝ) ≤ ((n:ℕ):ℝ) ^ 2 := by
    intro n
    cases n with
    | zero => norm_num
    | succ n' =>
      have hm : (0:ℝ) ≤ ((n' : ℕ) : ℝ) := Nat.cast_nonneg _
      simp only [Nat.cast_add, Nat.cast_one]
      nlinarith [sq_nonneg (((n' : ℕ) : ℝ)), hm]
  have hmono : ∀ n : ℕ,
      Real.exp (-(Real.pi * t) * (((n:ℕ):ℝ) ^ 2))
        ≤ Real.exp (-(Real.pi * t)) ^ n := by
    intro n
    rw [← Real.exp_natCast_mul n (-(Real.pi * t)),
      show ((n:ℕ):ℝ) * -(Real.pi * t) = -(Real.pi * t) * ((n:ℕ):ℝ) from by ring]
    refine Real.exp_le_exp.mpr ?_
    have h := neg_le_neg (mul_le_mul_of_nonneg_left (hsq n) (mul_nonneg Real.pi_pos.le ht.le))
    rw [neg_mul, neg_mul]
    exact h
  refine Summable.of_nat_of_neg ?_ ?_
  · refine Summable.of_norm_bounded hgeom ?_
    intro n
    simp only [Real.norm_eq_abs, gaussFam']
    push_cast
    rw [abs_of_nonneg (Real.exp_pos _).le, neg_mul]
    exact hmono n
  · refine Summable.of_norm_bounded hgeom ?_
    intro n
    have hcast : gaussFam' t (-((n : ℕ) : ℤ))
        = Real.exp (-(Real.pi * t) * (((n:ℕ):ℝ) ^ 2)) := by
      simp only [gaussFam']
      push_cast
      congr 1
      ring
    simp only [Real.norm_eq_abs]
    rw [hcast, abs_of_nonneg (Real.exp_pos _).le]
    exact hmono n

/-- The character receipt: the alternating sign carries absolute
value one (parity through `Int.even_or_odd`). -/
private theorem abs_neg_one_zpow (z : ℤ) : |(-1 : ℝ) ^ z| = 1 := by
  have hval : (-1 : ℝ) ^ z = 1 ∨ (-1 : ℝ) ^ z = -1 := by
    rcases z with (n : ℕ) | n
    · show (-1 : ℝ) ^ (n : ℤ) = 1 ∨ (-1 : ℝ) ^ (n : ℤ) = -1
      rw [zpow_natCast]
      exact neg_one_pow_eq_or ℝ n
    · rw [zpow_negSucc]
      rcases neg_one_pow_eq_or ℝ (n + 1) with h | h
      · left
        rw [h]
        norm_num
      · right
        rw [h]
        norm_num
  rcases hval with h | h
  · rw [h, abs_one]
  · rw [h, abs_neg, abs_one]

/-- The parity receipt: the alternating sign is always `±1`. -/
private theorem neg_one_zpow_eq_or (z : ℤ) :
    (-1 : ℝ) ^ z = 1 ∨ (-1 : ℝ) ^ z = -1 := by
  rcases z with (n : ℕ) | n
  · show (-1 : ℝ) ^ (n : ℤ) = 1 ∨ (-1 : ℝ) ^ (n : ℤ) = -1
    rw [zpow_natCast]
    exact neg_one_pow_eq_or ℝ n
  · rw [zpow_negSucc]
    rcases neg_one_pow_eq_or ℝ (n + 1) with h | h
    · left
      rw [h]
      norm_num
    · right
      rw [h]
      norm_num

/-- The alternating lattice family is summable: the sign carries norm
one, the Gaussian family dominates. -/
private theorem altFam_summable {t : ℝ} (ht : 0 < t) :
    Summable (fun z : ℤ =>
      (-1 : ℝ) ^ z * Real.exp (-Real.pi * t * ((z : ℝ)) ^ 2)) := by
  refine Summable.of_norm_bounded (gaussFam'_summable ht) ?_
  intro z
  simp only [Real.norm_eq_abs, gaussFam']
  rw [abs_mul, abs_neg_one_zpow, one_mul, abs_of_nonneg (Real.exp_pos _).le]

set_option maxHeartbeats 1000000 in
/-- The alternating value split: thetaFour equals the two-sided
alternating lattice sum `∑' z, (−1)^z · exp (−πt z²)`, through the
`tsum_int_eq_zero_add_two_mul_tsum_pnat` even twin (the alternating
sign is even: `(−1)^(−z) = (−1)^z`) and the theta4 nome unfolding. -/
private theorem thetaFour_eq_tsumInt {t : ℝ} (ht : 0 < t) :
    thetaFour t = ∑' (z : ℤ),
      (-1 : ℝ) ^ z * Real.exp (-Real.pi * t * ((z : ℝ)) ^ 2) := by
  have heven : Function.Even (fun z : ℤ =>
      (-1 : ℝ) ^ z * Real.exp (-Real.pi * t * ((z : ℝ)) ^ 2)) := by
    intro z
    show (-1 : ℝ) ^ (-z) * Real.exp (-Real.pi * t * ((-z : ℤ) : ℝ) ^ 2)
        = (-1 : ℝ) ^ z * Real.exp (-Real.pi * t * ((z : ℝ) ^ 2)
    have hsign : (-1 : ℝ) ^ (-z) = (-1 : ℝ) ^ z := by
      rw [zpow_neg]
      rcases neg_one_zpow_eq_or z with h | h
      · rw [h, inv_one]
      · rw [h]
        norm_num
    have hsq : Real.exp (-Real.pi * t * ((z : ℝ)) ^ 2)
        = Real.exp (-Real.pi * t * ((-z : ℤ) : ℝ) ^ 2) := by
      congr 1
      push_cast
      ring
    rw [hsign, hsq]
  have h0 : (-1 : ℝ) ^ (0 : ℤ)
      * Real.exp (-Real.pi * t * (((0 : ℤ) : ℝ)) ^ 2) = 1 := by
    norm_num
  have hsplit := tsum_int_eq_zero_add_two_mul_tsum_pnat
    heven (altFam_summable ht)
  rw [two_nsmul, ← two_mul] at hsplit
  have hpnat := tsum_pnat_eq_tsum_succ
    (f := fun n : ℕ =>
      (-1 : ℝ) ^ ((n : ℕ) : ℤ) * Real.exp (-Real.pi * t * (((n : ℕ) : ℤ) : ℝ) ^ 2))
  have hfinal : ∑' p : ℕ+,
      (-1 : ℝ) ^ ((p : ℕ) : ℤ) * Real.exp (-Real.pi * t * (((p : ℕ) : ℤ) : ℝ) ^ 2)
      = ∑' n : ℕ,
          (-1 : ℝ) ^ (((n : ℕ) + 1 : ℕ) : ℤ)
            * (Real.exp (-Real.pi * t)) ^ (((n : ℕ) + 1) ^ 2) := by
    rw [hpnat]
    refine tsum_congr (fun n => ?_)
    have hexp : Real.exp (-Real.pi * t * ((((n : ℕ) + 1 : ℕ) : ℤ) : ℝ) ^ 2)
        = (Real.exp (-Real.pi * t)) ^ (((n : ℕ) + 1) ^ 2) := by
      rw [← Real.exp_natCast_mul (((n : ℕ) + 1) ^ 2) (-Real.pi * t)]
      congr 1
      push_cast
      ring
    rw [hexp]
  simp only [thetaFour, theta4]
  rw [hsplit, h0, hfinal]
  rfl

/-- The complex square-root prefactor receipt: for `t > 0`,
`1 / (t : ℂ) ^ (1/2 : ℂ) = ((√t)⁻¹ : ℝ)`, through `ofReal_cpow`,
`sqrt_eq_rpow` and the ofReal division algebra. -/
private theorem complex_prefactor {t : ℝ} (ht : 0 < t) :
    1 / (t : ℂ) ^ ((1 : ℂ) / 2) = (((Real.sqrt t)⁻¹ : ℝ) : ℂ) := by
  have hexp : (((1:ℝ)/2 : ℝ) : ℂ) = (1 : ℂ) / 2 := by
    push_cast
    norm_num
  rw [show (1 : ℂ) / 2 = (((1:ℝ)/2 : ℝ) : ℂ) from hexp.symm]
  rw [← Complex.ofReal_cpow ht.le, ← Real.sqrt_eq_rpow]
  rw [← Complex.ofReal_one, ← Complex.ofReal_div, ← one_div]

/-- The alternating lattice term is real:
`cexp (−π·t·z² + iπ·z) = ((−1)^z · exp (−πtz²) : ℝ)`, through the
exponential split `exp_add`, the Gaussian face `ofReal_exp`, and the
character face `exp_intCast_mul` + `exp_pi_mul_I` + `ofReal_zpow`. -/
private theorem cexp_alternating {t : ℝ} (z : ℤ) :
    Complex.exp (-Real.pi * (t : ℂ) * ((z : ℂ)) ^ 2
        + 2 * Real.pi * (Complex.I / 2) * ((z : ℂ)))
      = (((-1 : ℝ) ^ z * Real.exp (-Real.pi * t * ((z : ℝ)) ^ 2)) : ℂ) := by
  have hzc : ((z : ℂ)) = (((z : ℝ)) : ℂ) := (Complex.ofReal_intCast z).symm
  rw [hzc,
    show -Real.pi * (t : ℂ) * (((z : ℝ)) : ℂ) ^ 2
        = (((-Real.pi * t * ((z : ℝ)) ^ 2 : ℝ)) : ℂ) from by
      rw [← Complex.ofReal_neg, ← Complex.ofReal_mul, ← Complex.ofReal_pow,
        ← Complex.ofReal_mul],
    show 2 * Real.pi * (Complex.I / 2) * (((z : ℝ)) : ℂ)
        = ((z : ℂ)) * (Real.pi * Complex.I) from by
      rw [Complex.ofReal_intCast z]
      ring,
    Complex.exp_add, Complex.exp_intCast_mul, Complex.exp_pi_mul_I,
    show (-1 : ℂ) = (((-1 : ℝ)) : ℂ) from by
      rw [Complex.ofReal_neg, Complex.ofReal_one],
    ← Complex.ofReal_zpow, ← Complex.ofReal_exp, ← Complex.ofReal_mul]
  rw [Complex.ofReal_mul, mul_comm]

/-- The half-lattice dual term is real:
`cexp (−π/t · (z − 1/2)²) = ((exp (−π/t · (z − 1/2)²)) : ℝ)`, all
casts pushed through the ofReal algebra. -/
private theorem cexp_halflattice {t : ℝ} (z : ℤ) :
    Complex.exp (-Real.pi / (t : ℂ) * (((z : ℂ)) + Complex.I * (Complex.I / 2)) ^ 2)
      = ((Real.exp (-Real.pi / t * (((z : ℝ)) - 1 / 2) ^ 2)) : ℂ) := by
  have hzc : ((z : ℂ)) = (((z : ℝ)) : ℂ) := (Complex.ofReal_intCast z).symm
  have hII : Complex.I * (Complex.I / 2) = (((-1 / 2 : ℝ)) : ℂ) := by
    rw [← mul_div_assoc, Complex.I_mul_I,
      show (-1 : ℂ) = (((-1 : ℝ)) : ℂ) from by
        rw [Complex.ofReal_neg, Complex.ofReal_one],
      show (2 : ℂ) = ((2 : ℝ) : ℂ) from by norm_num,
      ← Complex.ofReal_div]
  rw [hzc, hII, ← Complex.ofReal_add, ← Complex.ofReal_neg, ← Complex.ofReal_div,
    ← Complex.ofReal_pow, ← Complex.ofReal_mul, ← Complex.ofReal_exp]
  exact congrArg Complex.ofReal (congrArg Real.exp (by ring))

set_option maxHeartbeats 1000000 in
/-- THE HALF-LATTICE POISSON STONE: for every `t > 0`,
`thetaFour t = (√t)⁻¹ * thetaTwo (1/t)`, the modular transform of the
alternating theta. Rides Mathlib's `Complex.tsum_exp_neg_quadratic` at
the character `b = I/2` (its `b = 0` face is R234's thetaT_transform
receipt); the alternating lattice is its own half-shifted dual. This
is the modular engine the Z_1111(2) window (w2) will call on. -/
theorem thetaFour_transform {t : ℝ} (ht : 0 < t) :
    thetaFour t = (Real.sqrt t)⁻¹ * thetaTwo (1 / t) := by
  have hre : 0 < ((t : ℂ)).re := by
    rwa [Complex.ofReal_re]
  have hc := Complex.tsum_exp_neg_quadratic (a := (t : ℂ))
    (b := Complex.I / 2) hre
  have hL : ∑' (n : ℤ), Complex.exp (-Real.pi * (t : ℂ) * ((n : ℂ)) ^ 2
        + 2 * Real.pi * (Complex.I / 2) * ((n : ℂ)))
      = (((∑' (n : ℤ),
          (-1 : ℝ) ^ n * Real.exp (-Real.pi * t * ((n : ℝ)) ^ 2)) : ℝ) : ℂ) := by
    rw [tsum_congr (fun n => cexp_alternating n)]
    simp only [← Complex.ofReal_zpow, ← Complex.ofReal_mul]
    exact (Complex.ofReal_tsum
      (fun n : ℤ => (-1 : ℝ) ^ n * Real.exp (-Real.pi * t * ((n : ℝ)) ^ 2))).symm
  have hR : ∑' (n : ℤ), Complex.exp (-Real.pi / (t : ℂ)
        * (((n : ℂ)) + Complex.I * (Complex.I / 2)) ^ 2)
      = (((∑' (n : ℤ),
          Real.exp (-Real.pi / t * (((n : ℝ)) - 1 / 2) ^ 2)) : ℝ) : ℂ) := by
    rw [tsum_congr (fun n => cexp_halflattice n)]
    exact (Complex.ofReal_tsum
      (fun n : ℤ => Real.exp (-Real.pi / t * (((n : ℝ)) - 1 / 2) ^ 2))).symm
  rw [hL, hR, complex_prefactor ht, ← Complex.ofReal_mul] at hc
  have hcore : (∑' (n : ℤ),
      (-1 : ℝ) ^ n * Real.exp (-Real.pi * t * ((n : ℝ)) ^ 2))
      = (Real.sqrt t)⁻¹ * (∑' (n : ℤ),
          Real.exp (-Real.pi / t * (((n : ℝ)) - 1 / 2) ^ 2)) :=
    Complex.ofReal_inj.mp hc
  rw [thetaFour_eq_tsumInt ht, hcore, thetaTwo_eq_tsumFam]
  congr 1
  exact tsum_congr (fun z => by
    simp only [thetaTwoFam]
    congr 1
    rw [div_eq_inv_mul, one_div]
    ring)

/-! ## Stone iii: the super-exponential death -/

/-- THETAFOUR IS STRICTLY POSITIVE: the transform reads the alternating
theta as a positive prefactor times a positive sum. -/
theorem thetaFour_pos {t : ℝ} (ht : 0 < t) : 0 < thetaFour t := by
  rw [thetaFour_transform ht]
  exact mul_pos (inv_pos.mpr (Real.sqrt_pos.mpr ht))
    (thetaTwo_pos (by rw [one_div]; exact inv_pos.mpr ht))

/-- THE SUPER-EXPONENTIAL DEATH: for `0 < t ≤ 1`,
`thetaFour t ≤ (√t)⁻¹ * 4 * exp (−π/(4t))`, the transform read
through the dual gain. thetaFour dies faster than any power as t → 0;
this is the exact opposite face of the R235 deficit law, and the
engine that pays for window (w1). -/
theorem thetaFour_death {t : ℝ} (ht : 0 < t) (ht1 : t ≤ 1) :
    thetaFour t ≤ (Real.sqrt t)⁻¹ * 4 * Real.exp (-(Real.pi / (4 * t))) := by
  have hinv : (1:ℝ) ≤ 1 / t := by
    rw [le_div_iff₀ ht]
    linarith
  have hdec := thetaTwo_decay hinv
  have hexp : Real.exp (-(Real.pi * (1 / t) / 4))
      = Real.exp (-(Real.pi / (4 * t))) := by
    congr 1
    field_simp
  rw [thetaFour_transform ht]
  calc (Real.sqrt t)⁻¹ * thetaTwo (1 / t)
      ≤ (Real.sqrt t)⁻¹ * (4 * Real.exp (-(Real.pi * (1 / t) / 4))) :=
        mul_le_mul_of_nonneg_left hdec (inv_nonneg.mpr (Real.sqrt_nonneg _))
    _ = (Real.sqrt t)⁻¹ * 4 * Real.exp (-(Real.pi / (4 * t))) := by
        rw [hexp]
        ring

/-! ## Stone iv: window (w1) discharged -/

/-- The exponential kill receipt: `exp(−y) ≤ (2/y)²` for `y > 0`,
from `exp(y/2) ≥ 1 + y/2` squared. -/
private theorem exp_neg_le_inv_sq {y : ℝ} (hy : 0 < y) :
    Real.exp (-y) ≤ (2 / y) ^ 2 := by
  have h1 : 1 + y/2 ≤ Real.exp (y/2) := by
    have h2 := Real.add_one_le_exp (y/2)
    linarith
  have h3 : (y/2) ^ 2 ≤ (Real.exp (y/2)) ^ 2 := by
    have hp := Real.exp_pos (y/2)
    exact sq_le_sq' (by linarith) (by linarith)
  have h4 : (Real.exp (y/2)) ^ 2 = Real.exp y := by
    rw [sq, ← Real.exp_add]
    ring
  have h5 : (y/2) ^ 2 * Real.exp (-y) ≤ 1 := by
    have h6 : (y/2) ^ 2 * Real.exp (-y) ≤ Real.exp y * Real.exp (-y) :=
      mul_le_mul_of_nonneg_right (h3.trans_eq h4) (Real.exp_pos _).le
    rw [← Real.exp_add, add_neg_cancel, Real.exp_zero] at h6
    exact h6
  have hy2 : (0:ℝ) < y * y := mul_pos hy hy
  have h8 : Real.exp (-y) * (y * y) = (y/2) ^ 2 * Real.exp (-y) * 4 := by
    rw [show (y/2)^2 = (y*y)/4 from by ring]
    ring
  have h9 : Real.exp (-y) * (y * y) ≤ 4 := by
    rw [h8]
    linarith [h5]
  have hgoal : (2 / y) ^ 2 = 4 / (y * y) := by ring
  rw [hgoal, le_div_iff₀ hy2]
  exact h9

/-- THE SMALL-T BOUND: for `0 < x ≤ 1`, the 1000 kernel's absolute
value is capped by `2048/9 + 1`: the death `thetaFour ≤ (√x)⁻¹·4·exp
(−π/(4x))` kills the `thetaT^3 ≤ 8·x^(−3/2)` blow-up through the
exponential kill receipt, and the triangle law caps the rest. -/
private theorem kernel1000_small_bound {x : ℝ} (hx0 : 0 < x) (hx1 : x ≤ 1) :
    |x * (gauss1000 x - 1)| ≤ (2048:ℝ)/9 + 1 := by
  -- the thetaT side: blow-up plus (√x)⁻¹ ≥ 1
  have hT := thetaT_blowup hx0 hx1
  have hs : 0 < Real.sqrt x := Real.sqrt_pos.mpr hx0
  have hsinv : (1:ℝ) ≤ (Real.sqrt x)⁻¹ := by
    rw [one_le_inv_iff₀]
    have hle : Real.sqrt x ≤ 1 := by
      have h1 := Real.sqrt_le_sqrt hx1
      rwa [Real.sqrt_one] at h1
    exact ⟨hs, hle⟩
  have hT2 : thetaT x ≤ 2 * (Real.sqrt x)⁻¹ := by linarith
  -- the cube, without pow-monotonicity lemmas
  have hT3 : thetaT x ^ 3 ≤ 8 * ((Real.sqrt x)⁻¹) ^ 3 := by
    have h1 : thetaT x ^ 3 = thetaT x * thetaT x ^ 2 := by ring
    have h2 : thetaT x ^ 2 ≤ (2 * (Real.sqrt x)⁻¹) ^ 2 := by
      have hn : 0 ≤ thetaT x := thetaT_nonneg hx0
      exact sq_le_sq' (by linarith) hT2
    have h3 : (2 * (Real.sqrt x)⁻¹) ^ 2 = 4 * ((Real.sqrt x)⁻¹) ^ 2 := by ring
    rw [h1]
    calc thetaT x * thetaT x ^ 2
        ≤ (2 * (Real.sqrt x)⁻¹) * thetaT x ^ 2 :=
          mul_le_mul_of_nonneg_right hT2 (by positivity)
      _ ≤ (2 * (Real.sqrt x)⁻¹) * (4 * ((Real.sqrt x)⁻¹) ^ 2) :=
          mul_le_mul_of_nonneg_left (h2.trans_eq h3) (by positivity)
      _ = 8 * ((Real.sqrt x)⁻¹) ^ 3 := by ring
  -- the product: gauss1000 ≤ 32 * ((√x)⁻¹)^4 * exp(−π/(4x))
  have hF := thetaFour_death hx0 hx1
  have hg : gauss1000 x
      ≤ 32 * ((Real.sqrt x)⁻¹) ^ 4 * Real.exp (-(Real.pi / (4 * x))) := by
    have hF' : 0 ≤ (Real.sqrt x)⁻¹ * 4 * Real.exp (-(Real.pi / (4 * x))) := by
      positivity
    have hcalc : gauss1000 x
        ≤ (Real.sqrt x)⁻¹ * 4 * Real.exp (-(Real.pi / (4 * x)))
          * (8 * ((Real.sqrt x)⁻¹) ^ 3) := by
      have hnon : 0 ≤ thetaT x ^ 3 := pow_nonneg (thetaT_nonneg hx0) 3
      rw [gauss1000]
      calc thetaFour x * thetaT x ^ 3
          ≤ ((Real.sqrt x)⁻¹ * 4 * Real.exp (-(Real.pi / (4 * x))))
              * thetaT x ^ 3 :=
            mul_le_mul_of_nonneg_right hF hnon
        _ ≤ ((Real.sqrt x)⁻¹ * 4 * Real.exp (-(Real.pi / (4 * x))))
              * (8 * ((Real.sqrt x)⁻¹) ^ 3) :=
            mul_le_mul_of_nonneg_left hT3 hF'
        _ = 8 * ((Real.sqrt x)⁻¹) ^ 3
              * ((Real.sqrt x)⁻¹ * 4 * Real.exp (-(Real.pi / (4 * x)))) := by ring
        _ = (Real.sqrt x)⁻¹ * 4 * Real.exp (-(Real.pi / (4 * x)))
              * (8 * ((Real.sqrt x)⁻¹) ^ 3) := by ring
    exact hcalc.trans_eq (by ring)
  -- the kill: x·gauss1000 ≤ 2048/9
  have hy : 0 < Real.pi / (4 * x) := by
    have h1 : (0:ℝ) < 4 * x := by linarith
    exact div_pos Real.pi_pos h1
  have hkill : Real.exp (-(Real.pi / (4 * x)))
      ≤ (2 / (Real.pi / (4 * x))) ^ 2 := exp_neg_le_inv_sq hy
  have hyshape : (2 / (Real.pi / (4 * x))) ^ 2 = (8 * x / Real.pi) ^ 2 := by
    field_simp
    ring
  rw [hyshape] at hkill
  have hp2 : ((Real.sqrt x)⁻¹) ^ 2 = x ⁻¹ := by
    have h1 : ((Real.sqrt x)⁻¹) ^ 2 = ((Real.sqrt x) ^ 2) ⁻¹ := by
      rw [sq, sq, mul_inv]
    rw [h1, Real.sq_sqrt hx0.le]
  have hp4 : x * ((Real.sqrt x)⁻¹) ^ 4 = x ⁻¹ := by
    have h4 : ((Real.sqrt x)⁻¹) ^ 4 = (((Real.sqrt x)⁻¹) ^ 2) ^ 2 := by
      rw [← pow_mul]
    rw [h4, hp2, sq, ← mul_assoc, mul_inv_cancel₀ hx0.ne', one_mul]
  have hxg : x * gauss1000 x ≤ 2048 * x / (Real.pi * Real.pi) := by
    calc x * gauss1000 x
        ≤ x * (32 * ((Real.sqrt x)⁻¹) ^ 4 * Real.exp (-(Real.pi / (4 * x)))) :=
          mul_le_mul_of_nonneg_left hg hx0.le
      _ = 32 * (x * ((Real.sqrt x)⁻¹) ^ 4) * Real.exp (-(Real.pi / (4 * x))) := by ring
      _ = 32 * x ⁻¹ * Real.exp (-(Real.pi / (4 * x))) := by rw [hp4]
      _ ≤ 32 * x ⁻¹ * (8 * x / Real.pi) ^ 2 :=
          mul_le_mul_of_nonneg_left hkill (by positivity)
      _ = 2048 * x / (Real.pi * Real.pi) := by
        field_simp
        ring
  have hpi : (9:ℝ) ≤ Real.pi * Real.pi := by
    have := Real.pi_gt_three
    nlinarith [this]
  have hfinal : x * gauss1000 x ≤ 2048 / 9 := by
    have h1 : 2048 * x / (Real.pi * Real.pi) ≤ 2048 / 9 := by
      rw [div_le_div_iff₀ (mul_pos Real.pi_pos Real.pi_pos) (by norm_num)]
      have hx9 : 9 * x ≤ 9 := by nlinarith [hx1]
      have hp9 : 9 ≤ Real.pi * Real.pi := hpi
      nlinarith [hx9, hp9]
    exact hxg.trans h1
  -- the triangle cap and the two-sided bound
  have hgnn : 0 ≤ gauss1000 x := by
    rw [gauss1000]
    exact mul_nonneg (thetaFour_pos hx0).le (pow_nonneg (thetaT_nonneg hx0) 3)
  have habs : |x * (gauss1000 x - 1)| ≤ x * gauss1000 x + x := by
    rw [abs_le]
    constructor
    · nlinarith [hgnn]
    · nlinarith [hgnn]
  have hlast : x * gauss1000 x + x ≤ 2048 / 9 + 1 := by
    nlinarith [hfinal, hx1]
  exact habs.trans hlast

/-- THE DIFFERENCE SPINE'S SMALL-T BOUND: for `0 < x ≤ 1`, the
difference kernel's absolute value is capped by `2048/9 + 4` (the
1000 side through `kernel1000_small_bound`, the 1110 side through
the R236 receipts: `thetaFour^3 ≤ 1` and `x·thetaT ≤ x + √x`). -/
private theorem kernelDiff_small_bound {x : ℝ} (hx0 : 0 < x) (hx1 : x ≤ 1) :
    |x * (gauss1000 x - gauss1110 x)| ≤ (2048:ℝ)/9 + 4 := by
  have hF1 : thetaFour x ≤ 1 := by
    have h := abs_thetaFour_le_one hx0
    rw [abs_le] at h
    exact h.2
  have hF3 : thetaFour x ^ 3 ≤ 1 := by
    have habs := abs_thetaFour_le_one hx0
    rw [abs_le] at habs
    have hnn : (0:ℝ) ≤ thetaFour x ^ 2 := sq_nonneg _
    have hs2 : thetaFour x ^ 2 ≤ 1 := by nlinarith [habs.1, habs.2]
    have hc : thetaFour x ^ 3 = thetaFour x * thetaFour x ^ 2 := by ring
    rw [hc]
    calc thetaFour x * thetaFour x ^ 2
        ≤ 1 * thetaFour x ^ 2 := mul_le_mul_of_nonneg_right habs.2 hnn
      _ ≤ 1 * 1 := mul_le_mul_of_nonneg_left hs2 (by norm_num)
      _ = 1 := by ring
  have hT := thetaT_blowup hx0 hx1
  have hs : 0 < Real.sqrt x := Real.sqrt_pos.mpr hx0
  have hkey : x * (Real.sqrt x)⁻¹ = Real.sqrt x := by
    nth_rewrite 1 [← Real.mul_self_sqrt hx0.le]
    rw [mul_assoc, mul_inv_cancel₀ hs.ne', mul_one]
  have h1110nn : 0 ≤ gauss1110 x := by
    rw [gauss1110]
    exact mul_nonneg (pow_nonneg (thetaFour_pos hx0).le 3) (thetaT_nonneg hx0)
  have hxg1110 : x * gauss1110 x ≤ 2 := by
    have hc : gauss1110 x ≤ thetaT x := by
      rw [gauss1110]
      calc thetaFour x ^ 3 * thetaT x ≤ 1 * thetaT x :=
            mul_le_mul_of_nonneg_right hF3 (thetaT_nonneg hx0)
        _ = thetaT x := one_mul _
    have h1 : x * gauss1110 x ≤ x * thetaT x :=
      mul_le_mul_of_nonneg_left hc hx0.le
    have h2 : x * thetaT x ≤ x + Real.sqrt x := by
      have h3 : x * thetaT x ≤ x * (1 + (Real.sqrt x)⁻¹) :=
        mul_le_mul_of_nonneg_left hT hx0.le
      have h4 : x * (1 + (Real.sqrt x)⁻¹) = x + Real.sqrt x := by
        rw [mul_add, mul_one, hkey]
      exact h3.trans_eq h4
    have h5 : Real.sqrt x ≤ 1 := by
      have h6 := Real.sqrt_le_sqrt hx1
      rwa [Real.sqrt_one] at h6
    nlinarith
  have habs : |x * (gauss1000 x - gauss1110 x)|
      ≤ |x * (gauss1000 x - 1)| + |x * (1 - gauss1110 x)| := by
    have hsplit : x * (gauss1000 x - gauss1110 x)
        = x * (gauss1000 x - 1) + x * (1 - gauss1110 x) := by ring
    rw [hsplit]
    exact abs_add_le _ _
  have h2 : |x * (1 - gauss1110 x)| ≤ 3 := by
    rw [abs_le]
    constructor
    · nlinarith [h1110nn, hxg1110, hx1]
    · nlinarith [h1110nn, hxg1110, hx1]
  have h1000 := kernel1000_small_bound hx0 hx1
  have hlast : |x * (gauss1000 x - 1)| + |x * (1 - gauss1110 x)|
      ≤ (2048:ℝ)/9 + 4 := by
    linarith [h1000, h2]
  exact habs.trans hlast

/-! ### The measurability mirrors (R236's private receipts, re-proved
here since they are file-local; the value-split pattern is identical) -/

private noncomputable def gaussTerm' (t : ℝ) (n : ℕ) : ℝ :=
  Real.exp (-Real.pi * t * ((n : ℝ)) ^ 2)

/-- The positive tail is a measurable object (the ℕ-tsum of
measurable exponentials). -/
private theorem tailG'_measurable :
    Measurable (fun (t : ℝ) => ∑' (n : ℕ), gaussTerm' t (n + 1)) := by
  have h : ∀ (n : ℕ), Measurable (fun (t : ℝ) => gaussTerm' t (n + 1)) := by
    intro n
    simp only [gaussTerm']
    fun_prop
  exact Measurable.tsum (f := fun (n : ℕ) (t : ℝ) => gaussTerm' t (n + 1)) h

/-- The t-arm thetaFour is measurable (the alternating tsum of powers
of the nome; the R235/R236 receipt, mirrored). -/
private theorem thetaFour_meas : Measurable (thetaFour) := by
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

/-- The value split on the time axis (the `thetaT_split` receipt,
mirrored: the even twin split plus the ℕ+ face). -/
private theorem thetaT_splitG' {t : ℝ} (ht : 0 < t) :
    thetaT t = 1 + 2 * ∑' (n : ℕ), gaussTerm' t (n + 1) := by
  have hsumm : Summable (gaussFam' t) := gaussFam'_summable ht
  have heven : Function.Even (gaussFam' t) := by
    intro z
    simp only [gaussFam']
    congr 1
    push_cast
    ring
  have h0 : gaussFam' t 0 = 1 := by
    simp only [gaussFam']
    norm_num
  have hc : ∀ m : ℕ, gaussFam' t ((m : ℕ) : ℤ) = gaussTerm' t m := by
    intro m
    simp only [gaussFam', gaussTerm']
    push_cast
    rfl
  have hsplit := tsum_int_eq_zero_add_two_mul_tsum_pnat heven hsumm
  rw [two_nsmul, ← two_mul] at hsplit
  have hpnat := tsum_pnat_eq_tsum_succ
    (f := fun (m : ℕ) => gaussFam' t ((m : ℕ) : ℤ))
  have hfinal : ∑' (p : ℕ+), gaussFam' t ((p : ℕ) : ℤ)
      = ∑' (n : ℕ), gaussTerm' t (n + 1) := by
    rw [hpnat]
    exact tsum_congr (fun n => by rw [hc (n + 1)])
  show ∑' (z : ℤ), gaussFam' t z = 1 + 2 * ∑' (n : ℕ), gaussTerm' t (n + 1)
  rw [hsplit, h0, hfinal]

/-- The 1000 kernel is a.e. strongly measurable on any measurable set
lying in the positive time axis (the value-split pattern). -/
private theorem kernel1000_aemeas' (s : Set ℝ) (ms : MeasurableSet s)
    (hs : ∀ t ∈ s, (0:ℝ) < t) :
    AEStronglyMeasurable (fun t => t * (gauss1000 t - 1))
      (MeasureTheory.volume.restrict s) := by
  have hmeas : Measurable (fun t => t *
      (thetaFour t * (1 + 2 * ∑' (n : ℕ), gaussTerm' t (n + 1)) ^ 3 - 1)) := by
    refine measurable_id.mul ?_
    exact (thetaFour_meas.mul
      ((measurable_const.add (measurable_const.mul tailG'_measurable)).pow_const 3)).sub
      measurable_const
  have hptwise : ∀ t ∈ s,
      (t : ℝ) *
        (thetaFour t * (1 + 2 * ∑' (n : ℕ), gaussTerm' t (n + 1)) ^ 3 - 1)
        = t * (gauss1000 t - 1) := by
    intro t ht'
    simp only [gauss1000]
    rw [thetaT_splitG' (hs t ht')]
  exact hmeas.aestronglyMeasurable.congr
    (Filter.mem_of_superset (self_mem_ae_restrict ms) hptwise)

/-- The difference kernel's a.e. strong measurability, same pattern. -/
private theorem kernelDiff_aemeas' (s : Set ℝ) (ms : MeasurableSet s)
    (hs : ∀ t ∈ s, (0:ℝ) < t) :
    AEStronglyMeasurable (fun t => t * (gauss1000 t - gauss1110 t))
      (MeasureTheory.volume.restrict s) := by
  have htail : Measurable
      (fun (t : ℝ) => 1 + 2 * ∑' (n : ℕ), gaussTerm' t (n + 1)) :=
    measurable_const.add (measurable_const.mul tailG'_measurable)
  have hmeas : Measurable (fun t => t *
      (thetaFour t * (1 + 2 * ∑' (n : ℕ), gaussTerm' t (n + 1)) ^ 3
        - thetaFour t ^ 3 * (1 + 2 * ∑' (n : ℕ), gaussTerm' t (n + 1)))) := by
    refine measurable_id.mul ?_
    exact (thetaFour_meas.mul (htail.pow_const 3)).sub
      ((thetaFour_meas.pow_const 3).mul htail)
  have hptwise : ∀ t ∈ s,
      (t : ℝ) *
        (thetaFour t * (1 + 2 * ∑' (n : ℕ), gaussTerm' t (n + 1)) ^ 3
          - thetaFour t ^ 3 * (1 + 2 * ∑' (n : ℕ), gaussTerm' t (n + 1)))
        = t * (gauss1000 t - gauss1110 t) := by
    intro t ht'
    simp only [gauss1000, gauss1110]
    rw [thetaT_splitG' (hs t ht')]
  exact hmeas.aestronglyMeasurable.congr
    (Filter.mem_of_superset (self_mem_ae_restrict ms) hptwise)

/-! ### The integrability stones -/

/-- THE SMALL-T HALF OF THE 1000 KERNEL (window w1, DISCHARGED): the
kernel `t ↦ t·(gauss1000 t − 1)` is integrable on `(0, 1]`. The
super-exponential death of thetaFour (the half-lattice Poisson stone)
kills thetaT^3's blow-up: a bounded kernel on a finite volume. -/
theorem kernel1000_integrable_small :
    IntegrableOn (fun t => t * (gauss1000 t - 1)) (Ioc (0:ℝ) 1)
      MeasureTheory.volume := by
  have hvol : MeasureTheory.volume (Ioc (0:ℝ) 1) < ⊤ := by
    rw [volume_Ioc]
    simp
  have hbnd : ∀ x ∈ Ioc (0:ℝ) 1, ‖x * (gauss1000 x - 1)‖ ≤ (2048:ℝ)/9 + 1 := by
    intro x hx
    have hx0 : (0:ℝ) < x := (Set.mem_Ioc.mp hx).1
    have hx1 : x ≤ 1 := (Set.mem_Ioc.mp hx).2
    rw [Real.norm_eq_abs]
    exact kernel1000_small_bound hx0 hx1
  exact IntegrableOn.of_bound hvol
    (kernel1000_aemeas' (Ioc (0:ℝ) 1) measurableSet_Ioc
      (fun t ht => (Set.mem_Ioc.mp ht).1))
    ((2048:ℝ)/9 + 1)
    (Filter.mem_of_superset (self_mem_ae_restrict measurableSet_Ioc) hbnd)

/-- THE SMALL-T HALF OF THE DIFFERENCE SPINE: the kernel
`t ↦ t·(gauss1000 t − gauss1110 t)` is integrable on `(0, 1]`. -/
theorem kernelDiff_integrable_small :
    IntegrableOn (fun t => t * (gauss1000 t - gauss1110 t)) (Ioc (0:ℝ) 1)
      MeasureTheory.volume := by
  have hvol : MeasureTheory.volume (Ioc (0:ℝ) 1) < ⊤ := by
    rw [volume_Ioc]
    simp
  have hbnd : ∀ x ∈ Ioc (0:ℝ) 1,
      ‖x * (gauss1000 x - gauss1110 x)‖ ≤ (2048:ℝ)/9 + 4 := by
    intro x hx
    have hx0 : (0:ℝ) < x := (Set.mem_Ioc.mp hx).1
    have hx1 : x ≤ 1 := (Set.mem_Ioc.mp hx).2
    rw [Real.norm_eq_abs]
    exact kernelDiff_small_bound hx0 hx1
  exact IntegrableOn.of_bound hvol
    (kernelDiff_aemeas' (Ioc (0:ℝ) 1) measurableSet_Ioc
      (fun t ht => (Set.mem_Ioc.mp ht).1))
    ((2048:ℝ)/9 + 4)
    (Filter.mem_of_superset (self_mem_ae_restrict measurableSet_Ioc) hbnd)

/-- THE TWO HALVES OF THE 1000 KERNEL TOGETHER: the small half paid
this window, the large half paid R236. -/
theorem kernel1000_integrable_union :
    IntegrableOn (fun t => t * (gauss1000 t - 1)) (Ioc (0:ℝ) 1 ∪ Ioi (1:ℝ))
      MeasureTheory.volume := by
  rw [integrableOn_union]
  exact ⟨kernel1000_integrable_small, kernel1000_integrable_large⟩

/-- THE FULL 1000 KERNEL'S INTEGRABILITY (window w1, CLOSED): the
s = 2 Mellin kernel of the 1000 arm, `t ↦ t·(gauss1000 t − 1)`, is
integrable on the whole half-line `(0, ∞)` -- the 1000 arm's honest
object ZAdic1000 EXISTS, unconditionally. Its closed-form VALUE
`pi*G − (pi²/24)·log 2` remains the named window (w2), not claimed
here. -/
theorem kernel1000_integrable_full :
    IntegrableOn (fun t => t * (gauss1000 t - 1)) (Ioi (0:ℝ)) volume := by
  rw [← Ioc_union_Ioi_eq_Ioi (by norm_num : (0:ℝ) ≤ 1)]
  exact kernel1000_integrable_union

/-- THE TWO HALVES OF THE DIFFERENCE SPINE TOGETHER. -/
theorem kernelDiff_integrable_union :
    IntegrableOn (fun t => t * (gauss1000 t - gauss1110 t)) (Ioc (0:ℝ) 1 ∪ Ioi (1:ℝ))
      MeasureTheory.volume := by
  rw [integrableOn_union]
  exact ⟨kernelDiff_integrable_small, kernelDiff_integrable_large⟩

/-- THE FULL DIFFERENCE SPINE'S INTEGRABILITY: the antisymmetric kernel
`t ↦ t·(gauss1000 t − gauss1110 t)` (the factored spine behind the
`Z[i]` difference `Z_1000(2) − Z_1110(2) = 2·pi·G`, the ring identity
of `gauss1000_sub_gauss1110_eq`) is integrable on the whole
half-line. The VALUE `2·pi·G` remains the named window (w2), not
claimed here. -/
theorem kernelDiff_integrable_full :
    IntegrableOn (fun t => t * (gauss1000 t - gauss1110 t)) (Ioi (0:ℝ)) volume := by
  rw [← Ioc_union_Ioi_eq_Ioi (by norm_num : (0:ℝ) ≤ 1)]
  exact kernelDiff_integrable_union

end YangMills.DualBook

/-!
  REMAINDERS, honest and named (pre-registered for R238+):
  (w2) the VALUES: Z_1000(2) = pi*G - (pi^2/24)*log 2,
       Z_1110(2) = -pi*G - (pi^2/24)*log 2,
       Z_1111(2) = -(2/3)*pi^2*log 2 (the modular engine for this one
       is now banked: thetaFour_transform above, with thetaTwo the
       dual face).
  (w3) the Mellin scaling cascade: lift the latch law
       Theta_1100(q) = Theta_1111(q^2) and the D1' sum law
       Theta_1000(q) + Theta_1110(q) = 2*Theta_1111(q^4) to the s = 2
       Mellin integrals via t -> c*t, reducing the four Epstein debts
       to two analytic evaluations.
  Bench frozen at 100.0. Scope: THIS ARITHMETIC only.
-/
