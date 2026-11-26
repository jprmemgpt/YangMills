import Mathlib.Analysis.SumIntegralComparisons
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Algebra.Order.GroupWithZero.Basic
import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Analysis.Real.Pi.Bounds
import YangMills.DualBook.JacobiAnchorsL1b

namespace YangMills.DualBook

open MeasureTheory Real Set

/-! ## The alternating core -/

/-- The alternating core of the theta-4 constant:
`altCore q n = (−1)^(n+1) * q^((n+1)²)`, the n-th summand of the house
`theta4` tail. Summable on the book's domain by the theta-4 core
summability (`theta4Core_summable`, the sign carrying norm 1). -/
private noncomputable def altCore (q : ℝ) (n : ℕ) : ℝ :=
  (-1 : ℝ) ^ (n + 1) * q ^ ((n + 1) ^ 2)

/-- Summability of the alternating core on `0 < q < 1` (the house
receipt, nothing re-proved). -/
private theorem altCore_summable {q : ℝ} (hq0 : 0 < q) (hq1 : q < 1) :
    Summable (altCore q) :=
  theta4Core_summable hq0 hq1

/-- Odd-stride summability: the family k -> q^((2k+1)²), dominated by the
geometric family (its exponent (2k+1)² >= k). -/
private theorem oddStride_summable {q : ℝ} (hq0 : 0 < q) (hq1 : q < 1) :
    Summable fun k : ℕ => q ^ ((2 * k + 1) ^ 2) := by
  have hgeo : Summable fun k : ℕ => q ^ k :=
    summable_geometric_of_lt_one hq0.le hq1
  refine hgeo.of_norm_bounded fun k => ?_
  rw [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg hq0.le _)]
  exact pow_le_pow_of_le_one hq0.le hq1.le
    (calc k ≤ 2 * k + 1 := by omega
      _ ≤ (2 * k + 1) ^ 2 := by rw [pow_two]; exact Nat.le_mul_self _)

/-- Even-stride summability: the family k -> q^((2k+2)^2), dominated the
same way (its exponent (2k+2)^2 >= k). -/
private theorem evenStride_summable {q : ℝ} (hq0 : 0 < q) (hq1 : q < 1) :
    Summable fun k : ℕ => q ^ ((2 * k + 2) ^ 2) := by
  have hgeo : Summable fun k : ℕ => q ^ k :=
    summable_geometric_of_lt_one hq0.le hq1
  refine hgeo.of_norm_bounded fun k => ?_
  rw [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg hq0.le _)]
  exact pow_le_pow_of_le_one hq0.le hq1.le
    (calc k ≤ 2 * k + 2 := by omega
      _ ≤ (2 * k + 2) ^ 2 := by rw [pow_two]; exact Nat.le_mul_self _)

/-- The pair family u k = q^((2k+1)^2) - q^((2k+2)^2) is summable. -/
private theorem pair_summable {q : ℝ} (hq0 : 0 < q) (hq1 : q < 1) :
    Summable fun k : ℕ => q ^ ((2 * k + 1) ^ 2) - q ^ ((2 * k + 2) ^ 2) :=
  (oddStride_summable hq0 hq1).sub (evenStride_summable hq0 hq1)

/-- Exponent reversal for the nome: on `0 < q < 1` bigger exponent means
smaller power (Mathlib's `pow_le_pow_of_le_one`, pinned once). -/
private theorem powExp_le {q : ℝ} (hq0 : 0 < q) (hq1 : q < 1) {x y : ℕ}
    (h : x ≤ y) : q ^ y ≤ q ^ x :=
  pow_le_pow_of_le_one hq0.le hq1.le h

/-- Nonnegativity of the pair: `q^((2k+1)^2) >= q^((2k+2)^2)` on the
book's domain, because the odd square is the smaller exponent. -/
private theorem pair_nonneg {q : ℝ} (hq0 : 0 < q) (hq1 : q < 1) (k : ℕ) :
    0 ≤ q ^ ((2 * k + 1) ^ 2) - q ^ ((2 * k + 2) ^ 2) := by
  have hle12 : 2 * k + 1 ≤ 2 * k + 2 := by omega
  have hxy : (2 * k + 1) ^ 2 ≤ (2 * k + 2) ^ 2 := by
    rw [pow_two, pow_two]
    exact Nat.mul_le_mul hle12 hle12
  have h2 : q ^ ((2 * k + 2) ^ 2) ≤ q ^ ((2 * k + 1) ^ 2) :=
    powExp_le hq0 hq1 hxy
  linarith

/-- The core at an even index: `altCore q (2k) = -q^((2k+1)²)` — the sign
at 2k+1 is −1 (odd exponent of −1). -/
private theorem altCore_even_apply (q : ℝ) (k : ℕ) :
    altCore q (2 * k) = -(q ^ ((2 * k + 1) ^ 2)) := by
  simp only [altCore]
  have hsign : (-1 : ℝ) ^ (2 * k + 1) = -1 := by
    rw [pow_add, pow_mul]
    norm_num
  rw [hsign]
  ring

/-- The core at an odd index: `altCore q (2k+1) = q^((2k+2)²)` — the sign
at 2k+2 is +1 (even exponent of −1). -/
private theorem altCore_odd_apply (q : ℝ) (k : ℕ) :
    altCore q (2 * k + 1) = q ^ ((2 * k + 2) ^ 2) := by
  simp only [altCore]
  have hsign : (-1 : ℝ) ^ (2 * k + 1 + 1) = 1 := by
    have h2 : 2 * k + 1 + 1 = 2 * (k + 1) := by ring
    rw [h2, pow_mul]
    norm_num
  rw [hsign]
  ring

/-- THE PAIRING: on the book's domain, the theta-4 constant is
`theta4 q = 1 - 2 * Σ' (q^((2k+1)^2) - q^((2k+2)^2))` — the alternating
core split by the parity of the index: the even indices carry the minus
(the odd squares), the odd indices carry the plus (the even squares),
so the core total is minus the pair total, and the house constant is
1 minus twice it. -/
theorem theta4_pairing_eq {q : ℝ} (hq0 : 0 < q) (hq1 : q < 1) :
    theta4 q = 1 - 2 * ∑' k : ℕ,
      (q ^ ((2 * k + 1) ^ 2) - q ^ ((2 * k + 2) ^ 2)) := by
  have hcore := altCore_summable hq0 hq1
  have hOddSq := oddStride_summable hq0 hq1
  have hEvenSq := evenStride_summable hq0 hq1
  -- summability of the even and odd index strands
  have hEvS : Summable fun k : ℕ => altCore q (2 * k) :=
    hOddSq.neg.congr (fun k => (altCore_even_apply q k).symm)
  have hOdS : Summable fun k : ℕ => altCore q (2 * k + 1) :=
    hEvenSq.congr (fun k => (altCore_odd_apply q k).symm)
  -- the parity split of the core (Mathlib's even_add_odd)
  have hEO := HasSum.even_add_odd hEvS.hasSum hOdS.hasSum
  -- value of the even strand: minus the odd-square stride
  have hE1 : ∑' k : ℕ, altCore q (2 * k)
      = -(∑' k : ℕ, q ^ ((2 * k + 1) ^ 2)) := by
    rw [tsum_congr (altCore_even_apply q), tsum_neg]
  -- value of the odd strand: the even-square stride
  have hE2 : ∑' k : ℕ, altCore q (2 * k + 1)
      = ∑' k : ℕ, q ^ ((2 * k + 2) ^ 2) :=
    tsum_congr (altCore_odd_apply q)
  -- the pair total by subtraction of the two strides
  have hpair : ∑' k : ℕ, (q ^ ((2 * k + 1) ^ 2) - q ^ ((2 * k + 2) ^ 2))
      = (∑' k : ℕ, q ^ ((2 * k + 1) ^ 2)) - (∑' k : ℕ, q ^ ((2 * k + 2) ^ 2)) :=
    (hOddSq.hasSum.sub hEvenSq.hasSum).tsum_eq
  -- assemble: theta4 = 1 + 2 * (core) = 1 - 2 * (pair total)
  unfold theta4
  have hAC : ∑' n : ℕ, (-1 : ℝ) ^ (n + 1) * q ^ ((n + 1) ^ 2)
      = ∑' n : ℕ, altCore q n := rfl
  rw [hAC, hEO.tsum_eq, hE1, hE2, hpair]
  ring

/-- THE TELESCOPE BOUND: the pair total is at most q, by domination over
the telescoping family `q^((2k+1)²) - q^((2k+3)²)` whose total is
exactly q (the first term, the rest collapsing pairwise). -/
private theorem pair_tsum_le {q : ℝ} (hq0 : 0 < q) (hq1 : q < 1) :
    ∑' k : ℕ, (q ^ ((2 * k + 1) ^ 2) - q ^ ((2 * k + 2) ^ 2)) ≤ q := by
  have hOdd := oddStride_summable hq0 hq1
  -- the (2k+3)-stride is summable (same geometric domination)
  have hSg : Summable fun k : ℕ => q ^ ((2 * k + 3) ^ 2) := by
    have hgeo : Summable fun k : ℕ => q ^ k :=
      summable_geometric_of_lt_one hq0.le hq1
    refine hgeo.of_norm_bounded fun k => ?_
    rw [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg hq0.le _)]
    exact pow_le_pow_of_le_one hq0.le hq1.le
      (calc k ≤ 2 * k + 3 := by omega
        _ ≤ (2 * k + 3) ^ 2 := by rw [pow_two]; exact Nat.le_mul_self _)
  -- the two shapes of the shifted odd stride
  have hshift : ∑' k : ℕ, q ^ ((2 * (k + 1) + 1) ^ 2)
      = ∑' k : ℕ, q ^ ((2 * k + 3) ^ 2) :=
    tsum_congr fun k => by rw [(by omega : 2 * (k + 1) + 1 = 2 * k + 3)]
  have h42 : ∑' k : ℕ, q ^ ((2 * k + 3) ^ 2)
      = ∑' k : ℕ, q ^ ((2 * (k + 1) + 1) ^ 2) :=
    (hshift.symm)
  -- the value equation: the odd stride is q plus the shifted odd stride
  have hval : ∑' k : ℕ, q ^ ((2 * k + 1) ^ 2)
      = q + ∑' k : ℕ, q ^ ((2 * (k + 1) + 1) ^ 2) := by
    have h := hOdd.sum_add_tsum_nat_add 1
    simp only [Finset.range_one, Finset.sum_singleton] at h
    norm_num at h
    exact h.symm
  -- the telescoping family's total is exactly q
  have htelescope : ∑' k : ℕ, (q ^ ((2 * k + 1) ^ 2) - q ^ ((2 * k + 3) ^ 2))
      = q := by
    have hAB2 := (hOdd.hasSum.sub hSg.hasSum).tsum_eq
    rw [hAB2, hval, hshift]
    ring
  -- pointwise domination of the pair family by the telescope family
  have hle : ∀ k : ℕ, (q ^ ((2 * k + 1) ^ 2) - q ^ ((2 * k + 2) ^ 2))
      ≤ q ^ ((2 * k + 1) ^ 2) - q ^ ((2 * k + 3) ^ 2) := by
    intro k
    have hle23 : 2 * k + 2 ≤ 2 * k + 3 := by omega
    have hxy : (2 * k + 2) ^ 2 ≤ (2 * k + 3) ^ 2 := by
      rw [pow_two, pow_two]
      exact Nat.mul_le_mul hle23 hle23
    have h2 : q ^ ((2 * k + 3) ^ 2) ≤ q ^ ((2 * k + 2) ^ 2) :=
      powExp_le hq0 hq1 hxy
    exact sub_le_sub_left h2 _
  -- total: the pair sum is at most the telescope sum, which is exactly q
  have hW : Summable fun k : ℕ =>
      q ^ ((2 * k + 1) ^ 2) - q ^ ((2 * k + 3) ^ 2) :=
    (hOdd.hasSum.sub hSg.hasSum).summable
  exact ((pair_summable hq0 hq1).tsum_le_tsum hle hW).trans htelescope.le

/-- THE UPPER SANDWICH LINE: theta4 q <= 1 on the book's domain, because
the pair family is nonnegative and theta4 q = 1 - 2 * (its total). -/
theorem theta4_le_one {q : ℝ} (hq0 : 0 < q) (hq1 : q < 1) :
    theta4 q ≤ 1 := by
  rw [theta4_pairing_eq hq0 hq1]
  have hnn : 0 ≤ ∑' k : ℕ, (q ^ ((2 * k + 1) ^ 2) - q ^ ((2 * k + 2) ^ 2)) :=
    tsum_nonneg fun k => pair_nonneg hq0 hq1 k
  linarith

/-- THE LOWER SANDWICH LINE: 1 - 2 * q <= theta4 q on the book's domain,
the sharp elementary deficit bound: the pair total is at most q. -/
theorem theta4_ge_one_sub {q : ℝ} (hq0 : 0 < q) (hq1 : q < 1) :
    1 - 2 * q ≤ theta4 q := by
  rw [theta4_pairing_eq hq0 hq1]
  have h := pair_tsum_le hq0 hq1
  linarith

/-- THE DEFICIT LINE: 1 - theta4 q <= 2 * q on the book's domain — the
one-sided deficit form of the lower sandwich line. -/
theorem theta4_deficit {q : ℝ} (hq0 : 0 < q) (hq1 : q < 1) :
    1 - theta4 q ≤ 2 * q := by
  rw [theta4_pairing_eq hq0 hq1]
  have h := pair_tsum_le hq0 hq1
  linarith

/-- THE SANDWICH, ABSOLUTE FORM: |theta4 q| <= 1 on the book's domain. -/
theorem abs_theta4_le_one {q : ℝ} (hq0 : 0 < q) (hq1 : q < 1) :
    |theta4 q| ≤ 1 := by
  have h1 := theta4_le_one hq0 hq1
  have h2 := theta4_ge_one_sub hq0 hq1
  rw [abs_le]
  constructor <;> linarith

/-! ## The parity lemma (the character's calendar) -/

/-- THE PARITY LEMMA: n^2 = n (mod 2). The alternating character cannot
distinguish a lattice point from its square: exactly the stone the
character reindex of the 1111 arm needs. -/
theorem parity_sq (n : ℕ) : n ^ 2 % 2 = n % 2 := by
  rcases Nat.mod_two_eq_zero_or_one n with h | h
  · have hn : n = 2 * (n / 2) := by omega
    have hdvd : (2:ℕ) ∣ n * n := by
      refine ⟨2 * (n / 2) * (n / 2), ?_⟩
      conv_lhs => rw [hn]
      ring
    rw [pow_two, Nat.mod_eq_zero_of_dvd hdvd]
    omega
  · have hs : n ^ 2 = 1 + 2 * (2 * (n / 2) * (n / 2) + 2 * (n / 2)) := by
      conv_lhs => rw [show n = 2 * (n / 2) + 1 by omega]
      ring
    rw [hs, Nat.add_mul_mod_self_left]
    omega

/-! ## The t-arm: the 2-adic theta thetaFour -/

/-- THE 2-ADIC THETA (dimension one): the book's theta-4 constant read on
the time axis, `thetaFour t = theta4 (exp (-pi * t))`. This is the object
the 1111 arm's theta constant is the fourth power of; for `t > 0` the nome
`exp (-pi * t)` lies in the book's domain `0 < q < 1`, so the whole
q-sandwich transfers verbatim. -/
noncomputable def thetaFour (t : ℝ) : ℝ :=
  theta4 (Real.exp (-Real.pi * t))

/-- The nome of the t-arm lies in the book's domain for every `t > 0`:
`0 < exp (-pi * t) < 1`. -/
private theorem qexp_pos_lt_one {t : ℝ} (ht : 0 < t) :
    0 < Real.exp (-Real.pi * t) ∧ Real.exp (-Real.pi * t) < 1 := by
  constructor
  · exact Real.exp_pos _
  · have hpt : 0 < Real.pi * t := mul_pos Real.pi_pos ht
    have he := Real.exp_lt_exp.mpr (show -Real.pi * t < 0 by linarith)
    simpa using he

/-- THE PAIRING ON THE T-AXIS: the pairing identity read on the time arm,
with the nome `exp (-pi * t)`. -/
theorem thetaFour_pairing {t : ℝ} (ht : 0 < t) :
    thetaFour t = 1 - 2 * ∑' k : ℕ,
      (Real.exp (-Real.pi * t) ^ ((2 * k + 1) ^ 2)
        - Real.exp (-Real.pi * t) ^ ((2 * k + 2) ^ 2)) := by
  obtain ⟨hq0, hq1⟩ := qexp_pos_lt_one ht
  exact theta4_pairing_eq hq0 hq1

/-- THE T-ARM ABSOLUTE BOUND: |thetaFour t| <= 1 for t > 0. -/
theorem abs_thetaFour_le_one {t : ℝ} (ht : 0 < t) :
    |thetaFour t| ≤ 1 := by
  obtain ⟨hq0, hq1⟩ := qexp_pos_lt_one ht
  exact abs_theta4_le_one hq0 hq1

/-- THE T-ARM BOUNDS: for `t > 0`, `thetaFour t <= 1` and
`1 - thetaFour t <= 2 * exp (-pi * t)` — the sandwich and the deficit
law, with the deficit exponentially small in t. -/
theorem thetaFour_bounds {t : ℝ} (ht : 0 < t) :
    thetaFour t ≤ 1 ∧ 1 - thetaFour t ≤ 2 * Real.exp (-Real.pi * t) := by
  obtain ⟨hq0, hq1⟩ := qexp_pos_lt_one ht
  exact ⟨theta4_le_one hq0 hq1, theta4_deficit hq0 hq1⟩

/-- THE POWER BOUND: for t > 0, `thetaFour t ^ 4 <= 1` and
`1 - thetaFour t ^ 4 <= 8 * exp (-pi*t)`. The fourth power of a number in
[-1, 1] whose deficit is at most 2q again lies below 1, with deficit at
most 4 times the theta's own deficit. -/
theorem thetaFour_pow_bounds {t : ℝ} (ht : 0 < t) :
    thetaFour t ^ 4 ≤ 1 ∧ 1 - thetaFour t ^ 4 ≤ 8 * Real.exp (-Real.pi * t) := by
  have ⟨hθ1, hdef⟩ := thetaFour_bounds ht
  have habspow : |thetaFour t| ≤ 1 := abs_thetaFour_le_one ht
  have hθn : -1 ≤ thetaFour t := by
    have := abs_le.mp habspow
    linarith
  have hθp : thetaFour t ^ 2 ≤ 1 := by
    have habs2 : |thetaFour t| * |thetaFour t| ≤ 1 * 1 :=
      mul_le_mul habspow habspow (abs_nonneg _) (zero_le_one)
    calc thetaFour t ^ 2 = |thetaFour t| ^ 2 := (sq_abs (thetaFour t)).symm
      _ = |thetaFour t| * |thetaFour t| := pow_two _
      _ ≤ 1 * 1 := habs2
      _ = 1 := one_mul _
  have h3le : thetaFour t ^ 3 ≤ 1 := by
    have hrw3 : thetaFour t ^ 3 = thetaFour t * thetaFour t ^ 2 := by ring
    rw [hrw3]
    have hc := mul_le_mul hθ1 hθp (sq_nonneg (thetaFour t)) zero_le_one
    rw [one_mul] at hc
    exact hc
  have h3ge : -1 * thetaFour t ^ 2 ≤ thetaFour t ^ 3 := by
    have hrw3 : thetaFour t ^ 3 = thetaFour t * thetaFour t ^ 2 := by ring
    rw [hrw3]
    exact mul_le_mul_of_nonneg_right hθn (sq_nonneg (thetaFour t))
  have h4 : thetaFour t ^ 4 ≤ 1 := by
    have hrw : thetaFour t ^ 4 = thetaFour t ^ 2 * thetaFour t ^ 2 := by ring
    rw [hrw]
    have hc := mul_le_mul hθp hθp (sq_nonneg (thetaFour t)) zero_le_one
    rw [one_mul] at hc
    exact hc
  refine ⟨h4, ?_⟩
  -- 1 - y^4 = (1-y)(1+y+y^2+y^3), the four-term factorization
  have hfact : 1 - thetaFour t ^ 4
      = (1 - thetaFour t) * (1 + thetaFour t + thetaFour t ^ 2 + thetaFour t ^ 3) := by
    ring
  have hinnerpos : 0 ≤ 1 + thetaFour t + thetaFour t ^ 2 + thetaFour t ^ 3 := by
    have h1 : 0 ≤ 1 + thetaFour t := by linarith
    have h2 : 0 ≤ thetaFour t ^ 2 := sq_nonneg _
    linarith
  have hinnerle : 1 + thetaFour t + thetaFour t ^ 2 + thetaFour t ^ 3 ≤ 4 := by
    linarith
  rw [hfact]
  calc (1 - thetaFour t) * (1 + thetaFour t + thetaFour t ^ 2 + thetaFour t ^ 3)
      ≤ 2 * Real.exp (-Real.pi * t) * 4 :=
        mul_le_mul hdef hinnerle hinnerpos (by positivity)
    _ = 8 * Real.exp (-Real.pi * t) := by ring

/-! ## The kernel: measurability and integrability -/

/-- Measurability of the t-arm theta on the whole time axis: the theta-4
constant is `1 + 2 *` an alternating tsum of powers of the nome, every
term measurable on `t`, so the whole sum is measurable countably. -/
private theorem thetaFour_measurable : Measurable (thetaFour) := by
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

/-- The 1111 kernel is a.e. strongly measurable on any measurable set:
pointwise in `thetaFour_measurable` (the R233 `kernel_aemeas` pattern,
simpler: no pointwise split needed, the theta-4 core is measurable on
the whole time axis). -/
private theorem kernel1111_aemeas (s : Set ℝ) (_ms : MeasurableSet s) :
    AEStronglyMeasurable (fun t => t * (thetaFour t ^ 4 - 1))
      (MeasureTheory.volume.restrict s) := by
  have hone : Measurable (fun _ : ℝ => (1:ℝ)) := measurable_const
  have hp : Measurable (fun t : ℝ => thetaFour t ^ 4) :=
    thetaFour_measurable.pow_const 4
  have hmeas : Measurable (fun t : ℝ => t * (thetaFour t ^ 4 - 1)) :=
    measurable_id.mul (hp.sub hone)
  exact hmeas.aestronglyMeasurable

/-- THE SMALL-T HALF: the 1111 kernel `t -> t * (thetaFour t ^ 4 - 1)` is
integrable on `(0, 1]`. The kernel is nonpositive there (the character
kills the zero mode: thetaFour ^ 4 <= 1 with no Poisson estimate at
all), so its absolute value is t * (1 - thetaFour ^ 4) <= t <= 1 < 2.
The honest small-t half of Z_1111(2)'s convergence, elementary. -/
theorem kernel1111_integrable_small :
    IntegrableOn (fun t => t * (thetaFour t ^ 4 - 1)) (Ioc (0:ℝ) 1)
      MeasureTheory.volume := by
  have hvol : MeasureTheory.volume (Ioc (0:ℝ) 1) < ⊤ := by
    rw [volume_Ioc]
    simp
  have hbnd : ∀ x ∈ Ioc (0:ℝ) 1, ‖x * (thetaFour x ^ 4 - 1)‖ ≤ 2 := by
    intro x hx
    have hx0 : 0 < x := (Set.mem_Ioc.mp hx).1
    have hx1 : x ≤ 1 := (Set.mem_Ioc.mp hx).2
    have h4 := (thetaFour_pow_bounds hx0).1
    have hθ4 : 0 ≤ thetaFour x ^ 4 := by
      have hrr : thetaFour x ^ 4 = (thetaFour x ^ 2) ^ 2 := by ring
      rw [hrr]
      exact sq_nonneg _
    have hnp : x * (thetaFour x ^ 4 - 1) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos hx0.le (by linarith)
    rw [Real.norm_eq_abs, abs_of_nonpos hnp]
    have hrw : -(x * (thetaFour x ^ 4 - 1)) = x * (1 - thetaFour x ^ 4) := by ring
    rw [hrw]
    have h1 : x * (1 - thetaFour x ^ 4) ≤ x * 1 :=
      mul_le_mul_of_nonneg_left (by linarith) hx0.le
    have h1' : x * 1 ≤ 2 := by linarith
    linarith
  exact IntegrableOn.of_bound hvol
    (kernel1111_aemeas (Ioc (0:ℝ) 1) measurableSet_Ioc) 2
    (Filter.mem_of_superset (self_mem_ae_restrict measurableSet_Ioc) hbnd)

/-- THE LARGE-T HALF: the 1111 kernel is integrable on `(1, inf)`. The
deficit law gives 1 - thetaFour ^ 4 <= 8 * exp (-pi*x) <= 8 * exp (-x)
(since pi >= 1), so the kernel is dominated by
`8 * (x * exp (-x))`, itself integrable by Mathlib's
`integrableOn_rpow_mul_exp_neg_rpow` at `p = s = 1` (the R233 receipt). -/
theorem kernel1111_integrable_large :
    IntegrableOn (fun t => t * (thetaFour t ^ 4 - 1)) (Ioi (1:ℝ))
      MeasureTheory.volume := by
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
      (fun t => (8:ℝ) * (t * Real.exp (-t)))
      (MeasureTheory.volume.restrict (Ioi (1:ℝ))) :=
    MeasureTheory.Integrable.const_mul hbase1 8
  have hdom : ∀ x ∈ Ioi (1:ℝ),
      ‖x * (thetaFour x ^ 4 - 1)‖ ≤ ‖(8:ℝ) * (x * Real.exp (-x))‖ := by
    intro x hx
    have hx1 : (1:ℝ) < x := Set.mem_Ioi.mp hx
    have hx0 : (0:ℝ) < x := by linarith
    have h4 := (thetaFour_pow_bounds hx0).1
    have hdef := (thetaFour_pow_bounds hx0).2
    have hnp : x * (thetaFour x ^ 4 - 1) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos hx0.le (by linarith)
    have hnn2 : 0 ≤ (8:ℝ) * (x * Real.exp (-x)) := by positivity
    rw [Real.norm_eq_abs, abs_of_nonpos hnp, Real.norm_eq_abs, abs_of_nonneg hnn2]
    have hrw : -(x * (thetaFour x ^ 4 - 1)) = x * (1 - thetaFour x ^ 4) := by ring
    rw [hrw]
    have hqe : Real.exp (-(Real.pi) * x) ≤ Real.exp (-x) := by
      refine Real.exp_le_exp.mpr ?_
      nlinarith [hpione, hx0]
    have hmid : x * (1 - thetaFour x ^ 4) ≤ x * (8 * Real.exp (-Real.pi * x)) :=
      mul_le_mul_of_nonneg_left hdef hx0.le
    have hqe2 : 8 * Real.exp (-Real.pi * x) ≤ 8 * Real.exp (-x) := by
      nlinarith [hqe]
    have hmid2 : x * (8 * Real.exp (-Real.pi * x)) ≤ x * (8 * Real.exp (-x)) :=
      mul_le_mul_of_nonneg_left hqe2 hx0.le
    have hE : x * (8 * Real.exp (-x)) = (8:ℝ) * (x * Real.exp (-x)) := by ring
    exact hmid.trans hmid2 |>.trans_eq hE
  exact MeasureTheory.Integrable.mono hdom0
    (kernel1111_aemeas (Ioi (1:ℝ)) measurableSet_Ioi)
    (Filter.mem_of_superset (self_mem_ae_restrict measurableSet_Ioi) hdom)

/-- THE CAPSTONE UNION: the 1111 kernel is integrable on (0,1] ∪ (1,inf). -/
theorem kernel1111_integrable_union :
    IntegrableOn (fun x => x * (thetaFour x ^ 4 - 1)) (Ioc (0:ℝ) 1 ∪ Ioi (1:ℝ))
      MeasureTheory.volume := by
  rw [integrableOn_union]
  exact ⟨kernel1111_integrable_small, kernel1111_integrable_large⟩

/-- THE FULL KERNEL'S INTEGRABILITY: the s = 2 Mellin kernel of the 1111
arm, `t -> t * (thetaFour t ^ 4 - 1)`, is integrable on the whole
half-line `(0, inf)` -- the 2-adic arm's honest object exists. The
kernel's VALUE on any interval remains a named window (order 1113 stone
(iii)); this is existence only. -/
theorem kernel1111_integrable_full :
    IntegrableOn (fun x => x * (thetaFour x ^ 4 - 1)) (Ioi (0:ℝ)) volume := by
  rw [← Set.Ioc_union_Ioi_eq_Ioi (by norm_num : (0:ℝ) ≤ 1)]
  exact kernel1111_integrable_union

/-! ## The honest object (D1): ZAdic1111 -/

/-- THE 2-ADIC ARM'S HONEST OBJECT (D1): the book's s = 2 normalization of
the 1111 arm,
`ZAdic1111 = pi^2 * integral over (0, inf) of t * (thetaFour t ^ 4 - 1)`,
with `thetaFour t ^ 4 = theta4(exp(-pi t))^4 = Theta_1111(t)` the
theta-constant-fourth-power of the blueprint's 1111 character. The
integral exists by `kernel1111_integrable_full`; its closed-form VALUE
remains a named window. -/
noncomputable def ZAdic1111 : ℝ :=
  Real.pi ^ 2 * ∫ x in Ioi (0:ℝ), x * (thetaFour x ^ 4 - 1) ∂MeasureTheory.volume

/-- THE ONE-SIDED HONEST LAW: ZAdic1111 <= 0. The kernel is nonpositive
on the whole half-line (the character kills the zero mode:
`thetaFour x ^ 4 <= 1`), so the integral is nonpositive and the prefactor
`pi^2` is nonnegative. The VALUE of ZAdic1111 (the blueprint's
`-(2/3) * pi^2 * log 2` conjecture) remains a named window; only the
sign is claimed here. -/
theorem ZAdic1111_nonpos : ZAdic1111 ≤ 0 := by
  have hint : ∫ x in Ioi (0:ℝ), x * (thetaFour x ^ 4 - 1) ∂MeasureTheory.volume ≤ 0 := by
    rw [← integral_indicator measurableSet_Ioi]
    refine integral_nonpos (f := fun x => (Ioi (0:ℝ)).indicator
        (fun x => x * (thetaFour x ^ 4 - 1)) x) ?_
    intro x
    by_cases hx : x ∈ Ioi (0:ℝ)
    · simp only [Set.indicator_of_mem hx]
      have hx0 : 0 < x := Set.mem_Ioi.mp hx
      have h4 := (thetaFour_pow_bounds hx0).1
      exact mul_nonpos_of_nonneg_of_nonpos hx0.le (by linarith)
    · simp only [Set.indicator_apply, if_neg hx]
      exact le_refl _
  exact mul_nonpos_of_nonneg_of_nonpos (by positivity) hint

/-! ## The integer bridge on the time axis -/

/-- THE ℤ-REPRESENTATION ON THE T-ARM: for every `t > 0` the time-axis
theta equals the book's integer form at the same nome — the L1b bridge
(`routeL1b_proved`, R217) read on the time axis, cashed at the t-nome.
This is the honest bridge stone: every future ℤ-side argument on the
1111 arm enters through this door. -/
theorem thetaFour_eq_theta4z {t : ℝ} (ht : 0 < t) :
    thetaFour t = theta4z (Real.exp (-Real.pi * t)) := by
  obtain ⟨hq0, hq1⟩ := qexp_pos_lt_one ht
  exact routeL1b_proved _ hq0 hq1

end YangMills.DualBook
