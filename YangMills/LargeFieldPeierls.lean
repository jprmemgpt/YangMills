import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import YangMills.GaugeLattice
import YangMills.RenewalAndCauchy
import YangMills.RGFlowBridge
import YangMills.BalabanBlockSpin

/-!
# Module 20: LargeFieldPeierls (Lean 4 + Mathlib4)
Formalizes the large-field Peierls suppression bounds and certified KP corridor entry
bridge connecting Balaban block-spin geometry (`BalabanBlockSpin`) to `RGFlowBridge`:
1. Pointwise and finite-polymer Wilson action lower bounds on large-field plaquettes
   (`large_field_plaquette_action_gt`, `large_field_polymer_action_ge`) and exponential
   Boltzmann suppression (`large_field_boltzmann_suppression`).
2. Certified real lower bound `2653 / 1000 < exp 1` (`exp_one_gt_2653_div_1000`) and
   proof that the full Peierls tail envelope at minimal area `A₀ ≥ 7` strictly beats the
   KP bridge activity ceiling `1 / 567` (`peierls_tail_at_seven_lt_bridge_cap`,
   `peierls_tail_sum_lt_bridge_cap`).
3. Certified corridor-entry theorem (`balaban_peierls_implies_kp_corridor`) and end-to-end
   block-scale bridge (`balaban_block_to_corridor_mass_gap`): for any block scale `L ≥ 3`
   (giving minimal large-field spine area `L² ≥ 9 ≥ 7` and positive Neumann gap floor
   `4 sin²(π / (2L)) > 0`), large-field Peierls suppression drives `epsBridge < 1 / 567`
   and delivers the full five-toll mass floor and renewal-race victory.
-/

namespace YangMills

/-! ## 1. Large-Field Wilson Action Lower Bounds & Boltzmann Suppression -/

/-- On any large-field plaquette (`1 - χ(U_p) > pThresh`) at coupling `β > 0`,
    the Wilson plaquette action strictly exceeds `β · pThresh`. -/
theorem large_field_plaquette_action_gt {G : Type*} [Group G]
    (χ : UnitaryTrace G) (beta pThresh : ℝ) (hbeta : 0 < beta)
    (U : GaugeField G) (x : Site) (μ ν : Fin 4)
    (hlf : LargeFieldPlaquette χ U x μ ν pThresh) :
    beta * pThresh < wilsonPlaquetteAction χ beta U x μ ν := by
  unfold wilsonPlaquetteAction
  exact mul_lt_mul_of_pos_left hlf hbeta

/-- On any finite polymer `S` of large-field plaquettes, the total Wilson action is bounded
    below by `β · pThresh · |S|`. -/
theorem large_field_polymer_action_ge {G : Type*} [Group G]
    (χ : UnitaryTrace G) (beta pThresh : ℝ) (hbeta : 0 ≤ beta)
    (U : GaugeField G) (S : Finset (Site × Fin 4 × Fin 4))
    (hlf : ∀ p ∈ S, LargeFieldPlaquette χ U p.1 p.2.1 p.2.2 pThresh) :
    beta * pThresh * (S.card : ℝ) ≤
      ∑ p ∈ S, wilsonPlaquetteAction χ beta U p.1 p.2.1 p.2.2 := by
  have hsum : ∑ _p ∈ S, (beta * pThresh) ≤
      ∑ p ∈ S, wilsonPlaquetteAction χ beta U p.1 p.2.1 p.2.2 := by
    refine Finset.sum_le_sum fun p hp => ?_
    unfold wilsonPlaquetteAction
    exact mul_le_mul_of_nonneg_left (le_of_lt (hlf p hp)) hbeta
  simpa [Finset.sum_const, nsmul_eq_mul, mul_comm] using hsum

/-- Exponential Boltzmann suppression of any large-field polymer `S` of cardinality `|S|`:
    `exp(-∑_{p ∈ S} S_p(U)) ≤ exp(-β · pThresh · |S|)`. -/
theorem large_field_boltzmann_suppression {G : Type*} [Group G]
    (χ : UnitaryTrace G) (beta pThresh : ℝ) (hbeta : 0 ≤ beta)
    (U : GaugeField G) (S : Finset (Site × Fin 4 × Fin 4))
    (hlf : ∀ p ∈ S, LargeFieldPlaquette χ U p.1 p.2.1 p.2.2 pThresh) :
    Real.exp (-(∑ p ∈ S, wilsonPlaquetteAction χ beta U p.1 p.2.1 p.2.2)) ≤
      Real.exp (-(beta * pThresh * (S.card : ℝ))) := by
  apply Real.exp_le_exp.mpr
  linarith [large_field_polymer_action_ge χ beta pThresh hbeta U S hlf]

/-! ## 2. Certified Peierls Tail Beats the 1/567 KP Bridge Ceiling -/

/-- Elementary certified real lower bound `2.653 < exp 1`, derived purely from
    `1 + 1/20 ≤ exp(1/20)` raised to the 20th power. -/
theorem exp_one_gt_2653_div_1000 : (2653 : ℝ) / 1000 < Real.exp 1 := by
  have h1 : (21 : ℝ) / 20 ≤ Real.exp ((1 : ℝ) / 20) := by
    linarith [Real.add_one_le_exp ((1 : ℝ) / 20)]
  have hpow : ((21 : ℝ) / 20) ^ (20 : ℕ) ≤ (Real.exp ((1 : ℝ) / 20)) ^ (20 : ℕ) :=
    pow_le_pow_left₀ (by norm_num) h1 20
  have hexp : (Real.exp ((1 : ℝ) / 20)) ^ (20 : ℕ) = Real.exp 1 := by
    rw [← Real.exp_nat_mul]
    norm_num
  have hnum : (2653 : ℝ) / 1000 < ((21 : ℝ) / 20) ^ (20 : ℕ) := by norm_num
  linarith

/-- Certified Peierls envelope bound at area `A₀ = 7`:
    `exp(-7) / (1 - exp(-1)) < 1 / 567`. -/
theorem peierls_tail_at_seven_lt_bridge_cap :
    Real.exp (-7 : ℝ) / (1 - Real.exp (-1)) < (1 : ℝ) / 567 := by
  have he : (2653 : ℝ) / 1000 < Real.exp 1 := exp_one_gt_2653_div_1000
  have h1sub_pos : 0 < 1 - Real.exp (-1) := by
    have hlt : Real.exp (-1) < 1 := by
      simpa [Real.exp_zero] using Real.exp_lt_exp.mpr (by norm_num : (-1 : ℝ) < 0)
    linarith
  have he6 : ((2653 : ℝ) / 1000) ^ (6 : ℕ) < Real.exp 6 := by
    have hpow : ((2653 : ℝ) / 1000) ^ (6 : ℕ) < (Real.exp 1) ^ (6 : ℕ) :=
      pow_lt_pow_left₀ he (by norm_num) (by norm_num)
    have h6 : (Real.exp 1) ^ (6 : ℕ) = Real.exp 6 := by
      rw [← Real.exp_nat_mul]
      norm_num
    linarith
  have hprod : (567 : ℝ) < Real.exp 6 * (Real.exp 1 - 1) := by
    have hnum : (567 : ℝ) < ((2653 : ℝ) / 1000) ^ (6 : ℕ) * ((1653 : ℝ) / 1000) := by norm_num
    have hsub : (1653 : ℝ) / 1000 < Real.exp 1 - 1 := by linarith
    have hmul : ((2653 : ℝ) / 1000) ^ (6 : ℕ) * ((1653 : ℝ) / 1000) <
        Real.exp 6 * (Real.exp 1 - 1) :=
      mul_lt_mul'' he6 hsub (by norm_num) (by norm_num)
    linarith
  have hident : Real.exp (-7 : ℝ) * (Real.exp 6 * (Real.exp 1 - 1)) = 1 - Real.exp (-1) := by
    have h1 : Real.exp (-7 : ℝ) * (Real.exp 6 * (Real.exp 1 - 1)) =
        Real.exp (-7 : ℝ) * Real.exp 6 * Real.exp 1 - Real.exp (-7 : ℝ) * Real.exp 6 := by ring
    rw [h1, ← Real.exp_add, ← Real.exp_add]
    have ha : (-7 : ℝ) + 6 + 1 = 0 := by norm_num
    have hb : (-7 : ℝ) + 6 = -1 := by norm_num
    rw [ha, hb, Real.exp_zero]
  have hmul_exp : Real.exp (-7 : ℝ) * 567 < 1 - Real.exp (-1) := by
    have hpos : 0 < Real.exp (-7 : ℝ) := Real.exp_pos (-7)
    have hlt := mul_lt_mul_of_pos_left hprod hpos
    linarith
  rw [div_lt_div_iff₀ h1sub_pos (by norm_num)]
  linarith

/-- For every minimal large-field polymer area `A₀ ≥ 7`, the Peierls tail envelope
    `exp(-A₀) / (1 - exp(-1))` strictly beats `1 / 567`. -/
theorem peierls_envelope_lt_bridge_cap (A0 : ℕ) (hA0 : 7 ≤ A0) :
    Real.exp (-(A0 : ℝ)) / (1 - Real.exp (-1)) < (1 : ℝ) / 567 := by
  have h1sub_pos : 0 < 1 - Real.exp (-1) := by
    have hlt : Real.exp (-1) < 1 := by
      simpa [Real.exp_zero] using Real.exp_lt_exp.mpr (by norm_num : (-1 : ℝ) < 0)
    linarith
  have hA0R : (7 : ℝ) ≤ (A0 : ℝ) := by exact_mod_cast hA0
  have hexp : Real.exp (-(A0 : ℝ)) ≤ Real.exp (-7 : ℝ) :=
    Real.exp_le_exp.mpr (by linarith)
  have hdiv : Real.exp (-(A0 : ℝ)) / (1 - Real.exp (-1)) ≤
      Real.exp (-7 : ℝ) / (1 - Real.exp (-1)) :=
    div_le_div_of_nonneg_right hexp (le_of_lt h1sub_pos)
  exact lt_of_le_of_lt hdiv peierls_tail_at_seven_lt_bridge_cap

/-- Every finite Peierls tail sum `∑_{k=0}^{n-1} exp(-(A₀ + k))` with `A₀ ≥ 7` is strictly
    below the certified KP bridge activity ceiling `1 / 567`. -/
theorem peierls_tail_sum_lt_bridge_cap (A0 n : ℕ) (hA0 : 7 ≤ A0) :
    (∑ k ∈ Finset.range n, Real.exp (-((A0 + k : ℕ) : ℝ))) < (1 : ℝ) / 567 :=
  lt_of_le_of_lt (peierls_tail_sum_bound A0 n) (peierls_envelope_lt_bridge_cap A0 hA0)

/-! ## 3. Balaban Peierls Suppression → Certified KP Corridor Entry -/

/-- Certified KP corridor-entry theorem:
    if the Peierls action floor satisfies `κ₀ ≥ 6.1516` and the non-negative bridge activity
    `epsBridge` is bounded by the 1-nat Peierls tail envelope at minimal area `A₀ ≥ 7`,
    then `InKPCorridor κ₀ epsBridge` holds. -/
theorem balaban_peierls_implies_kp_corridor
    (κ₀ epsBridge : ℝ) (A0 : ℕ)
    (hκ₀ : (61516 : ℝ) / 10000 ≤ κ₀)
    (heps0 : 0 ≤ epsBridge)
    (hA0 : 7 ≤ A0)
    (heps_peierls : epsBridge ≤ Real.exp (-(A0 : ℝ)) / (1 - Real.exp (-1))) :
    InKPCorridor κ₀ epsBridge := by
  refine ⟨hκ₀, heps0, ?_⟩
  exact le_of_lt (lt_of_le_of_lt heps_peierls (peierls_envelope_lt_bridge_cap A0 hA0))

/-- End-to-end Balaban block-scale bridge:
    for any block scale `L ≥ 3` (giving minimal large-field spine area `L² ≥ 9 ≥ 7` and
    strictly positive 4D Neumann gap floor `4 sin²(π / (2L)) > 0`), any Peierls-suppressed
    bridge activity `0 ≤ epsBridge ≤ exp(-L²) / (1 - exp(-1))` and `κ₀ ≥ 6.1516` certifies:
    1. Positive small-field Neumann fluctuation gap floor `0 < neumannGapFloor L`.
    2. Strict KP corridor entry `InKPCorridor κ₀ epsBridge`.
    3. Strictly positive mass floor `0 < m₀`, `R_stop⁻¹ ≤ m₀`, and renewal-race victory
       `1 ≤ 2 b₀ g_*² ln(m₀ / Λ_RG)`. -/
theorem balaban_block_to_corridor_mass_gap
    (L : ℕ) (hL : 3 ≤ L)
    (κ₀ epsBridge b0 gStarSq LambdaRG : ℝ)
    (hκ₀ : (61516 : ℝ) / 10000 ≤ κ₀)
    (heps0 : 0 ≤ epsBridge)
    (heps_peierls : epsBridge ≤ Real.exp (-((L * L : ℕ) : ℝ)) / (1 - Real.exp (-1)))
    (hb0 : 0 < b0) (hgStar : 0 < gStarSq) (hLambda : 0 < LambdaRG) :
    let m0 := corridorMassFloor κ₀ b0 gStarSq LambdaRG
    let RstopInv := LambdaRG * Real.exp (1 / (2 * b0 * gStarSq))
    0 < neumannGapFloor L ∧
    InKPCorridor κ₀ epsBridge ∧
    0 < m0 ∧
    RstopInv ≤ m0 ∧
    1 ≤ 2 * b0 * gStarSq * Real.log (m0 / LambdaRG) := by
  intro m0 RstopInv
  have hL2 : 2 ≤ L := by omega
  have hA0 : 7 ≤ L * L := by nlinarith
  have hcorr : InKPCorridor κ₀ epsBridge :=
    balaban_peierls_implies_kp_corridor κ₀ epsBridge (L * L) hκ₀ heps0 hA0 heps_peierls
  have hfloor := mass_gap_floor_from_five_tolls κ₀ b0 gStarSq LambdaRG hκ₀ hb0 hgStar hLambda
  exact ⟨neumannGapFloor_pos L hL2, hcorr, hfloor.1, hfloor.2.1, hfloor.2.2⟩

end YangMills
