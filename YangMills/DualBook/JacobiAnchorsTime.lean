/-
PROVENANCE: R239 — the Anchors Unconditional window (the parity
decomposition cashed on the time axis), Papa's 172nd ask, following
Gemini's relay (R238 sealed at master a568aea, 6,530 jobs green).

THE WINDOW: the two time-axis Jacobi anchors, carried as NAMED WINDOWS
(hypotheses) by every R238 cascade theorem, become UNCONDITIONAL
THEOREMS here. The parity decomposition of the two-dimensional theta
series is already BANKED: the q-space faces `jacobiAnchorA` and
`jacobiAnchorB` were proved unconditional across R216-R229
(`anchorA_of_route_seven_paid`, JacobiAnchorsL4; `anchorB_of_route_
seven_paid`, JacobiAnchorsB5). This module reads those paid anchors at
the t-nome q = exp (-pi*t), where 0 < q < 1 for every t > 0, so the
whole q-space machinery transfers verbatim. The one new brick is the
bridge lemma `thetaT_eq_theta3_nome`: the Mellin route's thetaT IS the
book's theta3 at the t-nome.

WHAT BECOMES UNCONDITIONAL (the stones the relay named):
  * `anchorA_time_proved : anchorA_time` — the Landen identity
    thetaT t * thetaFour t = thetaFour (2*t)^2, unconditional;
  * `anchorB_time_proved : anchorB_time` — thetaT t^2 + thetaFour t^2
    = 2 * thetaT (2*t)^2, unconditional;
  * `ZAdic1100_eq_quarter_ZAdic1111_unconditional` — STONE A:
    Z_1100(2) = (1/4) * Z_1111(2), the anchor hypothesis discharged;
  * `ZAdic1000_add_ZAdic1110_eq_unconditional` — STONE B:
    Z_1000(2) + Z_1110(2) = (1/8) * Z_1111(2), both anchors
    discharged.

WHAT REMAINS OPEN (the honest remainders, unchanged by this window):
the two w2 analytic evaluations — Z_1111(2) = -(2/3)*pi^2*log 2 (the
modular engine thetaFour_transform is banked, R237) and
Z_1000(2) - Z_1110(2) = 2*pi*G (Gaussian integers + the R231 Catalan
gate). With this window's anchors unconditional, BOTH evaluations now
cascade down to all four arms unconditionally once they land.

SCOPE NOTE: this module certifies THIS ARITHMETIC — classical theta
identities read at the t-nome. It proves nothing about physical
four-dimensional Yang-Mills theory and claims no Clay Millennium
result. Bench frozen at 100.0. The crossing never claimed.

PROVED AND SEALED in the c1668 window (Thu 2026-11-26, Mathlib
31ce06ea / Lean v4.37.0-rc1 vintage): lake build green on the first
probe (6,554 jobs), zero sorry, zero native_decide, zero unsafe;
notarized [propext, Classical.choice, Quot.sound] on all five public
theorems (thetaT_eq_theta3_nome, anchorA_time_proved,
anchorB_time_proved, ZAdic1100_eq_quarter_ZAdic1111_unconditional,
ZAdic1000_add_ZAdic1110_eq_unconditional). Pre-registered via mailbox
order 1138 item GEN_PREREG (Papa's 172nd ask, Gemini's relay); the
two time-axis anchors UNCONDITIONAL (the q-space routes read at the
t-nome, the parity decomposition banked R216-R229), both cascade
stones UNCONDITIONAL, the two w2 evaluations the sole remaining
Epstein debt. The build and notary ran on exactly the source of md5
e1a49c2adf8d6c4b8aae217d472600fc; this certificate adds only this
seal note to that source. The warm-verify of the whole proved chain
(6,560 jobs, stage 3) preceded the new math per the standing law.
-/
import Mathlib.Topology.Algebra.InfiniteSum.NatInt
import Mathlib.Topology.Algebra.InfiniteSum.Ring
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import YangMills.DualBook.JacobiAnchorsL4
import YangMills.DualBook.JacobiAnchorsB5
import YangMills.DualBook.MellinCascadeWindow

/-!
# The Time-Axis Jacobi Anchors, Unconditional (R239)

The R238 cascade carried the two time-axis anchors as hypotheses. The
q-space faces of the same anchors are unconditional theorems of the
R216-R229 route family. At the t-nome `q = exp (-pi*t)` — inside the
book's domain `0 < q < 1` for every `t > 0` — the paid routes apply
verbatim, and the anchors retire from named windows to theorems.
-/

namespace YangMills.DualBook

/-! ## The t-nome and its facts -/

/-- The t-nome lies strictly inside the book's domain `0 < q < 1` for
every `t > 0`. -/
private theorem nome_pos_lt_one {t : ℝ} (ht : 0 < t) :
    0 < Real.exp (-Real.pi * t) ∧ Real.exp (-Real.pi * t) < 1 := by
  constructor
  · exact Real.exp_pos _
  · have hpt : 0 < Real.pi * t := mul_pos Real.pi_pos ht
    have he := Real.exp_lt_exp.mpr (show (-Real.pi * t : ℝ) < 0 by linarith)
    simpa using he

/-- The doubled t-nome is the square of the t-nome:
`exp (-pi * (2 * t)) = exp (-pi * t) * exp (-pi * t)` — the nome glue
that identifies `thetaFour (2 * t)` with `theta4 (q * q)`. -/
private theorem nome_sq (t : ℝ) : Real.exp (-Real.pi * (2 * t))
    = Real.exp (-Real.pi * t) * Real.exp (-Real.pi * t) := by
  rw [← Real.exp_add]
  ring

/-! ## The bridge: thetaT IS theta3 at the t-nome -/

/-- The bridge family: the integer theta family of `thetaT` under its
own name, so the NatInt even-split machinery applies. -/
private noncomputable def famT (t : ℝ) (z : ℤ) : ℝ :=
  Real.exp (-Real.pi * t * (z : ℝ) ^ 2)

/-- The bridge family is even — the square kills the sign. -/
private theorem famT_even (t : ℝ) : Function.Even (famT t) := by
  intro z
  simp only [famT]
  congr 1
  push_cast
  ring

/-- THE BRIDGE LEMMA: `thetaT t = theta3 (exp (-pi * t))` for every
`t > 0`. The Mellin route's integer theta IS the book's theta-3
constant at the t-nome. The proof rides the NatInt even-split (the
R233 `thetaT_split` method, restated here on a local family so no
private lemma crosses a module boundary), then matches the house
`theta3` tail term-by-term through `Real.exp_mul_natCast`. -/
theorem thetaT_eq_theta3_nome {t : ℝ} (ht : 0 < t) :
    thetaT t = theta3 (Real.exp (-Real.pi * t)) := by
  have hsumm : Summable (famT t) := thetaT_summable ht
  have hsplit := tsum_int_eq_zero_add_two_mul_tsum_pnat (famT_even t) hsumm
  rw [two_nsmul, ← two_mul] at hsplit
  have h0 : famT t 0 = 1 := by simp only [famT]; norm_num
  have hc : ∀ m : ℕ, famT t ((m : ℕ) : ℤ)
      = Real.exp (-Real.pi * t * ((m : ℝ) ^ 2)) := by
    intro m
    simp only [famT]
    push_cast
    ring
  have hpnat := tsum_pnat_eq_tsum_succ
    (f := fun (m : ℕ) => famT t ((m : ℕ) : ℤ))
  have hfinal : ∑' (p : ℕ+), famT t ((↑(p : ℕ) : ℕ) : ℤ)
      = ∑' (n : ℕ), Real.exp (-Real.pi * t * ((n : ℝ) + 1) ^ 2) := by
    rw [hpnat]
    exact tsum_congr (fun n => by rw [hc (n + 1)]; push_cast; ring)
  have hEq : ∀ n : ℕ, Real.exp (-Real.pi * t * ((n : ℝ) + 1) ^ 2)
      = (Real.exp (-Real.pi * t)) ^ ((n + 1) ^ 2) := by
    intro n
    rw [← Real.exp_mul_natCast]
    congr 1
    push_cast
    ring
  calc thetaT t = ∑' (z : ℤ), famT t z := rfl
    _ = 1 + 2 * ∑' (n : ℕ), Real.exp (-Real.pi * t * ((n : ℝ) + 1) ^ 2) := by
        show ∑' (z : ℤ), famT t z
          = 1 + 2 * ∑' (n : ℕ), Real.exp (-Real.pi * t * ((n : ℝ) + 1) ^ 2)
        rw [hsplit, h0, hfinal]
    _ = 1 + 2 * ∑' (n : ℕ), (Real.exp (-Real.pi * t)) ^ ((n + 1) ^ 2) := by
        rw [tsum_congr hEq]
    _ = theta3 (Real.exp (-Real.pi * t)) := by
        unfold theta3
        rfl

/-! ## The anchors, unconditional -/

/-- THE TIME-AXIS JACOBI ANCHOR A, UNCONDITIONAL: for every `t > 0`,
`thetaT t * thetaFour t = thetaFour (2 * t) ^ 2`. The R238 cascade
carried this as a named window (`anchorA_time`, hypothesis form); the
q-space face was proved unconditional across R216-R223 by the parity
decomposition of the two-dimensional theta series
(`anchorA_of_route_seven_paid`), and at the t-nome `q = exp (-pi*t)`
the paid route applies verbatim. The named window is RETIRED, not
erased: the hypothesis form stays in the record as history. -/
theorem anchorA_time_proved : anchorA_time := by
  intro t ht
  obtain ⟨hq0, hq1⟩ := nome_pos_lt_one ht
  have hA := anchorA_of_route_seven_paid (Real.exp (-Real.pi * t)) hq0 hq1
  show thetaT t * thetaFour t = thetaFour (2 * t) ^ 2
  rw [thetaT_eq_theta3_nome ht]
  unfold thetaFour
  rw [nome_sq t]
  exact hA

/-- THE TIME-AXIS JACOBI ANCHOR B, UNCONDITIONAL: for every `t > 0`,
`thetaT t ^ 2 + thetaFour t ^ 2 = 2 * thetaT (2 * t) ^ 2`. The q-space
face was proved unconditional across R225-R229
(`anchorB_of_route_seven_paid`); the t-nome cashes it. -/
theorem anchorB_time_proved : anchorB_time := by
  intro t ht
  obtain ⟨hq0, hq1⟩ := nome_pos_lt_one ht
  have hB := anchorB_of_route_seven_paid (Real.exp (-Real.pi * t)) hq0 hq1
  have h2t : 0 < 2 * t := by positivity
  show thetaT t ^ 2 + thetaFour t ^ 2 = 2 * thetaT (2 * t) ^ 2
  rw [thetaT_eq_theta3_nome ht, thetaT_eq_theta3_nome h2t]
  unfold thetaFour
  rw [nome_sq t]
  exact hB

/-! ## The stones, unconditional -/

/-- STONE A, UNCONDITIONAL: `Z_1100(2) = (1/4) * Z_1111(2)` with the
anchor hypothesis DISCHARGED — the R238 cascade stone with
`anchorA_time_proved` in place of the named window. -/
theorem ZAdic1100_eq_quarter_ZAdic1111_unconditional :
    ZAdic1100 = (1 / 4) * ZAdic1111 :=
  ZAdic1100_eq_quarter_ZAdic1111 anchorA_time_proved

/-- STONE B, UNCONDITIONAL: `Z_1000(2) + Z_1110(2) = (1/8) * Z_1111(2)`
with BOTH anchor hypotheses DISCHARGED — the R238 cascade stone with
`anchorA_time_proved` and `anchorB_time_proved` in place of the named
windows. -/
theorem ZAdic1000_add_ZAdic1110_eq_unconditional :
    ZAdic1000 + ZAdic1110 = (1 / 8) * ZAdic1111 :=
  ZAdic1000_add_ZAdic1110_eq anchorA_time_proved anchorB_time_proved

end YangMills.DualBook

/-!
  REMAINDERS, honest and named (for R240+):
  (w2) the VALUES, the sole remaining debt of the Epstein book, now
       reachable unconditionally: Z_1111(2) = -(2/3)*pi^2*log 2 (the
       modular engine thetaFour_transform is banked, R237) and the
       difference Z_1000(2) - Z_1110(2) = 2*pi*G (Gaussian integers +
       the R231 Catalan gate). Both cascade down to all four arms at
       once once they land — the anchors no longer gate anything.
  Bench frozen at 100.0. Scope: THIS ARITHMETIC only.
-/
