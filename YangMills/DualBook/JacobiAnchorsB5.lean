/-
PROVENANCE: R229 THE-B5-DOUBLED-NOME-FACTORIZATION (Tue 2026-11-24). The
fifth and LAST of the five named windows of the R2 candidate
(JacobiAnchorsB.lean) taken to the battery: the doubled-nome
factorization `routeB5`,
  ∑' p : ℤ × ℤ, latV q p = theta3z (q * q) * theta3z (q * q)   for 0 < q < 1,
which closes the R2 assembly: with B5 paid, `anchorB_of_route` runs on
nothing, `jacobiAnchorB` —
  theta3 q ^ 2 + theta4 q ^ 2 = 2 * theta3 (q * q) ^ 2   for 0 < q < 1 —
falls UNCONDITIONALLY, seven of seven hypotheses discharged by green
modules: the two R1 bridges (L1a, L1b) and the five B-windows
(B2a, B2b, B3, B4, B5).

THE CONTENT, IN ONE BREATH: this window is B2a's own receipt read at
the doubled nome. `latV q p = latU (q · q) p` by rfl — the doubled-nome
lattice summand IS the unsigned theta-3 lattice summand at the nome
`q²` — and `0 < q² < 1` follows from the domain hypotheses
(`positivity` and `pow_lt_one₀`, the same doubled-nome receipt the
conditional assembly itself carries). B2a's proved identity
`theta3z_mul_theta3z` then runs verbatim at the nome `q²`:
the square of the theta-3 integer sum at the doubled nome IS the
lattice book, read in the reverse direction.

PAPER ROUTE (pre-registered in the R2 candidate, executed here):
  ∑' p : ℤ × ℤ, latV q p
  = ∑' p : ℤ × ℤ, latU (q * q) p         [tsum_congr + the rfl bridge latV q p = latU (q * q) p]
  = theta3z (q * q) * theta3z (q * q)    [B2a's receipt at the nome q², reversed: Summable.tsum_mul_tsum and the
                                          Fubini twin already paid their battery in R225; here they ride imported]

THE BORDER, NAMED IN THE OPEN: every kernel step of this window was
proved on the green record before this module existed — the Cauchy
lift and the pair-family summability live in the B2a certificate
(R225), and this window supplies only the name substitution (the rfl
bridge) and the domain doubling (`0 < q² < 1`). That is why the last
stone is the shortest walk the ladder has: the machinery was paid for
twice (R219, R225) and this window merely cashes it at the doubled
nome.

STATUS: compiled green in-sandbox against the pinned triplet (Mathlib
31ce06eaadf4a200c0e1407c5f10953cf606b8f8, lake 5.0.0, lean
v4.37.0-rc1), with the R228 B4 certificate reproduced green (3,542
jobs) through the banked one-command snapshot script before any new
math crossed it.

SCOPE NOTE: this module certifies THIS ARITHMETIC — one classical
Jacobi theta identity, the doubled-nome lattice sum factored back into
the square of the theta-3 integer sum at the doubled nome. It proves
nothing about physical four-dimensional Yang–Mills theory and claims
no Clay Millennium result. Bench FROZEN AT 100.0, the crossing never
claimed.
-/

import Mathlib.Topology.Algebra.InfiniteSum.Ring
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Analysis.Normed.Group.InfiniteSum
import YangMills.DualBook.JacobiAnchors
import YangMills.DualBook.JacobiAnchorsB
import YangMills.DualBook.JacobiAnchorsB2a
import YangMills.DualBook.JacobiAnchorsB4

/-!
# R229: the doubled-nome factorization (B5, the last stone)

The doubled-nome lattice sum factors back into the square of the
theta-3 integer sum at the doubled nome: B2a's own receipt, cashed at
`q²`. With B5 paid, the five-window assembly `anchorB_of_route` has no
hypothesis left, and `jacobiAnchorB` — the second Jacobi anchor —
falls unconditionally. Five of five; the R2 route closes.
-/

namespace YangMills.DualBook

open Filter Topology

/-! ## The doubled-nome domain receipt -/

/-- The doubled nome is positive: `q² > 0` for `q > 0` (the same
receipt the conditional assembly itself carries). -/
private theorem qq_pos {q : ℝ} (hq0 : 0 < q) : 0 < q * q := by
  positivity

/-- The doubled nome stays below one: `q² < 1` for `0 < q < 1`
(`pow_lt_one₀` once the square is read as a power — the assembly's
own receipt, restated private as every window does). -/
private theorem qq_lt_one {q : ℝ} (hq0 : 0 < q) (hq1 : q < 1) :
    q * q < 1 := by
  rw [← sq]
  exact pow_lt_one₀ hq0.le hq1 (by omega)

/-! ## The rfl bridge: the doubled-nome summand IS B2a's summand -/

/-- THE BRIDGE (a rfl): the doubled-nome lattice summand is the
unsigned theta-3 lattice summand evaluated at the nome `q · q` —
`latV` was LITERALLY DEFINED as `latU` at the doubled nome, so this
is definition, not theorem. -/
private theorem latV_eq_latU {q : ℝ} (p : ℤ × ℤ) :
    latV q p = latU (q * q) p := rfl

/-! ## The window itself -/

/-- WINDOW B5, the main identity: the doubled-nome lattice sum is
the square of the theta-3 integer sum at the doubled nome. The heavy
machinery — the Mathlib Cauchy lift, the pair-family Fubini
summability, the exponent normalization — all rode B2a's R225 battery
and is imported verbatim; this window supplies the bridge and the
domain doubling only. -/
theorem latV_tsum_eq_theta3z_sq {q : ℝ} (hq0 : 0 < q) (hq1 : q < 1) :
    ∑' p : ℤ × ℤ, latV q p = theta3z (q * q) * theta3z (q * q) :=
  (tsum_congr (fun p => latV_eq_latU p)).trans
    (theta3z_mul_theta3z (qq_pos hq0) (qq_lt_one hq0 hq1)).symm

/-- WINDOW B5, PROVED: the doubled-nome factorization of the R2
route, now an unconditional theorem. Feed this to
`anchorB_of_route_one_paid` (B4's export) to discharge `h5`: FIVE of
the five stones, ZERO named windows remaining. -/
theorem routeB5_proved : routeB5 :=
  fun _ hq0 hq1 => latV_tsum_eq_theta3z_sq hq0 hq1

/-- THE ROUTE CLOSES (TYPE-CHECKED HERE): with B2a, B2b, B3, B4 and
B5 all proved, `anchorB_of_route` has NO hypothesis remaining, and
`jacobiAnchorB` —
  theta3 q ^ 2 + theta4 q ^ 2 = 2 * theta3 (q * q) ^ 2
for every 0 < q < 1 — is UNCONDITIONAL. Seven of seven stones paid on
the R2 route (the two R1 bridges and the five B-windows); the
conditional assembly is a theorem with nothing left to ask. The
A-route precedent name honored: as `anchorA_of_route_seven_paid`
sealed the first route in R223, `anchorB_of_route_seven_paid` seals
the second here. -/
theorem anchorB_of_route_seven_paid : jacobiAnchorB :=
  anchorB_of_route_one_paid routeB5_proved

end YangMills.DualBook
