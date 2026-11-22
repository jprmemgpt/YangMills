import Mathlib.Data.Rat.Defs
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith

/-!
# CorridorConstants — the repaired dependency ledger (R184 audit, all five tolls carried)

The first draft (the sister's Round-184 skeleton) defined
`deltaKappa := kappa0 - lnC4 - bridgeOverhead` and listed `lnC4Upper := 3079/1000`.
The R184 referee bench caught BOTH slips:
1. the structural `ln 16` fold toll and the resolvent-envelope correction were
   DROPPED (the certified chain is
   Δκ = -ln(z₀√A₂) - ln 16 - ln(8e) - ε²·Σ);
2. `3079/1000` is NOT an upper bound for `ln(8e) = 3.0794415...`
   (a rounding cut against its own direction).

This repaired file carries the FULL certified chain with honest directions,
as exact rationals, machine-verified by ym184_referee.cjs (tooth 184B2).

SCOPE (the honest one): this module certifies the RATIONAL LEDGER ONLY.
Every mathematical contact with Yang-Mills physics rides the hypotheses that
the physics modules (GaugeLattice, ContinuumOS, T1-T4) must eventually prove.
Zero sorries here is a claim about THIS arithmetic, never a formalized Clay
statement — the OS axioms are True-stubs in the skeleton and must stay LABELED
until real Mathlib proofs pay them.
-/


namespace YangMills

/-- The corridor constants as DECLARED rationals with certified directions.

Directions (machine-receipted; proofs to land in a future `AnalyticBounds.lean`):
* `kappa0Lower`: κ₀ = -ln z₀ = 6.151633299... ≥ 6.1516            (LOWER bound)
* `envelopeUpper`: -ln(1-1/567) ≤ 1/566 < 177/100000               (analytically:
  -ln(1-x) ≤ x/(1-x) at x = 1/567; integer check 100000 < 177*566)
* `lnFoldUpper`: ln 16 = 2.77258872... < 27726/10000                (UPPER bound)
* `lnC4Upper`: ln(8e) = 3.07944154... < 6159/2000                  (UPPER bound —
  the sister's 3079/1000 was BELOW the true value and is NOT an upper bound)
* `bridgeUpper`: (1/567)² · Σ(floor) = 431.9/567² < 84/62500       (UPPER bound).

The `h_*` fields are closures of the declarations (the future AnalyticBounds
module replaces them with real interval certificates). -/
structure CorridorConstants where
  kappa0Lower : ℚ
  envelopeUpper : ℚ
  lnFoldUpper : ℚ
  lnC4Upper : ℚ
  bridgeUpper : ℚ
  delta0 : ℚ
  rhoRes : ℚ
  sigmaFloor : ℚ
  lFinal : ℕ
  h_kappa0 : kappa0Lower = 61516 / 10000
  h_envelope : envelopeUpper = 177 / 100000
  h_lnFold : lnFoldUpper = 27726 / 10000
  h_lnC4 : lnC4Upper = 6159 / 2000
  h_bridge : bridgeUpper = 84 / 62500
  h_delta0 : delta0 = 1 / 4
  h_rhoRes : rhoRes = 1 / 567
  h_sigmaFloor : sigmaFloor = 4319 / 10
  h_lFinal : lFinal = 8

def certifiedConstants : CorridorConstants where
  kappa0Lower := 61516 / 10000
  envelopeUpper := 177 / 100000
  lnFoldUpper := 27726 / 10000
  lnC4Upper := 6159 / 2000
  bridgeUpper := 84 / 62500
  delta0 := 1 / 4
  rhoRes := 1 / 567
  sigmaFloor := 4319 / 10
  lFinal := 8
  h_kappa0 := rfl
  h_envelope := rfl
  h_lnFold := rfl
  h_lnC4 := rfl
  h_bridge := rfl
  h_delta0 := rfl
  h_rhoRes := rfl
  h_sigmaFloor := rfl
  h_lFinal := rfl

/-- The certified chain, ALL FIVE TERMS: Δκ ≥ κ₀_lower - env - ln16 - ln(8e) - bridge. -/
def deltaKappa (c : CorridorConstants) : ℚ :=
  c.kappa0Lower - c.envelopeUpper - c.lnFoldUpper - c.lnC4Upper - c.bridgeUpper

/-- The final coarse-block decay exponent μ₀(8) = L·Δκ. -/
def mu0Final (c : CorridorConstants) : ℚ := (c.lFinal : ℚ) * deltaKappa c

/-- The dimensionless mass ratio c_m = μ₀/2. -/
def cMass (c : CorridorConstants) : ℚ := mu0Final c / 2

/-- The certified pair margin as an exact rational (the corridor receipt 0.29489277). -/
def marginPairCertified : ℚ := 29489277 / 100000000

theorem certified_deltaKappa_pos : 0 < deltaKappa certifiedConstants := by
  unfold deltaKappa certifiedConstants; norm_num

/-- The floor book BEATS the certified corridor pair book, exactly. -/
theorem certified_floor_beats_corridor_pair :
    marginPairCertified < deltaKappa certifiedConstants := by
  unfold deltaKappa marginPairCertified certifiedConstants; norm_num

theorem certified_mu0_ge_two : 2 ≤ mu0Final certifiedConstants := by
  unfold mu0Final deltaKappa certifiedConstants; norm_num

theorem certified_cMass_ge_one : 1 ≤ cMass certifiedConstants := by
  unfold cMass mu0Final deltaKappa certifiedConstants; norm_num

end YangMills
