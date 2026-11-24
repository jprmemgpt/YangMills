/-
PROVENANCE: R222 THE-L3b-INVOLUTION-ZERO (Tue 2026-11-24). The sixth of
the seven named windows of the R1 route (YangMills v1.4,
JacobiAnchors.lean) taken to the battery: the involution zero
`routeL3b`,
  ∑' p : OddPar, latF q p.1 = 0   for 0 < q < 1,
proved by pairing every odd lattice point against its own reflection:
the swap (u,v) ↦ (v,u) is a fixed-point-free involution of the odd
book (a fixed point needs u = v, forcing u + v = 2u even — impossible
on OddPar), opposite-parity coordinates give opposite signs, the same
quadratic form gives the same magnitude, and each pair cancels
exactly. An infinite book with infinitely many nonzero entries that
counts nothing.

PAPER ROUTE (pre-registered in the R1 candidate, executed here):
  ∑' p : OddPar, latF q p.1
  = ∑' x : ℤ × ℤ, O.indicator (latF q) x     [tsum_subtype, the L3a defeq mating: the odd book IS its slice]
  = ∑' x, O.indicator (latF q) (Prod.swap x) [Equiv.tsum_eq along Equiv.prodComm: a reindex, honest for every filter]
  = ∑' x, -O.indicator (latF q) x            [pointwise antisymmetry, the sign heart]
  = -(∑' x, O.indicator (latF q) x)           [tsum_neg]
  — so S = -S and S = 0.                       [linear arithmetic]

THE SIGN HEART: on the odd book the two coordinates carry opposite
parity (omega closes |u| + |v| ≡ u + v ≡ 1 mod 2), so
(-1)^|u| = -(-1)^|v| while u² + v² = v² + u²: the swapped summand is
the negated summand, entry by entry.
THE ZERO HEART: the whole derivation is UNCONDITIONAL — it never uses
summability or 0 < q < 1, because in the swap the book carries its own
domination; the hypotheses of routeL3b are carried for the house's
sake and unused by the proof. The pendulum has no rest position.

STATUS: compiled green in-sandbox against the pinned triplet (Mathlib
31ce06eaadf4a200c0e1407c5f10953cf606b8f8, lake 5.0.0, lean v4.37.0-rc1),
with the R221 L3a certificate reproduced green (3,538 jobs) against
the fresh cache before any new math crossed it — this window the whole
rebuild ran through the banked one-command snapshot script (Papa's
idea, field-tested here).

DROP-IN NOTE: with this window green, the hypothesis `h3b : routeL3b`
of `anchorA_of_route` (JacobiAnchors.lean) is discharged by
`routeL3b_proved`; with L1a, L1b, L2, L2b and L3a already paid the R1
assembly rests on SEVEN named windows of which SIX are proved and ONE
remains (L4). The last pair is broken; one stone stands.

SCOPE NOTE: this module certifies THIS ARITHMETIC — one classical
Jacobi theta cancellation, the odd-parity half of one lattice sum
vanishing by paired reflection. It proves nothing about physical
four-dimensional Yang–Mills theory and claims no Clay Millennium
result. Bench FROZEN AT 100.0, the crossing never claimed.
-/

import Mathlib.Topology.Algebra.InfiniteSum.Ring
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Analysis.Normed.Group.InfiniteSum
import YangMills.DualBook.JacobiAnchors
import YangMills.DualBook.JacobiAnchorsL1a
import YangMills.DualBook.JacobiAnchorsL1b
import YangMills.DualBook.JacobiAnchorsL2
import YangMills.DualBook.JacobiAnchorsL2b
import YangMills.DualBook.JacobiAnchorsL3a

/-!
# R222: the involution zero (L3b)

The odd-parity book of the mixed lattice sum vanishes: every entry
pairs with its own reflection under `(u, v) ↦ (v, u)`, the two signs
oppose by parity, the two magnitudes agree by symmetry of the
quadratic form, and the book counts nothing — infinitely many nonzero
entries, total zero.
-/

namespace YangMills.DualBook

open Filter Topology

/-! ## The sign receipt, restated private (the L2b original does not cross modules) -/

/-- A sign of ±1 only knows the parity: `(-1)^n = (-1)^(n % 2)`, by
div-mod decomposition and `neg_one_sq`. (Nat.Even destructures as
`k + k` in this Mathlib; `two_mul` is the monoid law, not the
additive rewrite.) -/
private theorem neg_one_pow_mod (n : ℕ) :
    (-1 : ℝ) ^ n = (-1 : ℝ) ^ (n % 2) := by
  rcases Nat.even_or_odd n with ⟨k, hk⟩ | ⟨k, hk⟩
  · rw [show n % 2 = 0 by omega, pow_zero, hk]
    first
    | rw [pow_mul, neg_one_sq, one_pow]
    | rw [show k + k = 2 * k by ring, pow_mul, neg_one_sq, one_pow]
  · rw [show n % 2 = 1 by omega, pow_one, hk, pow_add, pow_one]
    first
    | rw [pow_mul, neg_one_sq, one_pow, one_mul]
    | rw [show k + k = 2 * k by ring, pow_mul, neg_one_sq, one_pow, one_mul]

/-! ## The sign heart: on the odd book, the swap negates the summand -/

/-- THE SIGN HEART: on the odd book the swapped summand is the
negated summand — the coordinates carry opposite parity (the
natAbs-bridge is omega-closed), so the signs oppose, and the exponent
is symmetric under `add_comm`. -/
private theorem latF_swap_neg (q : ℝ) (x : ℤ × ℤ) (hx : (x.1 + x.2) % 2 = 1) :
    latF q (Prod.swap x) = -latF q x := by
  have hb : (x.1.natAbs + x.2.natAbs) % 2 = 1 := by omega
  show (-1 : ℝ) ^ (x.1.natAbs) * q ^ ((x.2 * x.2 + x.1 * x.1).toNat)
      = -((-1 : ℝ) ^ (x.2.natAbs)
          * q ^ ((x.1 * x.1 + x.2 * x.2).toNat))
  rw [← add_comm (x.1 * x.1) (x.2 * x.2)]
  by_cases h1 : x.1.natAbs % 2 = 0
  · have h2 : x.2.natAbs % 2 = 1 := by omega
    have e1 : (-1 : ℝ) ^ (x.1.natAbs) = 1 := by rw [neg_one_pow_mod, h1, pow_zero]
    have e2 : (-1 : ℝ) ^ (x.2.natAbs) = -1 := by rw [neg_one_pow_mod, h2, pow_one]
    rw [e1, e2]
    ring
  · have h2 : x.1.natAbs % 2 = 1 := by omega
    have h3 : x.2.natAbs % 2 = 0 := by omega
    have e1 : (-1 : ℝ) ^ (x.1.natAbs) = -1 := by rw [neg_one_pow_mod, h2, pow_one]
    have e2 : (-1 : ℝ) ^ (x.2.natAbs) = 1 := by rw [neg_one_pow_mod, h3, pow_zero]
    rw [e1, e2]
    ring

/-- The pointwise antisymmetry of the odd slice: the reflected slice
is the negated slice, at EVERY point — members swap-and-negate,
non-members stay zero. -/
private theorem odd_slice_swap (q : ℝ) (x : ℤ × ℤ) :
    {x : ℤ × ℤ | (x.1 + x.2) % 2 = 1}.indicator (latF q) (Prod.swap x)
      = -{x : ℤ × ℤ | (x.1 + x.2) % 2 = 1}.indicator (latF q) x := by
  by_cases hx : (x.1 + x.2) % 2 = 1
  · have hs : (x.2 + x.1) % 2 = 1 := by omega
    rw [Set.indicator_of_mem hs (latF q), Set.indicator_of_mem hx (latF q)]
    exact latF_swap_neg q x hx
  · have hs : (x.2 + x.1) % 2 ≠ 1 := by omega
    rw [Set.indicator_of_notMem hs (latF q), Set.indicator_of_notMem hx (latF q)]
    ring

/-! ## The involution zero window itself -/

/-- WINDOW L3b, the main identity: the odd-parity book counts
nothing. The derivation is unconditional — no summability, no nome
positivity — because the swap carries its own cancellation: the book
is reindexed along its own reflection, meets itself negated, and the
only number equal to its own negative is zero. -/
theorem oddPar_tsum_zero (q : ℝ) :
    ∑' p : OddPar, latF q p.1 = 0 := by
  have hID : (∑' p : OddPar, latF q p.1)
      = ∑' x : ℤ × ℤ, {x : ℤ × ℤ | (x.1 + x.2) % 2 = 1}.indicator (latF q) x :=
    tsum_subtype {x : ℤ × ℤ | (x.1 + x.2) % 2 = 1} (latF q)
  rw [hID]
  have h1 : (∑' x : ℤ × ℤ, {x : ℤ × ℤ | (x.1 + x.2) % 2 = 1}.indicator (latF q) x)
      = (∑' x : ℤ × ℤ,
          {x : ℤ × ℤ | (x.1 + x.2) % 2 = 1}.indicator (latF q) (Prod.swap x)) :=
    (Equiv.tsum_eq (Equiv.prodComm ℤ ℤ) _).symm
  have hneg : (∑' x : ℤ × ℤ, {x : ℤ × ℤ | (x.1 + x.2) % 2 = 1}.indicator (latF q) x)
      = -(∑' x : ℤ × ℤ, {x : ℤ × ℤ | (x.1 + x.2) % 2 = 1}.indicator (latF q) x) := by
    calc (∑' x : ℤ × ℤ, {x : ℤ × ℤ | (x.1 + x.2) % 2 = 1}.indicator (latF q) x)
        = (∑' x : ℤ × ℤ,
            {x : ℤ × ℤ | (x.1 + x.2) % 2 = 1}.indicator (latF q) (Prod.swap x)) :=
        h1
      _ = (∑' x : ℤ × ℤ,
          -{x : ℤ × ℤ | (x.1 + x.2) % 2 = 1}.indicator (latF q) x) :=
        tsum_congr fun x => odd_slice_swap q x
      _ = -(∑' x : ℤ × ℤ, {x : ℤ × ℤ | (x.1 + x.2) % 2 = 1}.indicator (latF q) x) :=
        tsum_neg
  linarith

/-- WINDOW L3b, PROVED: the involution zero of the R1 route, now an
unconditional theorem (the proof itself never needed the nome
hypotheses; they are carried for the house's sake). Feed this to
`anchorA_of_route` to discharge `h3b`: six of the seven named windows
paid, one remaining. -/
theorem routeL3b_proved : routeL3b :=
  fun _ _ _ => oddPar_tsum_zero _

/-- DROP-IN RECEIPT (TYPE-CHECKED HERE): with L1a, L1b, L2, L2b, L3a
and L3b all proved, `anchorA_of_route` runs on its remaining ONE named
window (L4) — six of the seven hypotheses discharged by green modules,
the last pair broken, one stone standing, nothing hidden. -/
theorem anchorA_of_route_six_paid (h4 : routeL4) : jacobiAnchorA :=
  anchorA_of_route routeL1a_proved routeL1b_proved routeL2_proved
    routeL2b_proved routeL3a_proved routeL3b_proved h4
