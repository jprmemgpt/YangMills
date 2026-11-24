/-
PROVENANCE: R223 THE-L4-SAMEPAR-REINDEX (Tue 2026-11-24). The seventh and
final of the seven named windows of the R1 route (YangMills v1.4,
JacobiAnchors.lean) taken to the battery: the same-parity reindex
`routeL4`,
  ∑' p : SamePar, latF q p.1 = ∑' p : ℤ × ℤ, latS q p   for 0 < q < 1,
proved by carrying the even book along the linear bijection
(a, b) ↦ (u, v) = (a + b, a − b), whose inverse (u, v) ↦ ((u+v)/2,
(u−v)/2) is integral exactly because u ≡ v (mod 2) on SamePar. Along
the reindex u² + v² = 2(a² + b²) — the nome DOUBLES inside the
exponent itself — and (−1)^|v| = (−1)^|a+b| because a − b and a + b
share a parity. The even book was never half the book: it is the full
lattice in a rotated frame.

PAPER ROUTE (pre-registered in the R1 candidate, executed here):
  ∑' p : SamePar, latF q p.1
  = ∑' ab : ℤ × ℤ, latF q ((ab.1 + ab.2, ab.1 − ab.2))  [Equiv.tsum_eq along sameParEquiv: a reindex, honest for every filter]
  = ∑' ab : ℤ × ℤ, latS q ab                            [tsum_congr + the pointwise heart]

THE POINTWISE HEART: latF q (a+b, a−b) = latS q (a,b) entry by entry:
the sign survives the change of frame ((−1)^|a−b| = (−1)^|a+b| by
neg_one_pow_mod + the omega parity bridge, STANDALONE haves, never a
chained rw of nested %2 patterns — the R222 trap receipt), and the
exponent is the ring identity (a+b)² + (a−b)² = 2(a² + b²).
THE BORDER, NAMED IN THE OPEN: the derivation is UNCONDITIONAL — the
reindex and the pointwise heart never touch summability or 0 < q < 1,
so the hypotheses of routeL4 ride carried-unused, for the house's
sake. The substitution is free because either book is the other book.

WITH THIS WINDOW GREEN THE ASSEMBLY CLOSES: feeding routeL4_proved to
anchorA_of_route alongside the six paid windows discharges the LAST
hypothesis, and jacobiAnchorA — theta3 q * theta4 q = theta4 (q*q)^2
for every 0 < q < 1 — falls UNCONDITIONAL. Seven of seven stones
paid; the_route is proved; nothing else is claimed by it.

STATUS: compiled green in-sandbox against the pinned triplet (Mathlib
31ce06eaadf4a200c0e1407c5f10953cf606b8f8, lake 5.0.0, lean
v4.37.0-rc1), with the R222 L3b certificate reproduced green (3,540
jobs) through the banked one-command snapshot script (second field
test) before any new math crossed it.

SCOPE NOTE: this module certifies THIS ARITHMETIC — one classical
Jacobi theta identity, the same-parity half of one lattice sum
reindexed onto the doubled-nome lattice. It proves nothing about
physical four-dimensional Yang–Mills theory and claims no Clay
Millennium result. Bench FROZEN AT 100.0, the crossing never claimed.
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
import YangMills.DualBook.JacobiAnchorsL3b

/-!
# R223: the same-parity reindex (L4, the last stone)

The even-parity book of the mixed lattice sum is the doubled-nome
lattice sum: every entry rides the linear equivalence
`(a, b) ↦ (a + b, a − b)`, the sign survives the change of frame,
and the doubled nome appears inside the exponent. With L4 paid, the
seven-window assembly `anchorA_of_route` has no hypothesis left and
`jacobiAnchorA` is unconditional.
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

/-! ## The frame equivalence: the even book is the full lattice in rotated coordinates -/

/-- THE FRAME: `(a, b) ↦ (a + b, a − b)` carries `ℤ × ℤ` bijectively
onto the same-parity book. Membership: `(a + b) + (a − b) = 2a`. The
inverse `(u, v) ↦ ((u+v)/2, (u−v)/2)` is integral exactly because
`u ≡ v (mod 2)` on the even book; its left inverse is clean on ALL of
`ℤ × ℤ` because `2a` and `2b` are always even. -/
private def sameParEquiv : ℤ × ℤ ≃ {x : ℤ × ℤ // (x.1 + x.2) % 2 = 0} where
  toFun ab := ⟨(ab.1 + ab.2, ab.1 - ab.2), by omega⟩
  invFun p := ((p.1.1 + p.1.2) / 2, (p.1.1 - p.1.2) / 2)
  left_inv := by
    rintro ⟨a, b⟩
    simp only [Prod.mk.injEq]
    omega
  right_inv := by
    rintro ⟨⟨u, v⟩, huv⟩
    apply Subtype.ext
    simp only [Prod.mk.injEq]
    omega

/-! ## The pointwise heart: the sign survives the frame, the nome doubles in the exponent -/

/-- THE POINTWISE HEART: one lattice point of the even book, written in
the rotated frame, IS one summand of the doubled-nome book: the sign
survives the change of frame (`a − b` and `a + b` share a parity), and
the exponent is the ring identity `(a+b)² + (a−b)² = 2(a² + b²)`. The
R222 trap receipt respected: each sign is its own STANDALONE have,
never a chained rewrite through nested `%2` patterns. -/
private theorem latF_pair_eq_latS (q : ℝ) (a b : ℤ) :
    latF q (a + b, a - b) = latS q (a, b) := by
  have e1 : (-1 : ℝ) ^ ((a - b).natAbs) = (-1 : ℝ) ^ ((a + b).natAbs) := by
    have hA : (-1 : ℝ) ^ ((a - b).natAbs) = (-1 : ℝ) ^ ((a - b).natAbs % 2) :=
      neg_one_pow_mod _
    have hB : (-1 : ℝ) ^ ((a + b).natAbs) = (-1 : ℝ) ^ ((a + b).natAbs % 2) :=
      neg_one_pow_mod _
    have hm : (a - b).natAbs % 2 = (a + b).natAbs % 2 := by omega
    rw [hA, hm, ← hB]
  have e2 : q ^ (((a + b) * (a + b) + (a - b) * (a - b)).toNat)
      = q ^ ((2 * (a * a + b * b)).toNat) := by
    have hq : (a + b) * (a + b) + (a - b) * (a - b) = 2 * (a * a + b * b) := by ring
    rw [hq]
  show (-1 : ℝ) ^ ((a - b).natAbs)
      * q ^ (((a + b) * (a + b) + (a - b) * (a - b)).toNat)
      = (-1 : ℝ) ^ ((a + b).natAbs) * q ^ ((2 * (a * a + b * b)).toNat)
  rw [e1, e2]

/-! ## The last window itself -/

/-- WINDOW L4, the main identity: the even book is the doubled-nome
book. The derivation is unconditional — the reindex along an Equiv
is honest for every filter, and the pointwise heart never asks for
convergence — so the nome hypotheses ride carried-unused, for the
house's sake. -/
theorem samePar_tsum_reindex (q : ℝ) :
    ∑' p : SamePar, latF q p.1 = ∑' p : ℤ × ℤ, latS q p := by
  have hE1 : (∑' p : SamePar, latF q p.1)
      = ∑' ab : ℤ × ℤ, latF q ((sameParEquiv ab : SamePar) : ℤ × ℤ) :=
    (Equiv.tsum_eq sameParEquiv (fun p : SamePar => latF q p.1)).symm
  rw [hE1]
  exact tsum_congr (fun ab => latF_pair_eq_latS q ab.1 ab.2)

/-- WINDOW L4, PROVED: the same-parity reindex of the R1 route, now an
unconditional theorem (the proof itself never needed the nome
hypotheses; they are carried for the house's sake). Feed this to
`anchorA_of_route` to discharge `h4`: the LAST stone, seven of seven. -/
theorem routeL4_proved : routeL4 :=
  fun _ _ _ => samePar_tsum_reindex _

/-- DROP-IN RECEIPT (TYPE-CHECKED HERE): with all seven windows paid
(L1a, L1b, L2, L2b, L3a, L3b, L4), `anchorA_of_route` has NO
hypothesis remaining, and `jacobiAnchorA` —
theta3 q * theta4 q = theta4 (q * q) ^ 2 for every 0 < q < 1 —
is UNCONDITIONAL. Seven of seven stones paid on the R1 route; the
conditional assembly is a theorem with nothing left to ask. -/
theorem anchorA_of_route_seven_paid : jacobiAnchorA :=
  anchorA_of_route routeL1a_proved routeL1b_proved routeL2_proved
    routeL2b_proved routeL3a_proved routeL3b_proved routeL4_proved

end YangMills.DualBook
