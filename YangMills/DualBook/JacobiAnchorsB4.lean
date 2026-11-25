/-
PROVENANCE: R228 THE-B4-SAMEPAR-REINDEX (Tue 2026-11-24). The fourth of
the five named windows of the R2 candidate (JacobiAnchorsB.lean) taken
to the battery: the same-parity reindex `routeB4`,
  ∑' p : SamePar, latU q p.1 = ∑' p : ℤ × ℤ, latV q p   for 0 < q < 1,
proved by carrying the even book along the linear bijection
(a, b) ↦ (u, v) = (a + b, a − b), whose inverse (u, v) ↦ ((u+v)/2,
(u−v)/2) is integral exactly because u ≡ v (mod 2) on SamePar. Along
the reindex u² + v² = 2(a² + b²) — the nome DOUBLES inside the
exponent itself, which is the whole content: latU q (a+b, a−b) =
latV q (a, b) pointwise, the doubled-nome lattice born from the
theta-3 square's even book in a rotated frame. B3 paid the merge that
produced this book; B4 pays its reindex; B5 will factor it back into
a product.

PAPER ROUTE (pre-registered in the R2 candidate, executed here):
  ∑' p : SamePar, latU q p.1
  = ∑' ab : ℤ × ℤ, latU q ((sameParEquiv ab : SamePar) : ℤ × ℤ)  [Equiv.tsum_eq along sameParEquiv: a reindex, honest for every filter]
  = ∑' ab : ℤ × ℤ, latV q ab                                    [tsum_congr + the pointwise heart]

THE POINTWISE HEART: latU q (a+b, a−b) = latV q (a,b) entry by
entry, and it is UNSIGNED work — latU carries no sign, so this window
needs none of the sign-parity machinery of L4; the entire content is
the exponent: (a+b)² + (a−b)² = 2(a² + b²) by ring, the .toNat
doubling by Int.toNat_add on the nonnegative family, and then
q^(2N) = (q·q)^N. THE REWRITE RECEIPT (trace-probed this window):
this vintage's `two_mul` runs `2 * n = n + n` (the 2*n-DRIVEN
direction), so the exponent doubling rides `pow_add` + `mul_pow`
(q^(t+t) = q^t · q^t and (q·q)^t = q^t · q^t) and never asks two_mul
for the reversed ride. The frame Equiv itself is carried as a private
verbatim twin of the R223 receipt (the L4 original is private and
does not cross modules; each window carries its own copy, the B3
precedent for cross-module private receipts).

THE BORDER, NAMED IN THE OPEN: the derivation is UNCONDITIONAL — the
reindex along an Equiv is honest for every filter and the pointwise
heart never touches summability or 0 < q < 1, so the hypotheses of
routeB4 ride carried-unused, for the house's sake. The substitution is
free because either book is the other book.

WITH THIS WINDOW GREEN THE ASSEMBLY STANDS AT FOUR OF FIVE PAID:
feeding routeB4_proved to `anchorB_of_route_two_paid` (B3's export)
discharges `h4`, and the assembly waits on B5 (the doubled-nome
factorization) alone — ONE named window remains between this stone
and `jacobiAnchorB` falling unconditionally.

STATUS: compiled green in-sandbox against the pinned triplet (Mathlib
31ce06eaadf4a200c0e1407c5f10953cf606b8f8, lake 5.0.0, lean
v4.37.0-rc1), with the R227 B3 certificate reproduced green (3,540
jobs) through the banked one-command snapshot script before any new
math crossed it.

SCOPE NOTE: this module certifies THIS ARITHMETIC — one classical
Jacobi theta identity, the same-parity book of the theta-3 square
reindexed onto the doubled-nome lattice. It proves nothing about
physical four-dimensional Yang–Mills theory and claims no Clay
Millennium result. Bench FROZEN AT 100.0, the crossing never claimed.
-/

import Mathlib.Topology.Algebra.InfiniteSum.Ring
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Analysis.Normed.Group.InfiniteSum
import YangMills.DualBook.JacobiAnchors
import YangMills.DualBook.JacobiAnchorsB
import YangMills.DualBook.JacobiAnchorsB2b
import YangMills.DualBook.JacobiAnchorsB3

/-!
# R228: the same-parity reindex (B4, the fourth stone)

The even-parity book of the theta-3 square is the doubled-nome
lattice sum: every entry rides the linear equivalence
`(a, b) ↦ (a + b, a − b)`, the nome doubles inside the exponent, and
the book that B3's parity merge bought outright is revealed as the
full lattice in a rotated frame. With B4 paid, the five-window
assembly `anchorB_of_route` stands at four of five, waiting on B5
alone.
-/

namespace YangMills.DualBook

open Filter Topology

/-! ## The frame equivalence (a private verbatim twin of the R223 receipt) -/

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

/-! ## The pointwise heart: the nome doubles in the exponent -/

/-- THE POINTWISE HEART: one lattice point of the even book, written
in the rotated frame, IS one summand of the doubled-nome book. There
is no sign to save this time — latU is unsigned — so the whole heart
is the exponent: the ring identity
`(a+b)² + (a−b)² = 2(a² + b²)`, the `.toNat` doubling on the
nonnegative family, and then
`q^(t+t) = q^t · q^t = (q·q)^t` by `pow_add` and `mul_pow`
(the direction-receipt: this vintage's `two_mul` runs `2 * n = n + n`,
so the doubling never asks it for the reversed ride). -/
private theorem latU_pair_eq_latV (q : ℝ) (a b : ℤ) :
    latU q (a + b, a - b) = latV q (a, b) := by
  have hnn : 0 ≤ a * a + b * b :=
    add_nonneg (mul_self_nonneg a) (mul_self_nonneg b)
  have hr : (a + b) * (a + b) + (a - b) * (a - b)
      = 2 * (a * a + b * b) := by ring
  have hexp : ((a + b) * (a + b) + (a - b) * (a - b)).toNat
      = ((a * a + b * b) + (a * a + b * b)).toNat := by
    rw [hr, two_mul]
  show q ^ ((a + b) * (a + b) + (a - b) * (a - b)).toNat
      = (q * q) ^ ((a * a + b * b).toNat)
  rw [hexp, Int.toNat_add hnn hnn, pow_add, mul_pow]

/-! ## The window itself -/

/-- WINDOW B4, the main identity: the even book of the theta-3
square is the doubled-nome book. The derivation is unconditional —
the reindex along an Equiv is honest for every filter, and the
pointwise heart never asks for convergence — so the nome hypotheses
ride carried-unused, for the house's sake. -/
theorem samePar_tsum_reindex_latU (q : ℝ) :
    ∑' p : SamePar, latU q p.1 = ∑' p : ℤ × ℤ, latV q p := by
  have hE1 : (∑' p : SamePar, latU q p.1)
      = ∑' ab : ℤ × ℤ, latU q ((sameParEquiv ab : SamePar) : ℤ × ℤ) :=
    (Equiv.tsum_eq sameParEquiv (fun p : SamePar => latU q p.1)).symm
  rw [hE1]
  exact tsum_congr (fun ab => latU_pair_eq_latV q ab.1 ab.2)

/-- WINDOW B4, PROVED: the same-parity reindex of the R2 route, now
an unconditional theorem (the proof itself never needed the nome
hypotheses; they are carried for the house's sake). Feed this to
`anchorB_of_route_two_paid` (B3's export) to discharge `h4`: four of
the five stones, ONE named window remaining. -/
theorem routeB4_proved : routeB4 :=
  fun _ _ _ => samePar_tsum_reindex_latU _

/-- DROP-IN RECEIPT (TYPE-CHECKED HERE): with B2a, B2b, B3 and B4 all
proved, `anchorB_of_route` runs on its ONE remaining named window
(B5, the doubled-nome factorization): six of the seven hypotheses
discharged by green modules, nothing hidden. The house counting
convention honored: B2a minted `four_paid`, B2b `three_paid`, B3
`two_paid`, and this window's export is `one_paid`. -/
theorem anchorB_of_route_one_paid (h5 : routeB5) : jacobiAnchorB :=
  anchorB_of_route_two_paid routeB4_proved h5

end YangMills.DualBook
