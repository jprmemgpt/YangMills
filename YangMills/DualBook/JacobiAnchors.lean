/-
PROVENANCE: R1 candidate — the Jacobi anchor A route decomposition, window R214
(THE FIRST DIG, Tue 2026-11-24). Typed from the certified retired source
(YangMills v1.4, DualBookAssembly.lean, the byte-faithful anchor statement
copied below). The route decomposes the anchor into SEVEN well-scoped named
windows (L1a, L1b, L2, L2b, L3a, L3b, L4), each with its paper proof
pre-registered in its doc-string, and proves the ASSEMBLY
`anchorA_of_route` conditional on the seven, in the v1.4 house pattern:
explicit hypotheses, never dressed as theorems until each battery passes.

STATUS: CANDIDATE — NOT GREEN. The lake battery has NOT run on this file.
Nothing in this file is claimed proved except the conditional assembly,
whose proof is short and will be checked by the battery before any claim.
The seven windows are the next seven problems, one window per code window,
on Papa's standing order ("just the next problem in front of us").

SCOPE NOTE: this module certifies THIS ARITHMETIC — the route decomposition
of a classical Jacobi theta identity. It proves nothing about physical
four-dimensional Yang–Mills theory and claims no Clay Millennium result.

THE PAPER ROUTE (pre-registered, checked three ways: coefficient check
through q^10, both asymptotic endpoints, and an independent Euler-product
referee cross-check shown at the bottom):

  theta3 q * theta4 q                      (the anchor's left side)
  = theta3z q * theta4z q                  [L1a, L1b: the integer bridges]
  = ∑' p : ℤ × ℤ, latF q p                [L2: the mixed Cauchy product]
  = (∑' SamePar, latF) + (∑' OddPar, latF)  [L3a: the parity split]
  = (∑' SamePar, latF) + 0                [L3b: the involution —
                                            (u,v) ↔ (v,u) pairs every
                                            opposite-parity lattice point
                                            with a partner carrying the
                                            negated sign and the same
                                            modulus; no fixed points,
                                            since u = v forces the parity
                                            even; the shell cancels]
  = ∑' p : ℤ × ℤ, latS q p                [L4: the same-parity sublattice
                                            reindexes (a,b) ↦ (a+b, a−b);
                                            u,v same parity matches ℤ²
                                            bijectively; (−1)^(a+b) = (−1)^u
                                            and u² + v² = 2(a² + b²)]
  = theta4z (q * q) ^ 2                    [L2b: the square Cauchy product]
  = theta4 (q * q) ^ 2                     [L1b at the doubled nome]

THE REFEREE CROSS-CHECK (the second route, an Euler-product confirmation,
never a proof substitute): by the Jacobi triple product
  θ₃(q)  = ∏ n ≥ 1 (1 − q^{2n})(1 + q^{2n−1})²
  θ₄(q)  = ∏ n ≥ 1 (1 − q^{2n})(1 − q^{2n−1})²       [with the minus sign]
so θ₃(q)·θ₄(q) = ∏ (1 − q^{2n})² (1 − q^{4n−2})², while
  θ₄(q²)² = ∏ (1 − q^{4n})² (1 − q^{4n−2})⁴,
and splitting (1 − q^{2n}) into the (1 − q^{4n}) and (1 − q^{4n−2}) parts
makes the two products coincide term by term. Certified on paper here;
formalizing infinite products is a LATER window and is NOT part of R1.
-/
import YangMills.DualBook.ThetaConstants
import YangMills.DualBook.DualBookAssembly
import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.Topology.Algebra.InfiniteSum.Ring
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-!
# The Jacobi anchor A route (R1 candidate, the seven named windows)

This file decomposes `jacobiAnchorA` into seven named windows and proves
the conditional assembly `anchorA_of_route`. The paper proof of each window
rides its doc-string. The battery judges before anyone speaks: nothing is
promoted, packaged, or claimed green until `lake build` passes on the
shipping machine (runbook step 4 remains the notary).
-/

namespace YangMills.DualBook

/-! ## The integer-form theta constants and the lattice summands -/

/-- The theta-3 constant as an integer sum (even function via `natAbs`):
`theta3z q = ∑' z : ℤ, q ^ (|z|²)`. For `0 < q < 1` this is the classical
`θ₃(q) = Σ_{n ∈ ℤ} q^{n²}`, and `L1a` bridges it to the house `theta3`. -/
noncomputable def theta3z (q : ℝ) : ℝ := ∑' z : ℤ, q ^ (z.natAbs ^ 2)

/-- The theta-4 constant as an integer sum (even via `natAbs` on both the
sign and the exponent): `theta4z q = ∑' z : ℤ, (−1)^|z| · q ^ (|z|²)`.
For `0 < q < 1` this is the classical `θ₄(q) = Σ_{n ∈ ℤ} (−1)^n q^{n²}`,
and `L1b` bridges it to the house `theta4`. -/
noncomputable def theta4z (q : ℝ) : ℝ :=
  ∑' z : ℤ, (-1 : ℝ) ^ (z.natAbs) * q ^ (z.natAbs ^ 2)

/-- The mixed lattice summand of the Cauchy product `θ₃·θ₄`:
`latF q (m, n) = (−1)^|n| · q^{|m² + n²|}`. The `toNat` is the identity on
the nonnegative integer `m² + n²`; the paper proofs carry that one-line
`Int.toNat_of_nonneg`. -/
noncomputable def latF (q : ℝ) (p : ℤ × ℤ) : ℝ :=
  (-1 : ℝ) ^ (p.2.natAbs) * q ^ ((p.1 * p.1 + p.2 * p.2).toNat)

/-- The doubled-nome lattice summand of `θ₄(q²)²`:
`latS q (a, b) = (−1)^{|a+b|} · q^{|2(a² + b²)|}`. -/
noncomputable def latS (q : ℝ) (p : ℤ × ℤ) : ℝ :=
  (-1 : ℝ) ^ ((p.1 + p.2).natAbs) * q ^ ((2 * (p.1 * p.1 + p.2 * p.2)).toNat)

/-- The same-parity sublattice: lattice points with even coordinate sum.
`L4` reindexes this onto `ℤ × ℤ` by `(a,b) ↦ (a+b, a−b)`. -/
def SamePar : Type := {p : ℤ × ℤ // (p.1 + p.2) % 2 = 0}

/-- The opposite-parity part of the lattice: odd coordinate sum.
`L3b` proves its `latF`-sum vanishes under the `(u,v) ↔ (v,u)` involution. -/
def OddPar : Type := {p : ℤ × ℤ // (p.1 + p.2) % 2 = 1}

/-! ## The seven named windows (each with its pre-registered paper proof) -/

/-- Window L1a: the theta-3 bridge. `theta3 q = theta3z q` on `0 < q < 1`.

PAPER PROOF: the house `theta3 q = 1 + 2 ∑' n : ℕ, q^((n+1)²)` and the
integer sum splits over `ℤ = {0} ⊔ {n+1} ⊔ {−(n+1)}`: both tails agree
because `|−(n+1)|² = (n+1)²` (natAbs), giving `theta3z q =
q^0 + 2 ∑' n : ℕ, q^((n+1)²)`; summability rides `theta3Core_summable`
(both tails are the same nonnegative tail) and `tsum` reindexing along the
explicit `Option ℕ ⊕ ℕ`-shaped bijection of `ℤ` (or `tsum_subtype` plus a
`Fintype` fold for the `0` coordinate). -/
def routeL1a : Prop :=
  ∀ q, 0 < q → q < 1 → theta3 q = theta3z q

/-- Window L1b: the theta-4 bridge. `theta4 q = theta4z q` on `0 < q < 1`.

PAPER PROOF: as L1a, with the sign riding along: `(−1)^(n+1)` in the house
tail matches `(−1)^|n+1|` on both mirrored coordinates because
`|−n−1| = n+1`; summability rides `theta4Core_summable`. Applied at the
doubled nome (with `0 < q² < 1` from the domain facts), the same bridge
gives `theta4 (q*q) = theta4z (q*q)`. -/
def routeL1b : Prop :=
  ∀ q, 0 < q → q < 1 → theta4 q = theta4z q

/-- Window L2: the mixed Cauchy product.
`theta3z q * theta4z q = ∑' p : ℤ × ℤ, latF q p` on `0 < q < 1`.

PAPER PROOF: absolute convergence of both integer sums (dominated by the
`q^(|z|)`-geometric series, as in `theta3Core_summable`), then the
`tsum_mul_tsum` Cauchy lift to `ℤ × ℤ` with the product summand
`q^{|m²|} · (−1)^|n| · q^{|n²|} = latF q (m, n)` (exponents add:
`|m²| + |n²| = |m² + n²|` for the nonnegative integer involved). -/
def routeL2 : Prop :=
  ∀ q, 0 < q → q < 1 →
    theta3z q * theta4z q = ∑' p : ℤ × ℤ, latF q p

/-- Window L2b: the square Cauchy product at the doubled nome.
`theta4z (q * q) ^ 2 = ∑' p : ℤ × ℤ, latS q p` on `0 < q < 1`.

PAPER PROOF: as L2 with both factors `theta4z (q*q)`: the Cauchy summand
is `(−1)^{|a|} (q²)^{|a²|} · (−1)^{|b|} (q²)^{|b²|} =
(−1)^{|a|+|b|} q^{2|a²+b²|}`, and `|a| + |b| ≡ a + b (mod 2)` while
`2(a²+b²) ≥ 0` already, so the summand is `latS` "up to the sign-parity
identity `(−1)^{|a|+|b|} = (−1)^{|a+b|}`, a one-line parity lemma. -/
def routeL2b : Prop :=
  ∀ q, 0 < q → q < 1 →
    theta4z (q * q) ^ 2 = ∑' p : ℤ × ℤ, latS q p

/-- Window L3a: the parity split of the mixed lattice sum.
`∑' p : ℤ × ℤ, latF q p =
   (∑' p : SamePar, latF q p.1) + ∑' p : OddPar, latF q p.1`
on `0 < q < 1`.

PAPER PROOF: `ℤ × ℤ` is the disjoint union of the same-parity and
odd-parity sublattices (`(u + v) % 2` decides); summability of the whole
lattice sum (L2's domination) forces summability of each part, and
`tsum_add`/`tsum_subtype` along the `Sum`-shaped partition of the index
set splits the sum. -/
def routeL3a : Prop :=
  ∀ q, 0 < q → q < 1 →
    ∑' p : ℤ × ℤ, latF q p
      = (∑' p : SamePar, latF q p.1) + ∑' p : OddPar, latF q p.1

/-- Window L3b: the involution zero. The odd-parity part vanishes:
`∑' p : OddPar, latF q p.1 = 0` on `0 < q < 1`.

PAPER PROOF: the map `(u, v) ↦ (v, u)` is a fixed-point-free involution of
`OddPar` (a fixed point needs `u = v`, forcing `u + v = 2u` even, but
`OddPar` points have odd coordinate sum). Each orbit `{(u,v), (v,u)}` has
opposite-parity coordinates, so `(−1)^{|u|} = −(−1)^{|v|}` while
`|u²+v²| = |v²+u²|`: the two summands cancel exactly. Summing over orbits
(the involution induces the pairing of the summable family) gives zero.
Formalizing via the orbit `Equiv` and `tsum` cancelation on even/odd
partitions of the index. -/
def routeL3b : Prop :=
  ∀ q, 0 < q → q < 1 → ∑' p : OddPar, latF q p.1 = 0

/-- Window L4: the same-parity reindex to the doubled-nome lattice.
`∑' p : SamePar, latF q p.1 = ∑' p : ℤ × ℤ, latS q p` on `0 < q < 1`.

PAPER PROOF: the linear change of variables `(a, b) ↦ (u, v) = (a+b, a−b)`
is a bijection `ℤ × ℤ → SamePar` (inverse `(u+v)/2, (u−v)/2`, integral
exactly because `u ≡ v (mod 2)` on `SamePar`); along it,
`u² + v² = 2(a² + b²)` (expand and cancel) and `(−1)^{|u|} = (−1)^{|a+b|}`
(parity: `u = a + b`). Reindexing the absolutely convergent sublattice sum
along this `Equiv` gives the identity. -/
def routeL4 : Prop :=
  ∀ q, 0 < q → q < 1 →
    ∑' p : SamePar, latF q p.1 = ∑' p : ℤ × ℤ, latS q p

/-! ## The conditional assembly (the proved part of R1) -/

/-- Domain facts for the doubled nome, local to this file (the assembly's
only arithmetic). -/
private theorem sq_mem_ball' {q : ℝ} (hq0 : 0 < q) (hq1 : q < 1) :
    0 < q * q ∧ q * q < 1 := by
  refine ⟨by positivity, ?_⟩
  rw [← sq]
  exact pow_lt_one₀ hq0.le hq1 (by omega)

/-- THE R1 ASSEMBLY: the seven named windows together imply
`jacobiAnchorA`. This is the v1.4 conditional-assembly pattern applied to
the anchor itself: the short algebraic spine is PROVED HERE, and each of
the seven windows, once its own battery passes, drops in as a hypothesis
until no hypothesis remains and the anchor is UNCONDITIONAL. -/
theorem anchorA_of_route (h1a : routeL1a) (h1b : routeL1b) (h2 : routeL2)
    (h2b : routeL2b) (h3a : routeL3a) (h3b : routeL3b) (h4 : routeL4) :
    jacobiAnchorA := by
  intro q hq0 hq1
  have hqq := sq_mem_ball' hq0 hq1
  calc theta3 q * theta4 q
      = theta3z q * theta4z q := by rw [h1a q hq0 hq1, h1b q hq0 hq1]
    _ = ∑' p : ℤ × ℤ, latF q p := h2 q hq0 hq1
    _ = (∑' p : SamePar, latF q p.1) + ∑' p : OddPar, latF q p.1 :=
          h3a q hq0 hq1
    _ = (∑' p : SamePar, latF q p.1) + 0 := by rw [h3b q hq0 hq1]
    _ = ∑' p : SamePar, latF q p.1 := (add_zero _)
    _ = ∑' p : ℤ × ℤ, latS q p := h4 q hq0 hq1
    _ = theta4z (q * q) ^ 2 := (h2b q hq0 hq1).symm
    _ = theta4 (q * q) ^ 2 := by rw [h1b (q * q) hqq.1 hqq.2]

end YangMills.DualBook
