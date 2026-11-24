import YangMills.DualBook.ThetaConstants
import YangMills.DualBook.DualBookAssembly
import YangMills.DualBook.JacobiAnchors
import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.Topology.Algebra.InfiniteSum.Ring
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-!
# The Jacobi anchor B route (R2 candidate, the five named windows)

R224, opened Tue 2026-11-24 on Papa's word ("let's do R2"). This file
decomposes `jacobiAnchorB` — the second anchor, `θ₃(q)² + θ₄(q)² = 2·θ₃(q²)²`
for `0 < q < 1`, byte-faithful from the v1.4 `DualBookAssembly.lean` — into
FIVE named windows, each with its paper proof pre-registered in its
doc-string, plus the two R1 bridges reused as importable standing stones.

The windows reuse the R1 machinery wherever the arithmetic rhymes:
`routeB2a`/`routeB2b` are square-Cauchy factorizations (the R219 receipt),
`routeB3` merges the unsigned and sign-carrying lattices pointwise by
parity (no involution needed — the merge itself kills the odd shell),
`routeB4` reindexes the same-parity sublattice by the R223 `(a,b) ↦ (a+b,a−b)`
change of variables, and `routeB5` factors the doubled-nome lattice sum
back into a product (R219's receipt once more, at the nome `q²`).

STATUS: CANDIDATE — NOT GREEN until the battery passes. Only the short
algebraic spine `anchorB_of_route` is proved here; every window arrives as
an explicit hypothesis in the v1.4 house pattern. When all five drop in,
`jacobiAnchorB` is UNCONDITIONAL and `theta_sum_D1'` loses its last
hypothesis.

SCOPE NOTE: this module certifies THIS ARITHMETIC, the decomposition of a
classical Jacobi theta identity. It proves nothing about physical
four-dimensional Yang–Mills theory and claims no Clay Millennium result.
-/

namespace YangMills.DualBook

/-! ## The anchor-B lattice summands -/

/-- The unsigned lattice summand of the square Cauchy product `θ₃z·θ₃z`:
`latU q (m, n) = q^{|m² + n²|}`. The `toNat` is the identity on the
nonnegative integer `m² + n²`; the window proofs carry the one-line
`Int.toNat_of_nonneg`. -/
noncomputable def latU (q : ℝ) (p : ℤ × ℤ) : ℝ :=
  q ^ ((p.1 * p.1 + p.2 * p.2).toNat)

/-- The sign-carrying lattice summand of the square Cauchy product
`θ₄z·θ₄z`: `latT q (m, n) = (−1)^{|m|+|n|} · q^{|m² + n²|}`. The sign is
carried by the `natAbs` sum, so `|(−1)^{|m|+|n|}| = 1` line by line
(the `abs_neg_one_pow` receipt, R217). -/
noncomputable def latT (q : ℝ) (p : ℤ × ℤ) : ℝ :=
  (-1 : ℝ) ^ (p.1.natAbs + p.2.natAbs) * q ^ ((p.1 * p.1 + p.2 * p.2).toNat)

/-- The doubled-nome lattice summand of `θ₃z (q²)²`:
`latV q (a, b) = (q²)^{|a² + b²|}`. `routeB4` lands here and `routeB5`
factors the sum back into the product. -/
noncomputable def latV (q : ℝ) (p : ℤ × ℤ) : ℝ :=
  (q * q) ^ ((p.1 * p.1 + p.2 * p.2).toNat)

/-! ## The five named windows (each with its pre-registered paper proof) -/

/-- Window B2a: the theta-3 square factorization.
`theta3z q * theta3z q = ∑' p : ℤ × ℤ, latU q p` on `0 < q < 1`.

PAPER PROOF: the Cauchy product of two copies of the integer theta sum.
`theta3z q` is `∑' z : ℤ, q ^ (z.natAbs ^ 2)` (geometric domination on the
nonnegative family, the `theta3z_summable` receipt of R216).
`Summable.tsum_mul_tsum` (the R219 receipt) gives
`theta3z q * theta3z q = ∑' p : ℤ × ℤ, q ^ (|p.1|²) * q ^ (|p.2|²)`, and the
pointwise collapse `q ^ (|u|²) * q ^ (|v|²) = q ^ (|u² + v²|)` is
`pow_add` plus `Int.toNat_of_nonneg` on `u² + v²`. Pair summability rides
`Summable.of_norm_bounded` over the nonneg family, itself summable by
`summable_prod_of_nonneg` (the Fubini twin, R219). -/
def routeB2a : Prop :=
  ∀ q, 0 < q → q < 1 →
    theta3z q * theta3z q = ∑' p : ℤ × ℤ, latU q p

/-- Window B2b: the theta-4 square factorization.
`theta4z q * theta4z q = ∑' p : ℤ × ℤ, latT q p` on `0 < q < 1`.

PAPER PROOF: the same Cauchy ride as B2a, with the sign family attached.
`Summable.tsum_mul_tsum` on `theta4z q · theta4z q` gives
`∑' (u,v), (−1)^|u| (−1)^|v| q^(|u|²) q^(|v|²)`, and the pointwise collapse
is the B2a identity times `(−1)^(|u|+|v|)`. The pair family is summable
because its norm is EXACTLY the B2a pair family (`abs_mul` splits the
product, `abs_neg_one_pow` kills the signs). -/
def routeB2b : Prop :=
  ∀ q, 0 < q → q < 1 →
    theta4z q * theta4z q = ∑' p : ℤ × ℤ, latT q p

/-- Window B3: the parity merge. On `0 < q < 1`:
`(∑' p : ℤ × ℤ, latU q p) + ∑' p : ℤ × ℤ, latT q p = 2 * ∑' p : SamePar, latU q p.1`.

PAPER PROOF: pointwise, the two summands add to
`(1 + (−1)^(|u|+|v|)) · q^(|u²+v²|)`. If `u + v` is odd, `|u| + |v|` is odd
(`|u| ≡ u (mod 2)` by the natAbs parity bridge, the R222 omega receipt), so
the bracket is `1 + (−1) = 0`: the odd-parity shell dies pointwise, and no
involution is needed this time. If `u + v` is even, the bracket is `2`, and
summing the merged family `2 · ∑' SamePar` requires the canonical split of
`ℤ × ℤ` into the SamePar/OddPar books (the R221 `Set.indicator` split and
`tsum_subtype` mating) with the OddPar slice carrying the zero family. -/
def routeB3 : Prop :=
  ∀ q, 0 < q → q < 1 →
    (∑' p : ℤ × ℤ, latU q p) + ∑' p : ℤ × ℤ, latT q p
      = 2 * ∑' p : SamePar, latU q p.1

/-- Window B4: the same-parity reindex to the doubled-nome modulus.
`∑' p : SamePar, latU q p.1 = ∑' p : ℤ × ℤ, latV q p` on `0 < q < 1`.

PAPER PROOF: the R223 change of variables `(a, b) ↦ (u, v) = (a+b, a−b)`,
the hand-built `sameParEquiv` of the L4 window: a bijection `ℤ × ℤ ≃ SamePar`
(inverse `((u+v)/2, (u−v)/2)`, integral exactly because `u ≡ v (mod 2)` on
`SamePar`). Along it, `u² + v² = 2(a² + b²)` (`ring`), so
`latU q (u,v) = latV q (a,b)` pointwise, and `Equiv.tsum_eq` reindexes with
NO summability hypothesis needed. -/
def routeB4 : Prop :=
  ∀ q, 0 < q → q < 1 →
    ∑' p : SamePar, latU q p.1 = ∑' p : ℤ × ℤ, latV q p

/-- Window B5: the doubled-nome factorization home.
`∑' p : ℤ × ℤ, latV q p = theta3z (q * q) * theta3z (q * q)` on `0 < q < 1`.

PAPER PROOF: `latV q (a,b) = (q²)^(|a²+b²|) = (q²)^(|a|²) · (q²)^(|b|²)`
(`pow_add` and the `toNat` one-liner, the B2a mirror at the nome `q²`), so
the lattice sum is exactly the Cauchy product of `theta3z (q * q)` with
itself; `Summable.tsum_mul_tsum` in the reverse direction rides
`theta3z_summable` at the doubled nome (`0 < q² < 1`). -/
def routeB5 : Prop :=
  ∀ q, 0 < q → q < 1 →
    ∑' p : ℤ × ℤ, latV q p = theta3z (q * q) * theta3z (q * q)

/-! ## The conditional assembly (the proved part of R2) -/

/-- THE R2 ASSEMBLY: the five named windows together with the two R1
bridges imply `jacobiAnchorB`. The short algebraic spine is PROVED HERE,
and each window, once its own battery passes, drops in as a hypothesis
until no hypothesis remains and the anchor is UNCONDITIONAL. -/
theorem anchorB_of_route (h1a : routeL1a) (h1b : routeL1b) (h2a : routeB2a)
    (h2b : routeB2b) (h3 : routeB3) (h4 : routeB4) (h5 : routeB5) :
    jacobiAnchorB := by
  intro q hq0 hq1
  have hqq : 0 < q * q ∧ q * q < 1 := ⟨mul_pos hq0 hq0, by nlinarith⟩
  calc theta3 q ^ 2 + theta4 q ^ 2
      = theta3z q * theta3z q + theta4z q * theta4z q := by
          rw [h1a q hq0 hq1, h1b q hq0 hq1, pow_two, pow_two]
    _ = (∑' p : ℤ × ℤ, latU q p) + ∑' p : ℤ × ℤ, latT q p := by
          rw [h2a q hq0 hq1, h2b q hq0 hq1]
    _ = 2 * ∑' p : SamePar, latU q p.1 := h3 q hq0 hq1
    _ = 2 * ∑' p : ℤ × ℤ, latV q p := by rw [h4 q hq0 hq1]
    _ = 2 * (theta3z (q * q) * theta3z (q * q)) := by rw [h5 q hq0 hq1]
    _ = 2 * theta3 (q * q) ^ 2 := by
          rw [pow_two, ← h1a (q * q) hqq.1 hqq.2]

end YangMills.DualBook
