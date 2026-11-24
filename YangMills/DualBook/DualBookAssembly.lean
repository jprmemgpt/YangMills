/-
PROVENANCE: rung 5 of the dual/Z₂-scaffold exact book (Bucket B), following
the printed "Bucket B Handoff — the Dual-Book Spec for Gemini" (the named
source document; certified record of the optimization bench's R69 window,
machine-certified at 1e-13, second independent referee route to 2.6e-9).
Rung 4 foundations (`ThetaConstants.lean`) landed first; this module
assembles the shift-labeled composites Θ_σ and proves the book's
structural laws CONDITIONALLY on the two Jacobi doubling anchors.

SCOPE NOTE: this module certifies THIS ARITHMETIC — polynomial and
q-series identities among the theta composites. It proves nothing about
physical four-dimensional Yang–Mills theory and claims no Clay
Millennium result.

HONEST WINDOW SPLIT:
  PROVEN HERE (conditional on the anchors): the latch law
  `theta_1100_of_anchor` and the D1′ sum law `theta_sum_D1'`.
  NAMED WINDOWS (hypotheses, NOT proved here): the two Jacobi anchors
  `jacobiAnchorA`, `jacobiAnchorB`. Mathlib carries only the complex
  upper-half-plane `jacobiTheta` family; the real q-series doubling
  identities are the named follow-up window. The numeric witnesses
  (sum repulsion −0.5700907053215 to ~1e-11) live in the bench record and
  are evidence, never proof.
-/
import YangMills.DualBook.ThetaConstants
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-!
# The Θ_σ composites and the conditional structural laws (rung 5)

This file assembles the shift-labeled composites `theta1100`, `theta1111`,
`theta1000`, `theta1110` in the corrected convention, states the two Jacobi
anchors as named windows (`jacobiAnchorA`, `jacobiAnchorB`), and proves the
latch law `theta_1100_of_anchor` and the D1′ sum law `theta_sum_D1'`
conditionally on those anchors.
-/

namespace YangMills.DualBook

/-! ## The shift-labeled composites Θ_σ (corrected convention) -/

/-- Θ_1100 = θ₄²·θ₃². -/
noncomputable def theta1100 (q : ℝ) : ℝ := theta4 q ^ 2 * theta3 q ^ 2

/-- Θ_1111 = θ₄⁴. -/
noncomputable def theta1111 (q : ℝ) : ℝ := theta4 q ^ 4

/-- Θ_1000 = θ₄·θ₃³. -/
noncomputable def theta1000 (q : ℝ) : ℝ := theta4 q * theta3 q ^ 3

/-- Θ_1110 = θ₄³·θ₃. -/
noncomputable def theta1110 (q : ℝ) : ℝ := theta4 q ^ 3 * theta3 q

/-! ## The Jacobi anchors (named windows, carried as hypotheses) -/

/-- Jacobi anchor A: `θ₃(q)·θ₄(q) = θ₄(q²)²` for `0 < q < 1`.

A NAMED WINDOW, not proved in this file: it rides `jacobiAnchorA` as an
explicit hypothesis in every theorem below. The anchor is a classical
Jacobi theta identity; rebuilding its q-series proof in Lean is the named
follow-up window (Mathlib currently carries no real theta constants). -/
def jacobiAnchorA : Prop :=
  ∀ q, 0 < q → q < 1 → theta3 q * theta4 q = theta4 (q * q) ^ 2

/-- Jacobi anchor B: `θ₃(q)² + θ₄(q)² = 2·θ₃(q²)²` for `0 < q < 1`.

A NAMED WINDOW, carried as an explicit hypothesis, like `jacobiAnchorA`. -/
def jacobiAnchorB : Prop :=
  ∀ q, 0 < q → q < 1 → theta3 q ^ 2 + theta4 q ^ 2 = 2 * theta3 (q * q) ^ 2

/-! ## The conditional structural laws (proved) -/

/-- Domain facts for the doubled nome: `0 < q < 1` gives `0 < q² < 1`. -/
private theorem sq_mem_ball {q : ℝ} (hq0 : 0 < q) (hq1 : q < 1) :
    0 < q * q ∧ q * q < 1 := by
  refine ⟨by positivity, ?_⟩
  rw [← sq]
  exact pow_lt_one₀ hq0.le hq1 (by omega)

/-- The latch law (bucket "Theorem L" pattern): under anchor A,
`Θ_1100(q) = Θ_1111(q²)`. This is the exact structural identity behind
the book's Theorem A scaffold; certified on the bench at 1e-13. -/
theorem theta_1100_of_anchor (hA : jacobiAnchorA) {q : ℝ} (hq0 : 0 < q) (hq1 : q < 1) :
    theta1100 q = theta1111 (q * q) := by
  have e2 : theta3 q * theta4 q = theta4 (q * q) ^ 2 := hA q hq0 hq1
  unfold theta1100 theta1111
  calc theta4 q ^ 2 * theta3 q ^ 2 = (theta3 q * theta4 q) ^ 2 := by ring
    _ = (theta4 (q * q) ^ 2) ^ 2 := by rw [e2]
    _ = theta4 (q * q) ^ 4 := by ring

/-- The D1′ sum law: under anchors A and B,
`Θ_1000(q) + Θ_1110(q) = 2·Θ_1111(q⁴)`.

This is the book's D1′ in unconditional composite form: the sum repulsion
of the 1100/1111 arms feeds the 1000/1110 pair. The bench witness sum
−0.5700907053215 ( agreement ~1e-11 at s ∈ {2, 2.5, 3, 4}) is evidence
for the CLOSED FORMS this law helps assemble, and is never a proof
substitute. -/
theorem theta_sum_D1' (hA : jacobiAnchorA) (hB : jacobiAnchorB) {q : ℝ}
    (hq0 : 0 < q) (hq1 : q < 1) :
    theta1000 q + theta1110 q = 2 * theta1111 ((q * q) * (q * q)) := by
  have hqq := sq_mem_ball hq0 hq1
  have e2 : theta3 q * theta4 q = theta4 (q * q) ^ 2 := hA q hq0 hq1
  have e1 : theta3 q ^ 2 + theta4 q ^ 2 = 2 * theta3 (q * q) ^ 2 := hB q hq0 hq1
  have e3 : theta3 (q * q) * theta4 (q * q) = theta4 ((q * q) * (q * q)) ^ 2 :=
    hA (q * q) hqq.1 hqq.2
  unfold theta1000 theta1110 theta1111
  calc theta4 q * theta3 q ^ 3 + theta4 q ^ 3 * theta3 q
      = (theta3 q * theta4 q) * (theta3 q ^ 2 + theta4 q ^ 2) := by ring
    _ = theta4 (q * q) ^ 2 * (2 * theta3 (q * q) ^ 2) := by rw [e2, e1]
    _ = 2 * (theta3 (q * q) * theta4 (q * q)) ^ 2 := by ring
    _ = 2 * (theta4 ((q * q) * (q * q)) ^ 2) ^ 2 := by rw [e3]
    _ = 2 * theta4 ((q * q) * (q * q)) ^ 4 := by ring

end YangMills.DualBook
