/-
PROVENANCE: v1.5 UNCONDITIONAL ASSEMBLY (Tue 2026-11-24).
Closes R1 (Jacobi Anchor A, R216–R223) and R2 (Jacobi Anchor B, R224–R229)
into the v1.4 DualBookAssembly spine (`theta_1100_of_anchor`, `theta_sum_D1'`).
Both structural laws now stand as unconditional theorems with zero hypotheses
and zero `sorry`.

SCOPE NOTE: this module certifies THIS ARITHMETIC — classical Jacobi theta
doubling identities and the resulting unconditional latch law and D1′ sum law.
It proves nothing about physical four-dimensional Yang–Mills theory and claims
no Clay Millennium result. Bench FROZEN AT 100.0, the crossing never claimed.
-/

import YangMills.DualBook.DualBookAssembly
import YangMills.DualBook.JacobiAnchorsL4
import YangMills.DualBook.JacobiAnchorsB5

/-!
# Unconditional Dual-Book Assembly (v1.5)

Discharges `jacobiAnchorA` (via `anchorA_of_route_seven_paid`, R223) and
`jacobiAnchorB` (via `anchorB_of_route_seven_paid`, R229) into the structural
laws of `DualBookAssembly.lean`, making both the latch law (`Θ_1100(q) = Θ_1111(q²)`)
and the D1′ sum law (`Θ_1000(q) + Θ_1110(q) = 2·Θ_1111(q⁴)`) unconditional.
-/

namespace YangMills.DualBook

/-- Jacobi Anchor A, unconditional (`θ₃(q)·θ₄(q) = θ₄(q²)²` for `0 < q < 1`). -/
theorem jacobiAnchorA_unconditional : jacobiAnchorA :=
  anchorA_of_route_seven_paid

/-- Jacobi Anchor B, unconditional (`θ₃(q)² + θ₄(q)² = 2·θ₃(q²)²` for `0 < q < 1`). -/
theorem jacobiAnchorB_unconditional : jacobiAnchorB :=
  anchorB_of_route_seven_paid

/-- The latch law, UNCONDITIONAL: `Θ_1100(q) = Θ_1111(q²)` for `0 < q < 1`. -/
theorem theta_1100_unconditional {q : ℝ} (hq0 : 0 < q) (hq1 : q < 1) :
    theta1100 q = theta1111 (q * q) :=
  theta_1100_of_anchor jacobiAnchorA_unconditional hq0 hq1

/-- The D1′ sum law, UNCONDITIONAL:
`Θ_1000(q) + Θ_1110(q) = 2·Θ_1111(q⁴)` for `0 < q < 1`. -/
theorem theta_sum_D1'_unconditional {q : ℝ} (hq0 : 0 < q) (hq1 : q < 1) :
    theta1000 q + theta1110 q = 2 * theta1111 ((q * q) * (q * q)) :=
  theta_sum_D1' jacobiAnchorA_unconditional jacobiAnchorB_unconditional hq0 hq1

end YangMills.DualBook
