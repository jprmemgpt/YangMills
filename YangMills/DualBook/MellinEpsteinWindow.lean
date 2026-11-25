/-
  PROVENANCE: YangMills.DualBook.MellinEpsteinWindow (R232)
  Built by Gen, Papa's hands only, in the R232 window (Wed 2026-11-25 morning CT),
  on the certified spine of the R71 manuscript section
  (ym_manuscript_section2_r71.md) and the R69 honest-slips record, with the
  CatalanGate paid by the R231 window (Papa's commit 9e98aa4) cashed here for
  the first time in Lean.
  SCOPE: THIS ARITHMETIC only. This module is the ASSEMBLY LAYER: it cashes
  the structural laws of the five-constant book as theorem arithmetic.
  (1) The Gaussian arm sum and difference laws, conditional on the
      Theorem-B closed forms Z_1000(2) = pi*G - (pi^2/24)log 2 and
      Z_1110(2) = -pi*G - (pi^2/24)log 2, where G is the book's Catalan
      constant; the difference law is restated through the PAID gate
      leTwoChiMinusFour = catalan (the D2'-D3' law that waited on it).
  (2) The Mellin regularizer at s = 2 with T0 = 1: [pi^2/Gamma(2)]*(1/2) = pi^2/2,
      Gamma(2) = 1 cashed by Mathlib's Real.Gamma_two. The R69 slip record is
      carried as theorems: the missing -1/s on (0,1] inflates every Z_sigma(2)
      by exactly this regularizer, and E stays GREEN because the common piece
      cancels in the Z_1100 - Z_1111 difference.
  (3) The 2-adic difference cashing: conditional on the Theorem-A closed forms
      Z_1100(2) = -(pi^2/6)log 2 and Z_1111(2) = -4*(pi^2/6)log 2, their
      difference is exactly mellinRegulator * log 2.
  Nothing else is claimed: the Epstein evaluation itself and the full mellin
  integral REMAIN NAMED WINDOWS, never claimed here; no functional equation,
  no analytic continuation, no Clay claim of any kind; the bench stays frozen.
-/
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Gamma.BohrMollerup
import YangMills.DualBook.CatalanGate
import YangMills.DualBook.CatalanGateWindow

namespace YangMills.DualBook

/-! ## The Gaussian arm: sum and difference laws (Theorem B, conditional) -/

/-- Conditional on the Theorem-B closed forms, the Gaussian arm satisfies the
sum law `Z_1000 + Z_1110 = -(pi^2/12) * log 2`. -/
theorem sumLaw_closed {Z1000 Z1110 : ℝ}
    (h1 : Z1000 = Real.pi * catalan - Real.pi ^ 2 / 24 * Real.log 2)
    (h2 : Z1110 = -Real.pi * catalan - Real.pi ^ 2 / 24 * Real.log 2) :
    Z1000 + Z1110 = -(Real.pi ^ 2 / 12) * Real.log 2 := by
  rw [h1, h2]; ring

/-- Conditional on the Theorem-B closed forms, the Gaussian arm satisfies the
difference law `Z_1000 - Z_1110 = 2 * pi * catalan`. --/
theorem diffLaw_closed {Z1000 Z1110 : ℝ}
    (h1 : Z1000 = Real.pi * catalan - Real.pi ^ 2 / 24 * Real.log 2)
    (h2 : Z1110 = -Real.pi * catalan - Real.pi ^ 2 / 24 * Real.log 2) :
    Z1000 - Z1110 = 2 * Real.pi * catalan := by
  rw [h1, h2]; ring

/-- The gate cashed: the same difference law restated through the PAID Catalan
gate (`leTwoChiMinusFour = catalan`, R231). The first Lean cashing of the paid
gate, the D2'-D3' law that waited on it. -/
theorem diffLaw_gate {Z1000 Z1110 : ℝ}
    (h1 : Z1000 = Real.pi * catalan - Real.pi ^ 2 / 24 * Real.log 2)
    (h2 : Z1110 = -Real.pi * catalan - Real.pi ^ 2 / 24 * Real.log 2) :
    Z1000 - Z1110 = 2 * Real.pi * leTwoChiMinusFour := by
  have hgate : leTwoChiMinusFour = catalan := catalanGate_paid
  rw [h1, h2, ← hgate]; ring

/-! ## The Mellin regularizer at s = 2 (the R69 slip record as theorems) -/

/-- The honest regularizer of the Mellin normalization at `s = 2` with `T0 = 1`,
spelled: `pi^2 / 2`, the exact size of the R69 slip on every `Z_sigma(2)`. -/
noncomputable def mellinRegulator : ℝ := Real.pi ^ 2 / 2

/-- The regularizer cashed against the Gamma factor: `[pi^2 / Gamma 2] * (1/2)`
is exactly `pi^2 / 2` because `Gamma 2 = 1` (Mathlib's `Real.Gamma_two`). -/
theorem mellinRegulator_cashed :
    mellinRegulator = Real.pi ^ 2 / Real.Gamma 2 * (1 / 2) := by
  rw [mellinRegulator, Real.Gamma_two]; ring

/-- The R69 slip law: an object inflated by the missing `-1/s` piece (the
regularizer) differs from the honest one by exactly the regularizer, the
fingerprint of the slip (deviation 4.9348...) as a theorem. -/
theorem slip_inflation (Z Z' : ℝ) (h : Z' = Z + mellinRegulator) :
    Z' - Z = mellinRegulator := by
  rw [h]; ring

/-- E stays GREEN under the slip: the common inflated piece cancels in the
`Z_1100 - Z_1111` difference, so the difference law is untouched by the slip. -/
theorem E_green_under_slip (Z1100 Z1111 : ℝ) :
    (Z1100 + mellinRegulator) - (Z1111 + mellinRegulator) = Z1100 - Z1111 := by
  simp only [mellinRegulator]; ring

/-! ## The 2-adic arm difference cashed against the regularizer --/

/-- Conditional on the Theorem-A closed forms, the 2-adic difference is
exactly `mellinRegulator * log 2`, tying the Epstein book's difference to the
regularizer of the Mellin normalization. --/
theorem thetaDifference_cashed {Z1100 Z1111 : ℝ}
    (h1 : Z1100 = -(Real.pi ^ 2 / 6) * Real.log 2)
    (h2 : Z1111 = -4 * (Real.pi ^ 2 / 6) * Real.log 2) :
    Z1100 - Z1111 = mellinRegulator * Real.log 2 := by
  rw [h1, h2, mellinRegulator]; ring

end YangMills.DualBook
