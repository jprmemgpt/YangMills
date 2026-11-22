# Yang–Mills Existence and Mass Gap — Lean 4 Formalization

Formal verification of a 28-module Yang–Mills Existence and Mass Gap pipeline in **Lean 4 + Mathlib4**, uniting non-abelian compact gauge seats (`SU(2)` and `SU(3)`), multi-scale Balaban block-spin renormalization group (RG) control, Kotecký–Preiss (KP) corridor bounds, continuum Osterwalder–Schrader (OS) Hilbert-space reconstruction, and physical Hamiltonian spectral-gap exclusion.

## Verification Status (`v0.9-28-modules-verified`)

* **Verified Modules:** 28 / 28 compiled cleanly (`lake build` — 5,729 jobs)
* **Audited Theorems:** **108 theorems** in `YangMills/AxiomAudit.lean`
* **Sorry Count:** **0** (`zero sorryAx` across the entire codebase)
* **Trusted Axioms:** Standard Lean 4 kernel axioms only (`propext`, `Classical.choice`, `Quot.sound`)

---

## Architecture Overview

The pipeline is organized into four layers culminating in `YangMills.yang_mills_existence_and_mass_gap_master`:

1. **Lattice Gauge Theory, Compact Seats & Reflection Positivity**
   * Concrete non-abelian compact groups `SU(2)` and `SU(3)` with bi-invariant Haar measures (`SU2CompactSeat`, `SU3CompactSeat`, `CompactGroupSeat`).
   * Gauge-invariant Wilson plaquette action, discrete Bianchi identities, finite-volume partition function bounds, and bulk-crossing OS2 reflection positivity (`GaugeLattice`, `WilsonMeasure`, `LatticeReflectionPositivity`).
2. **Analytic Bounds, Multi-Scale Balaban RG & KP Corridor**
   * Five-toll surplus (`Δκ > 0`), dyadic Cauchy bounds, Peierls tail-sum suppression, Neumann 4D spectral floor, and renewal-race inequalities (`AnalyticBounds`, `RenewalAndCauchy`, `NeumannSpectrum`).
   * Axial-gauge trivialization, small-field fluctuation coercivity, large-field Boltzmann suppression, and multi-scale `L ≥ 3` block-spin RG entry into the KP corridor (`< 1/567`) uniformly across scales `K` (`BalabanBlockSpin`, `LargeFieldPeierls`, `MultiScaleRGStep`, `RGFlowBridge`).
3. **Osterwalder–Schrader Reconstruction & Physical Transfer Matrix**
   * Pre-Hilbert OS quotient `V / 𝒩`, Cauchy–Schwarz null-space characterization, and Hilbert-space completion `PhysicalOSHilbertSpace` (`OSReconstruction`, `HilbertCompletion`, `OSHilbertSpace`).
   * Self-adjoint contraction transfer operator `T̂` (`H ≥ 0`), vacuum-orthogonal invariance (`Ω^⊥`), Rayleigh-quotient bounds, and spectral-gap exclusion `(0, m₀)` (`SpectralGapBridge`, `TransferMatrixGap`).
4. **Continuum Weak Limit & Master Theorem**
   * Pointwise weak-limit closure of OS1 invariance, OS2 reflection positivity, bilinearity, and uniform OS4 exponential clustering (`ContinuumOS`).
   * Unified 9-part capstone theorem `yang_mills_existence_and_mass_gap_master` (`YangMillsMaster`).

---

## Build & Reproduce the Axiom Audit

Requires [elan](https://github.com/leanprover/elan) and Lean 4 (matching `lean-toolchain`).

```bash
# 1. Build all 28 modules
lake build

# 2. Run the 108-theorem kernel axiom audit
lake env lean YangMills/AxiomAudit.lean
```

Every audited declaration in `YangMills/AxiomAudit.lean` prints only standard Lean axioms (`[propext, Classical.choice, Quot.sound]`) with no `sorryAx` or custom axioms.
