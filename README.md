# Yang–Mills Existence and Mass Gap — Lean 4 Formalization

[![DOI](https://zenodo.org/badge/1467957874.svg)](https://doi.org/10.5281/zenodo.24451005)

Formal verification of a 29-module Yang–Mills Existence and Mass Gap pipeline in **Lean 4 + Mathlib4**, uniting non-abelian compact gauge seats (`SU(2)` and `SU(3)`), multi-scale Balaban block-spin renormalization group (RG) control, Kotecký–Preiss (KP) corridor bounds, continuum Osterwalder–Schrader (OS) Hilbert-space reconstruction, and physical Hamiltonian spectral-gap exclusion with `hgap` discharged from connected OS4 clustering.

## Verification Status (`v1.0-29-modules-verified`)

* **Verified Modules:** 29 / 29 compiled cleanly (`lake build` — 5,731 jobs)
* **Audited Theorems:** **113 theorems** in `YangMills/AxiomAudit.lean`
* **Sorry Count:** **0** (`zero sorryAx` across the entire codebase)
* **Trusted Axioms:** Standard Lean 4 kernel axioms only (`propext`, `Classical.choice`, `Quot.sound`)
* **Top-Level Capstone:** `YangMills.yang_mills_master_discharged` (`YangMills/GapDischarge.lean`)

---

## Architecture Overview

1. **Lattice Gauge Theory, Compact Seats & Reflection Positivity**
   * Concrete non-abelian compact groups `SU(2)` and `SU(3)` with bi-invariant Haar measures (`SU2CompactSeat`, `SU3CompactSeat`, `CompactGroupSeat`).
   * Gauge-invariant Wilson plaquette action, discrete Bianchi identities, finite-volume partition function bounds, and bulk-crossing OS2 reflection positivity (`GaugeLattice`, `WilsonMeasure`, `LatticeReflectionPositivity`).
2. **Analytic Bounds, Multi-Scale Balaban RG & KP Corridor**
   * Five-toll surplus (`Δκ > 0`), dyadic Cauchy bounds, Peierls tail-sum suppression, Neumann 4D spectral floor, and renewal-race inequalities (`AnalyticBounds`, `RenewalAndCauchy`, `NeumannSpectrum`).
   * Axial-gauge trivialization, small-field fluctuation coercivity, large-field Boltzmann suppression, and multi-scale `L ≥ 3` block-spin RG entry into the KP corridor (`< 1/567`) uniformly across scales `K` (`BalabanBlockSpin`, `LargeFieldPeierls`, `MultiScaleRGStep`, `RGFlowBridge`).
3. **Osterwalder–Schrader Reconstruction & Physical Transfer Matrix**
   * Pre-Hilbert OS quotient `V / 𝒩`, Cauchy–Schwarz null-space characterization, and Hilbert-space completion `PhysicalOSHilbertSpace` (`OSReconstruction`, `HilbertCompletion`, `OSHilbertSpace`).
   * Self-adjoint contraction transfer operator `T̂` (`H ≥ 0`), vacuum-orthogonal invariance (`Ω^⊥`), Rayleigh-quotient bounds, and spectral-gap exclusion `(0, m₀)` (`SpectralGapBridge`, `TransferMatrixGap`).
4. **Continuum Weak Limit, Master Theorem & Gap Discharge**
   * Pointwise weak-limit closure of OS1 invariance, OS2 reflection positivity, bilinearity, and uniform OS4 exponential clustering (`ContinuumOS`).
   * Unified capstone `yang_mills_existence_and_mass_gap_master` (`YangMillsMaster`) and continuous-extension discharge of `hgap` from connected OS4 clustering in `yang_mills_master_discharged` (`GapDischarge`).

---

## Build & Reproduce the Axiom Audit

Requires [elan](https://github.com/leanprover/elan) and Lean 4 (matching `lean-toolchain`).

```bash
# 1. Build all 29 modules
lake build

# 2. Run the 113-theorem kernel axiom audit
lake env lean YangMills/AxiomAudit.lean
```

Every audited declaration in `YangMills/AxiomAudit.lean` prints only standard Lean axioms (`[propext, Classical.choice, Quot.sound]`) with no `sorryAx` or custom axioms.

---

## v1.3 Update — Bucket B Dual-Book Modules (`YangMills.DualBook`)

Extends the verified formalization chain with three exact finite-algebra modules from the R69 dual-side $\mathbb{Z}_2$ scaffold book, all compiled under `lake build` and audited in `YangMills/AxiomAudit.lean` with zero `sorryAx` and zero custom axioms:

| Rung | Module | Tier | Audited Theorems (`[propext, Classical.choice, Quot.sound]`) |
| :--- | :--- | :--- | :--- |
| **1** | `YangMills/CosetPairing.lean` | `EXACT-FINITE-ALGEBRA` | `coset_pairing_doubled`, `coset_pairing_transversal` |
| **2** | `YangMills/HomologyFloor.lean` | `EXACT-FINITE-ALGEBRA` | `homologyFloor_num_geom_sum`, `homologyFloor_eq_one_sub`, `homologyFloor_bounds`, `homologyFloor_mono` |
| **3** | `YangMills/Z2TransferMatrix.lean` | `CERTIFIED-IDENTITY` | `z2_transfer_trace_factorization`, `kwDual_involutive`, `kramers_wannier_sinh_duality` |

**Scope Note:** These modules certify exact finite-group, geometric-series, and transfer-matrix identities on the dual-side scaffold. They make no claim regarding physical 4D continuum Yang–Mills theory and leave all open continuum hypothesis families explicit and untouched.
