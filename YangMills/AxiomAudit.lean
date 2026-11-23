import YangMills.Z2TransferMatrix
import YangMills.CosetPairing
import YangMills.HomologyFloor
import YangMills.GapDischarge
import YangMills.YangMillsMaster
import YangMills.ContinuumOS
import YangMills.TransferMatrixGap
import YangMills.OSHilbertSpace
import YangMills.LatticeReflectionPositivity
import YangMills.LatticeHaarMeasure
import YangMills.MultiScaleRGStep
import YangMills.SU3CompactSeat
import YangMills.LargeFieldPeierls
import YangMills.BalabanBlockSpin
import YangMills.SpectralGapBridge
import YangMills.CompactGroupSeat
import YangMills.Defs.CorridorConstants
import YangMills.DiscreteGeometry
import YangMills.HyperoctahedralSymmetry
import YangMills.AnalyticBounds
import YangMills.RenewalAndCauchy
import YangMills.NeumannSpectrum
import YangMills.GaugeLattice
import YangMills.ClusterExpansion
import YangMills.OsterwalderSchrader
import YangMills.SU2Seat
import YangMills.SU3Seat
import YangMills.WilsonMeasure
import YangMills.OSReconstruction
import YangMills.RGFlowBridge
import YangMills.HaarMeasureSeat
import YangMills.HilbertCompletion

/-!
# AxiomAudit — Independent Lean 4 Kernel Axiom Certificate (16 Modules)
Prints the exact axioms used by every headline theorem across all 16 verified modules.
A clean audit shows ONLY Lean's standard axioms (`propext`, `Classical.choice`, `Quot.sound`)
or a subset thereof, with ZERO `sorryAx` and ZERO custom axioms.
-/

#print axioms YangMills.certified_deltaKappa_pos
#print axioms YangMills.certified_floor_beats_corridor_pair
#print axioms YangMills.certified_mu0_ge_two
#print axioms YangMills.torus4_betti_rank_nullity
#print axioms YangMills.peierls_group_blind_one_nat
#print axioms YangMills.wb4_schur_uniqueness_trF2
#print axioms YangMills.harmonic_4d_laplacian_zero
#print axioms YangMills.real_five_toll_surplus
#print axioms YangMills.dyadic_cauchy_four_thirds_bound
#print axioms YangMills.peierls_tail_sum_bound
#print axioms YangMills.renewal_corridor_band
#print axioms YangMills.single_line_renewal_race
#print axioms YangMills.neumann_4d_spectral_floor
#print axioms YangMills.wilsonPlaquetteAction_gauge_invariant
#print axioms YangMills.discrete_bianchi_identity
#print axioms YangMills.mass_gap_floor_from_five_tolls
#print axioms YangMills.os2_weak_limit_closed
#print axioms YangMills.os4_implies_spectral_mass_gap
#print axioms YangMills.SU2.nonabelian
#print axioms YangMills.su2_wilson_gauge_invariant
#print axioms YangMills.su2_discrete_bianchi
#print axioms YangMills.SU3.nonabelian
#print axioms YangMills.su3_wilson_gauge_invariant
#print axioms YangMills.su3_discrete_bianchi
#print axioms YangMills.partitionFunction_pos
#print axioms YangMills.wilsonExpect_gauge_invariant
#print axioms YangMills.os_taylor_truncation_reflection_positive
#print axioms YangMills.wilson_os2_reflection_positivity_of_limit
#print axioms YangMills.osInner_eq_zero_iff
#print axioms YangMills.os_transfer_contraction
#print axioms YangMills.os_clustering_implies_transfer_gap
#print axioms YangMills.ymBeta0_pos
#print axioms YangMills.rg_one_loop_iteration
#print axioms YangMills.dimensional_transmutation_identity
#print axioms YangMills.yang_mills_corridor_mass_gap_pipeline
#print axioms YangMills.su2_and_su3_seats_certified
#print axioms YangMills.haar_integral_conj_inv
#print axioms YangMills.haar_boltzmann_pos
#print axioms YangMills.haar_factorized_kernel_reflection_positive
#print axioms YangMills.haar_os2_reflection_positivity_of_tendsto
#print axioms YangMills.hilbertCompletion_complete
#print axioms YangMills.liftOperator_symmetric
#print axioms YangMills.liftOperator_contraction
#print axioms YangMills.hilbert_transfer_mass_gap_decay

-- Module 17: CompactGroupSeat (Concrete SU(2) Topological Group & Bi-Invariant Haar Measure)
#print axioms YangMills.su2Haar_integral_one
#print axioms YangMills.su2Haar_integral_conj_inv
#print axioms YangMills.su2Haar_wilson_plaquette_pos
#print axioms YangMills.su2Haar_reflection_positive_square

-- Module 18: SpectralGapBridge (Completed Hilbert-Space Spectral Gap Exclusion)
#print axioms YangMills.vacuumOrthog_invariant
#print axioms YangMills.hilbert_rayleigh_mass_gap
#print axioms YangMills.hilbert_no_eigenvalue_in_gap
#print axioms YangMills.hilbert_hamiltonian_gap_exclusion
#print axioms YangMills.corridor_to_hilbert_spectral_gap

-- Module 19: BalabanBlockSpin (4D L-Block Transport, Axial Gauge & Small-Field Coercivity)
#print axioms YangMills.blockLink_gauge_covariant
#print axioms YangMills.blockLink_plaquette_gauge_invariant
#print axioms YangMills.axial_gauge_trivializes_ray
#print axioms YangMills.balaban_fluctuation_coercivity
#print axioms YangMills.balaban_small_field_fluctuation_decay

-- Module 20: LargeFieldPeierls (Large-Field Boltzmann Suppression & KP Corridor Entry)
#print axioms YangMills.large_field_boltzmann_suppression
#print axioms YangMills.peierls_tail_at_seven_lt_bridge_cap
#print axioms YangMills.peierls_tail_sum_lt_bridge_cap
#print axioms YangMills.balaban_peierls_implies_kp_corridor
#print axioms YangMills.balaban_block_to_corridor_mass_gap

-- Module 21: SU3CompactSeat (Concrete Compact SU(3) & Bi-Invariant Haar Measure)
#print axioms YangMills.SU3.isCompact_range_mat
#print axioms YangMills.su3Haar_integral_conj_inv
#print axioms YangMills.su3Haar_wilson_plaquette_bounds
#print axioms YangMills.su3Haar_wilson_plaquette_pos
#print axioms YangMills.su3Haar_reflection_positive_square

-- Module 22: MultiScaleRGStep (Iterated k-Step Block-Spin RG & Spectral Gap Bridge)
#print axioms YangMills.iterBlockLink_gauge_covariant
#print axioms YangMills.iterBlockLink_plaquette_gauge_invariant
#print axioms YangMills.runningInvCoupling_strict_mono_uv
#print axioms YangMills.multiscale_dyadic_beats_bridge_cap
#print axioms YangMills.multiscale_balaban_to_hilbert_spectral_gap

-- Module 23: LatticeHaarMeasure (Concrete N-Link Product Haar & Finite-Volume Wilson Measure)
#print axioms YangMills.latticeHaar_map_gaugeTransform
#print axioms YangMills.latticeHaar_integral_gauge_inv
#print axioms YangMills.latticePartition_bounds
#print axioms YangMills.latticeExpect_gauge_invariant
#print axioms YangMills.su2LatticeHaar_gauge_invariant
#print axioms YangMills.su3LatticeHaar_gauge_invariant

-- Module 24: LatticeReflectionPositivity (Concrete Finite-Volume OS2 Reflection Positivity)
#print axioms YangMills.lattice_os2_factorized_nonneg
#print axioms YangMills.lattice_os2_bulk_crossing_nonneg
#print axioms YangMills.lattice_os2_of_tendsto
#print axioms YangMills.su2_lattice_os2_bulk_crossing_nonneg
#print axioms YangMills.su3_lattice_os2_bulk_crossing_nonneg

-- Module 25: OSHilbertSpace (Concrete Pre-Hilbert OS Quotient & Completed Physical Hilbert Space)
#print axioms YangMills.LinearOSBilinearSpace.toOSBilinearSpace
#print axioms YangMills.LinearOSBilinearSpace.ofReflectionFunctional
#print axioms YangMills.osQuotient_norm_sq
#print axioms YangMills.physicalOSHilbert_complete
#print axioms YangMills.physicalOSHilbert_inner_mk
#print axioms YangMills.physicalOSHilbert_norm_sq_mk

-- Module 26: TransferMatrixGap (Physical Hilbert-Space Transfer Operator & Spectral Gap Exclusion)
#print axioms YangMills.LinearOSTransferSemigroup.T1_preserves_osEquiv
#print axioms YangMills.LinearOSTransferSemigroup.quotientTransferLinear_symm
#print axioms YangMills.LinearOSTransferSemigroup.quotientTransferLinear_contraction
#print axioms YangMills.LinearOSTransferSemigroup.physicalTransfer_symmetric
#print axioms YangMills.LinearOSTransferSemigroup.physicalTransfer_contraction
#print axioms YangMills.LinearOSTransferSemigroup.physicalTransfer_vacuumOrthog_invariant
#print axioms YangMills.LinearOSTransferSemigroup.quotientTransfer_clustering_norm_le
#print axioms YangMills.LinearOSTransferSemigroup.physical_hamiltonian_mass_gap_exclusion

-- Module 27: ContinuumOS (Continuum Weak-Limit Closure of OS1, OS2, OS4 & Transfer Mass Gap)
#print axioms YangMills.continuum_os2_reflection_positivity
#print axioms YangMills.continuum_os_symm
#print axioms YangMills.continuum_os_add_left
#print axioms YangMills.continuum_os_smul_left
#print axioms YangMills.continuumOSBilinearSpace
#print axioms YangMills.continuum_os1_invariance
#print axioms YangMills.continuum_os4_clustering
#print axioms YangMills.continuumTransferSemigroup
#print axioms YangMills.continuum_transfer_mass_gap

-- Module 28: YangMillsMaster (Unified 28-Module Existence & Mass Gap Capstone)
#print axioms YangMills.yang_mills_existence_and_mass_gap_master

-- Module 29: GapDischarge (Discharging hgap from Connected OS4 Clustering)
#print axioms YangMills.vacOrthogProj_continuous
#print axioms YangMills.vacOrthogProj_eq_self
#print axioms YangMills.osMk_sub_smul_coe
#print axioms YangMills.discharge_hgap_from_connected_os4
#print axioms YangMills.yang_mills_master_discharged

#print axioms YangMills.DualBook.coset_pairing_doubled
#print axioms YangMills.DualBook.coset_pairing_transversal
#print axioms YangMills.DualBook.homologyFloor_num_geom_sum
#print axioms YangMills.DualBook.homologyFloor_eq_one_sub
#print axioms YangMills.DualBook.homologyFloor_bounds
#print axioms YangMills.DualBook.homologyFloor_mono

#print axioms YangMills.DualBook.z2_transfer_trace_factorization
#print axioms YangMills.DualBook.kwDual_involutive
#print axioms YangMills.DualBook.kramers_wannier_sinh_duality
