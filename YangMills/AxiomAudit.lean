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

/-!
# AxiomAudit — Independent Lean 4 Kernel Axiom Certificate
Prints the exact axioms used by every headline theorem across all 10 verified modules.
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
