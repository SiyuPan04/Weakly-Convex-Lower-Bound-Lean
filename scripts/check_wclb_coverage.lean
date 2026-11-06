import WC
import WCLB.Main
import WCLB.Verification
import WCLB.ModelClass
import WCLB.RadialOracle
import WCLB.Locality
import WCLB.RandomizedReduction
import WCLB.JointMeasurability
import WCLB.TerminalSubspace

/-! Every mapped declaration and key transitive axiom dependency. -/

#check WCLB.main
#check WCLB.main_explicit
#check WCLB.zero_outside_of_mem_coordinateSpan
#check WCLB.terminal_subspace_barrier
#check WCLB.terminal_stationarity
#check WC.WeaklyConvex
#check WC.GloballyLipschitz
#check WC.GapBound
#check WC.Admissible
#check WC.gapBound_iff_inf
#check WCLB.Model.Instance
#check WC.moreauEnvelope
#check WC.moreau_hasGradientAt
#check WC.moreau_gradient_eq
#check WCLB.Model.successProbability
#check WC.subdifferential
#check WC.fullOracle
#check WC.fullOracle_measurable
#check WC.parameterized_fullOracle_measurable
#check WCLB.Model.BorelAlgorithm
#check WCLB.Model.trajectory
#check WC.Model.UnitBorelAlgorithm.extend_trajectory
#check WCLB.Model.hittingTime
#check WCLB.Model.oracleComplexity
#check WCLB.Model.oracleComplexityOn
#check WCLB.Model.oracleComplexityOn_univ
#check WCLB.Model.MainTheorem
#check WCLB.small_accuracy_ratios
#check WCLB.uniformFamilies
#check WCLB.UnscaledHardInstanceConditions
#check WCLB.construction_satisfies_conditions
#check WC.euclideanTiltedBlock_frechetSubgradient_locality
#check WC.positiveScore_variational
#check WC.coupledFunction_variational
#check WC.weightedCoupledFunction_relay_expansion
#check WC.weightedCoupledFunction_grouped
#check WC.hasGradientAt_euclideanProgress
#check WC.progressGradient_norm_le
#check WC.progressGradient_norm_sub_le
#check WC.monotone_blockProgress
#check WC.weaklyConvex_smoothBlockTerm
#check WC.weaklyConvex_weightedCoupledFunction
#check WC.weaklyConvex_coupledFunction
#check WC.chainMajorant_finite
#check WC.chainMajorant_lipschitz
#check WC.chainMajorant_weaklyConvex
#check WC.chainMajorant_lower_bound
#check WC.coupledFunction_coordinate_antitone
#check WC.diagonal_filtration_width
#check WC.diagonal_quotient_finrank
#check WC.diagonal_initial_space
#check WC.subdifferential_coupledFunction_blockwise
#check WC.mem_coupledBlockSubgradients_iff
#check WC.coupledBlockSubgradients_nonempty
#check WC.coupledBlockSubgradients_convex
#check WC.coupledBlockSubgradients_isCompact
#check WC.coupledProgressCoefficient_mem_Icc
#check WC.active_coupled_weight_score_nonneg
#check WC.chainMajorant_sources_nonempty
#check WC.chainMajorant_sources_isCompact
#check WC.chainMajorant_subdifferential
#check WCLB.source_radius_bound
#check WCLB.source_order
#check WCLB.remote_source_subdifferential
#check WCLB.robust_oracle_identity
#check WC.chainMajorant_diagonalMask_eq
#check WC.chainMajorant_diagonalMask_subdifferential_eq
#check WCLB.unscaled_terminal_barrier
#check WCLB.terminal_diagonal_barrier
#check WC.horizon_bound
#check WCLB.initial_gap_le_five
#check WC.chainMajorant_zero
#check WC.chainMajorant_gap
#check WC.chainMajorant_infimum
#check WCLB.radialRadius
#check WCLB.radialObjective
#check WCLB.radial_admissible
#check WCLB.radial_moreau_barrier
#check WCLB.radial_exterior_gradient
#check WCLB.radial_exterior_oracle
#check WCLB.radialObjectiveAt_exterior_fullOracle_eq
#check WCLB.Concentration.sphere_mgf_le
#check WCLB.Concentration.sphere_projection_tail
#check WCLB.Concentration.adaptive_projection_tail_product
#check WCLB.logarithmicDimensionBound
#check WCLB.logarithmic_dimension_budget_ennreal
#check WCLB.family_barrierEvent_measurable
#check WCLB.joint_barrier_of_exponential_budget
#check WCLB.randomized_reduction
#check WCLB.radial_prefix_fullOracle
#check WCLB.prefixResponse_measurable
#check WCLB.chainFamily
#check WCLB.family_trajectory_measurable
#check WCLB.family_evaluatedOutput_measurable

#print axioms WCLB.main
#print axioms WCLB.terminal_stationarity
#print axioms WCLB.construction_satisfies_conditions
#print axioms WCLB.radial_moreau_barrier
#print axioms WCLB.radial_exterior_oracle
#print axioms WCLB.robust_oracle_identity
#print axioms WCLB.uniformFamilies
#print axioms WCLB.Concentration.sphere_mgf_le
#print axioms WCLB.Concentration.sphere_projection_tail
#print axioms WCLB.Concentration.adaptive_projection_tail_product
#print axioms WCLB.logarithmic_dimension_budget_ennreal
#print axioms WCLB.joint_barrier_of_exponential_budget
#print axioms WCLB.randomized_reduction
#print axioms WCLB.family_barrierEvent_measurable
#print axioms WCLB.radial_prefix_fullOracle
#print axioms WCLB.prefixResponse_measurable
#print axioms WCLB.chainFamily
