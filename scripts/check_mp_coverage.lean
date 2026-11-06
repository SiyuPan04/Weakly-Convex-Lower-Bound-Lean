import WC
import MP.Main
import MP.Verification
import MP.ModelClass
import MP.RadialOracle
import MP.Locality
import MP.RandomizedReduction
import MP.JointMeasurability
import MP.TerminalSubspace

/-! Every mapped declaration and key transitive axiom dependency. -/

#check MP.main
#check MP.main_explicit
#check MP.zero_outside_of_mem_coordinateSpan
#check MP.terminal_subspace_barrier
#check MP.terminal_stationarity
#check WC.WeaklyConvex
#check WC.GloballyLipschitz
#check WC.GapBound
#check WC.Admissible
#check WC.gapBound_iff_inf
#check MP.Model.Instance
#check WC.moreauEnvelope
#check WC.moreau_hasGradientAt
#check WC.moreau_gradient_eq
#check MP.Model.successProbability
#check WC.subdifferential
#check WC.fullOracle
#check WC.fullOracle_measurable
#check WC.parameterized_fullOracle_measurable
#check MP.Model.BorelAlgorithm
#check MP.Model.trajectory
#check WC.Model.UnitBorelAlgorithm.extend_trajectory
#check MP.Model.hittingTime
#check MP.Model.oracleComplexity
#check MP.Model.oracleComplexityOn
#check MP.Model.oracleComplexityOn_univ
#check MP.Model.MainTheorem
#check MP.small_accuracy_ratios
#check MP.uniformFamilies
#check MP.UnscaledHardInstanceConditions
#check MP.construction_satisfies_conditions
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
#check MP.source_radius_bound
#check MP.source_order
#check MP.remote_source_subdifferential
#check MP.robust_oracle_identity
#check WC.chainMajorant_diagonalMask_eq
#check WC.chainMajorant_diagonalMask_subdifferential_eq
#check MP.unscaled_terminal_barrier
#check MP.terminal_diagonal_barrier
#check WC.horizon_bound
#check MP.initial_gap_le_five
#check WC.chainMajorant_zero
#check WC.chainMajorant_gap
#check WC.chainMajorant_infimum
#check MP.radialRadius
#check MP.radialObjective
#check MP.radial_admissible
#check MP.radial_moreau_barrier
#check MP.radial_exterior_gradient
#check MP.radial_exterior_oracle
#check MP.radialObjectiveAt_exterior_fullOracle_eq
#check MP.Concentration.sphere_mgf_le
#check MP.Concentration.sphere_projection_tail
#check MP.Concentration.adaptive_projection_tail_product
#check MP.logarithmicDimensionBound
#check MP.logarithmic_dimension_budget_ennreal
#check MP.family_barrierEvent_measurable
#check MP.joint_barrier_of_exponential_budget
#check MP.randomized_reduction
#check MP.radial_prefix_fullOracle
#check MP.prefixResponse_measurable
#check MP.chainFamily
#check MP.family_trajectory_measurable
#check MP.family_evaluatedOutput_measurable

#print axioms MP.main
#print axioms MP.terminal_stationarity
#print axioms MP.construction_satisfies_conditions
#print axioms MP.radial_moreau_barrier
#print axioms MP.radial_exterior_oracle
#print axioms MP.robust_oracle_identity
#print axioms MP.uniformFamilies
#print axioms MP.Concentration.sphere_mgf_le
#print axioms MP.Concentration.sphere_projection_tail
#print axioms MP.Concentration.adaptive_projection_tail_product
#print axioms MP.logarithmic_dimension_budget_ennreal
#print axioms MP.joint_barrier_of_exponential_budget
#print axioms MP.randomized_reduction
#print axioms MP.family_barrierEvent_measurable
#print axioms MP.radial_prefix_fullOracle
#print axioms MP.prefixResponse_measurable
#print axioms MP.chainFamily
