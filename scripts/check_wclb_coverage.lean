import WC
import WCLB

/-! Numbered statements in WC.pdf, in printed order. Axiom queries also check
that the declarations resolve in the two public library entry points. -/

example : WCLB.Model.MainTheorem := WCLB.main

-- Theorem 1, p. 3: Lower bound for all sufficiently small positive accuracies
#print axioms WCLB.main_for_sufficiently_small
#print axioms WCLB.main_for_sufficiently_small_nonneg_gap

-- Definition 1, p. 4: Function class
#print axioms WC.WeaklyConvex
#print axioms WC.GloballyLipschitz
#print axioms WC.GapBound
#print axioms WC.Admissible
#print axioms WC.gapBound_iff_inf
#print axioms WCLB.Model.Instance
#print axioms WCLB.Model.positiveDimensionalInstances

-- Definition 2, p. 5: Stationarity of the Moreau envelope
#print axioms WC.moreauEnvelope
#print axioms WC.moreau_hasGradientAt
#print axioms WC.moreau_gradient_eq
#print axioms WCLB.Model.successProbability

-- Definition 3, p. 5: First-order oracle
#print axioms WC.subdifferential
#print axioms WC.fullOracle
#print axioms WC.fullOracle_measurable
#print axioms WC.parameterized_fullOracle_measurable

-- Definition 4, p. 5: Randomized first-order algorithm
#print axioms WCLB.Model.BorelAlgorithm
#print axioms WCLB.Model.trajectory
#print axioms WC.Model.UnitBorelAlgorithm.extend_trajectory

-- Definition 5, p. 5: Oracle complexity
#print axioms WCLB.Model.hittingTime
#print axioms WCLB.Model.oracleComplexity
#print axioms WCLB.Model.oracleComplexityOn
#print axioms WCLB.Model.oracleComplexityOn_univ
#print axioms WCLB.Model.positiveDimensionalComplexity
#print axioms WCLB.Model.hittingTime_zero_dimension
#print axioms WCLB.Model.positiveDimensionalComplexity_eq

-- Theorem 2, p. 6: Explicit randomized lower bound
#print axioms WCLB.Model.MainTheorem
#print axioms WCLB.small_accuracy_ratios
#print axioms WCLB.physical_hard_instance_logarithmic
#print axioms WCLB.main_explicit
#print axioms WCLB.main
#print axioms WCLB.main_positive_dimension

-- Condition 1, p. 7: Unscaled hard instance properties
#print axioms WCLB.UnscaledHardInstanceConditions
#print axioms WCLB.construction_satisfies_conditions

-- Lemma 1, p. 8: Tilted-block locality
#print axioms WC.euclideanTiltedBlock_frechetSubgradient_locality

-- Lemma 2, p. 10: Variational representation
#print axioms WC.positiveScore_variational
#print axioms WC.coupledFunction_variational
#print axioms WC.weightedCoupledFunction_relay_expansion
#print axioms WC.weightedCoupledFunction_grouped

-- Lemma 3, p. 11: Progress regularity
#print axioms WC.hasGradientAt_euclideanProgress
#print axioms WC.progressGradient_norm_le
#print axioms WC.progressGradient_norm_sub_le
#print axioms WC.monotone_blockProgress
#print axioms WC.blockProgress_nonneg
#print axioms WC.blockProgress_le_one

-- Lemma 4, p. 11: Weak convexity of the coupled function
#print axioms WC.weaklyConvex_smoothBlockTerm
#print axioms WC.weaklyConvex_weightedCoupledFunction
#print axioms WC.weaklyConvex_coupledFunction

-- Proposition 1, p. 12: Majorant regularity
#print axioms WC.chainMajorant_finite
#print axioms WC.chainMajorant_lipschitz
#print axioms WC.chainMajorant_weaklyConvex
#print axioms WC.chainMajorant_lower_bound
#print axioms WC.coupledFunction_coordinate_antitone

-- Lemma 5, p. 13: Complete raw subdifferential
#print axioms WC.subdifferential_coupledFunction_blockwise
#print axioms WC.mem_coupledBlockSubgradients_iff
#print axioms WC.coupledBlockSubgradients_nonempty
#print axioms WC.coupledBlockSubgradients_convex
#print axioms WC.coupledBlockSubgradients_isCompact
#print axioms WC.coupledProgressCoefficient_mem_Icc
#print axioms WC.active_coupled_weight_score_nonneg
#print axioms WCLB.active_weight_characterization

-- Lemma 6, p. 13: Sources and complete majorant subdifferential
#print axioms WC.chainMajorant_sources_nonempty
#print axioms WC.chainMajorant_sources_isCompact
#print axioms WC.chainMajorant_subdifferential
#print axioms WCLB.source_radius_bound

-- Lemma 7, p. 14: Source order and remote singleton
#print axioms WCLB.source_order
#print axioms WCLB.remote_source_subdifferential

-- Proposition 2, p. 14: Robust complete-oracle identity
#print axioms WCLB.robust_oracle_identity
#print axioms WC.chainMajorant_diagonalMask_eq
#print axioms WC.chainMajorant_diagonalMask_subdifferential_eq

-- Fact 1, p. 15: Order, activity and relay gates on unrevealed coordinates
#print axioms WCLB.lastStartedBlock
#print axioms WCLB.fact_one

-- Lemma 8, p. 15: Support of the displacement of a remote maximizing source
#print axioms WCLB.remote_source_displacement

-- Proposition 3, p. 18: Terminal horizon and Moreau stationarity barrier
#print axioms WC.horizon_bound_real
#print axioms WCLB.terminal_diagonal_barrier
#print axioms WCLB.terminal_stationarity

-- Lemma 9, p. 18: Inactive set geometry, source radius and off-set subgradient bound
#print axioms WCLB.inactiveSet
#print axioms WCLB.inactiveSet_eq_terminalRegion
#print axioms WCLB.terminal_geometry
#print axioms WCLB.source_radius_lt_three
#print axioms WCLB.off_terminal_subgradient_lower

-- Proposition 4, p. 22: Initial gap
#print axioms WCLB.initial_gap_le_five
#print axioms WC.chainMajorant_zero
#print axioms WC.chainMajorant_gap
#print axioms WC.chainMajorant_infimum

-- Lemma 10, p. 23: Properties of the radial modification
#print axioms WCLB.radialRadius
#print axioms WCLB.radialObjective
#print axioms WCLB.radial_admissible
#print axioms WCLB.radial_moreau_barrier
#print axioms WCLB.radial_exterior_gradient
#print axioms WCLB.radial_exterior_oracle
#print axioms WCLB.radialObjectiveAt_exterior_fullOracle_eq
#print axioms WCLB.radial_subgradient_inner_lower

-- Lemma 11, p. 26: Randomized reduction
#print axioms WCLB.Concentration.sphere_mgf_le
#print axioms WCLB.Concentration.sphere_projection_tail
#print axioms WCLB.Concentration.adaptive_projection_tail_product
#print axioms WCLB.logarithmicDimensionBound
#print axioms WCLB.logarithmic_dimension_budget_ennreal
#print axioms WCLB.family_barrierEvent_measurable
#print axioms WCLB.joint_barrier_of_exponential_budget
#print axioms WCLB.randomized_reduction
#print axioms WCLB.randomized_reduction_fixed_frame
#print axioms WCLB.physical_joint_barrier_logarithmic

-- Supporting results used in the text and proof constructions.
#print axioms WCLB.unstarted_relay_thresholds
#print axioms WC.diagonal_filtration_width
#print axioms WC.diagonal_quotient_finrank
#print axioms WC.diagonal_initial_space
#print axioms WCLB.radial_prefix_fullOracle
#print axioms WCLB.prefixResponse_measurable
#print axioms WCLB.chainFamily
#print axioms WCLB.family_trajectory_measurable
#print axioms WCLB.family_evaluatedOutput_measurable
#print axioms WCLB.uniformFamilies
