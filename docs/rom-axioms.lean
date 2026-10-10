import Foundation.Constructions.Hash.NativeSimulatorQueryLoadingResources
import Foundation.Constructions.Hash.NativeSimulatorQueryLoading
import Foundation.Crypto.Semantics.Oracle.NativeCodeTapeEquivalence
import Foundation.Constructions.Hash.NativeSimulatorLookupContextRestore
import Foundation.Constructions.Hash.NativeSimulatorLookupRestoredHit
import Foundation.Constructions.Hash.NativeSimulatorLookupRestore
import Foundation.Constructions.Hash.NativeSimulatorLookupDispatchPacket
import Foundation.Constructions.Hash.NativeSimulatorLookupDispatch
import Foundation.Constructions.Hash.NativeSimulatorLookupHitResponse
import Foundation.Constructions.Hash.NativeSimulatorLookupFreshResponse
import Foundation.Constructions.Hash.NativeSimulatorFreshAfterLookupResponse
import Foundation.Constructions.Hash.NativeSimulatorFreshResponse
/- Reproduce with: lake env lean docs/rom-axioms.lean
   This prints dependencies of the checked ROM and hash-security declarations. -/
import Foundation.Constructions.Hash.NativeSimulatorRememberResponse
import Foundation.Constructions.Hash.Indifferentiability
import Foundation.Constructions.Hash.QueryIndifferentiability
import Foundation.Constructions.Hash.WholeExecution
import Foundation.Constructions.Hash.NativeIdealResources
import Foundation.Constructions.Hash.NativeProcedure
import Foundation.Constructions.Hash.NativeRuntimeProcedure
import Foundation.Constructions.Hash.NativeRuntimePacketService
import Foundation.Constructions.Hash.NativeRuntimeLoadedInput
import Foundation.Constructions.Hash.NativeRuntimeLaunchedExecution
import Foundation.Constructions.Hash.NativeRuntimeTransfer
import Foundation.Constructions.Hash.NativeRuntimeEquivalentInput
import Foundation.Constructions.Hash.NativeRuntimeLinkedHash
import Foundation.Constructions.Hash.NativeRuntimeRawExecution
import Foundation.Constructions.Hash.NativeRuntimeCellExport
import Foundation.Constructions.Hash.NativeRuntimeRawExport
import Foundation.Constructions.Hash.NativeRuntimeRawExportTime
import Foundation.Constructions.Hash.NativeRuntimeRawProcedure
import Foundation.Constructions.Hash.NativeRuntimeRawResources
import Foundation.Constructions.Hash.NativeRuntimeRawPacket
import Foundation.Constructions.Hash.NativeRuntimeRawService
import Foundation.Constructions.Hash.NativeRuntimeRawServiceResources
import Foundation.Constructions.Hash.NativePublicWorld
import Foundation.Constructions.Hash.NativePublicWorldService
import Foundation.Constructions.Hash.NativePublicWorldResources
import Foundation.Examples.HeterogeneousWholeOracleAttack
import Foundation.Constructions.Symmetric.SecretPrefixMACConstructedSecurity
import Foundation.Constructions.Symmetric.SecretPrefixMACPublicSecurity
import Foundation.Constructions.Hash.SimulatorInvariant
import Foundation.Constructions.Hash.TrackedReal
import Foundation.Constructions.Hash.IndexedReal
import Foundation.Constructions.Hash.LatentIdeal
import Foundation.Constructions.Hash.LatentRelation
import Foundation.Constructions.Hash.CoordinateTerminal
import Foundation.Constructions.Hash.CoordinateAllocation
import Foundation.Constructions.Hash.LatentPairedStep
import Foundation.Constructions.Hash.LatentStructure
import Foundation.Constructions.Hash.CoordinateInvariant
import Foundation.Constructions.Hash.LatentPublication
import Foundation.Constructions.Hash.LatentLiterals
import Foundation.Constructions.Hash.LatentRecognition
import Foundation.Constructions.Hash.LatentDataLoop
import Foundation.Constructions.Hash.LatentPublicTerminal
import Foundation.Constructions.Hash.FiniteHashWorld
import Foundation.Constructions.Hash.CoupledWorlds
import Foundation.Crypto.Semantics.Oracle.RandomOracleFiniteCollision
import Foundation.Crypto.Semantics.Oracle.FiniteExtension
import Foundation.Crypto.Semantics.Oracle.CoupledRun
import Foundation.Crypto.Semantics.Oracle.FiniteContextRequests
import Foundation.Crypto.Semantics.Oracle.RandomOracleValues
import Foundation.Constructions.Hash.LatentGuessing
import Foundation.Constructions.Hash.LatentResources
import Foundation.Constructions.Hash.LatentGraph
import Foundation.Constructions.Hash.FactoredReal
import Foundation.Constructions.Hash.RealCoordinates
import Foundation.Constructions.Hash.CoordinateRealWorld
import Foundation.Crypto.Semantics.Oracle.FiniteRequests
import Foundation.Constructions.Hash.SimulatorOrder
import Foundation.Constructions.Symmetric.SecretPrefixMACReduction
import Foundation.Crypto.Semantics.Oracle.RandomOracleFinite
import Foundation.Crypto.Semantics.Oracle.RandomOracleReindex
import Foundation.Crypto.Semantics.Probability.Coupling
import Foundation.Constructions.Hash.NativePublicWorldRound

import Foundation.Crypto.Semantics.Oracle.SourcePrefixStraightLine
import Foundation.Crypto.Semantics.Oracle.PacketResponseHalt
import Foundation.Constructions.Hash.NativeAdaptivePublicCaller
import Foundation.Constructions.Hash.NativeAdaptivePublicExecution
import Foundation.Constructions.Hash.NativeAdaptivePublicHalt
import Foundation.Constructions.Hash.NativeAdaptivePublicResources
import Foundation.Constructions.Hash.NativeSimulatorRandom
import Foundation.Constructions.Hash.NativeSimulatorKeyComparison
import Foundation.Constructions.Hash.NativeSimulatorLookupCode
import Foundation.Constructions.Hash.NativeSimulatorLookupStages
import Foundation.Constructions.Hash.NativeSimulatorLookup
import Foundation.Constructions.Hash.NativeSimulatorLookupResources
import Foundation.Constructions.Hash.NativeSimulatorRememberResources
import Foundation.Constructions.Hash.NativeSimulatorFreshAfterLookup
import Foundation.Crypto.Semantics.Oracle.NativeCodeOracleIndependence
import Foundation.Crypto.Semantics.Oracle.PacketWriter
#print axioms CryptoOracle.RandomOracle.adaptive_fresh_joint
#print axioms CryptoOracle.Program.run_observe_trace
#print axioms Foundation.Hash.trackedReal_step_hidden_terminals
#print axioms Foundation.Hash.trackedReal_run_hidden_terminals
#print axioms Foundation.Hash.trackedReal_hidden_terminals_from_empty
#print axioms Foundation.Hash.HiddenTerminalsComplete.unrecognized_fresh
#print axioms Foundation.Hash.trackedReal_public_history
#print axioms Foundation.Hash.coordinate_real_public_execution
#print axioms Foundation.Hash.coordinate_real_local_fresh
#print axioms Foundation.Hash.latent_coordinate_public_known
#print axioms Foundation.Hash.latent_coordinate_terminal_execution
#print axioms Foundation.Hash.coordinate_public_known_pair
#print axioms Foundation.Hash.coordinate_recognized_terminal_pair
#print axioms Foundation.Hash.coordinate_orphan_terminal_pair
#print axioms Foundation.Hash.latent_coordinate_public_record
#print axioms Foundation.Hash.latent_coordinate_public_history
#print axioms Foundation.Hash.tracked_latent_public_same
#print axioms Foundation.Hash.coordinate_equal_history_witness
#print axioms Foundation.Hash.coupled_public_witness
#print axioms Foundation.Hash.LatentState.LiteralAvoids.parent_canonical
#print axioms Foundation.Hash.LatentState.LiteralAvoids.decoded_consistent
#print axioms Foundation.Hash.latentAdvance_real_backend_frame
#print axioms Foundation.Hash.reserveMessage_real_data_loop
#print axioms Foundation.Hash.simulator_data_terminal_consistent
#print axioms Foundation.Hash.coordinate_real_data_terminal_value
#print axioms Foundation.Hash.LatentDataRelation.terminal_transition
#print axioms Foundation.Hash.coordinate_real_high_step
#print axioms Foundation.Hash.latent_coordinate_high_execution
#print axioms Foundation.Hash.coordinate_high_pair
#print axioms Foundation.Hash.finishLatent_supply_of_not_mem
#print axioms Foundation.Hash.coordinate_pending_data_pair
#print axioms Foundation.Hash.coordinate_fresh_data_pair
#print axioms CryptoOracle.RandomOracle.step_entries
#print axioms CryptoOracle.RandomOracle.run_entries
#print axioms CryptoOracle.RandomOracle.unqueried_fresh
#print axioms CryptoOracle.RandomOracle.eager_lazy
#print axioms CryptoOracle.RandomOracle.fresh_guess_bound
#print axioms CryptoOracle.RandomOracle.empty_collision_bound
#print axioms CryptoOracle.RandomOracle.reindex_step
#print axioms CryptoOracle.RandomOracle.reindex_run
#print axioms CryptoOracle.RandomOracle.reindex_result
#print axioms CryptoOracle.Program.stopBefore_run
#print axioms CryptoOracle.Program.stopBeforeAllowed_val
#print axioms CryptoOracle.Program.run_bind
#print axioms CryptoOracle.Program.inline_run
#print axioms Foundation.Hash.DataChain.unique
#print axioms Foundation.Hash.DataChain.length_le
#print axioms Foundation.Hash.messagePrefix_complete
#print axioms Foundation.Hash.compressionSimulator_eq
#print axioms Foundation.Hash.expand_run
#print axioms Foundation.Hash.real_collision_bound
#print axioms Foundation.Hash.real_graph_failure_bound
#print axioms Foundation.Hash.real_search_failure_bound
#print axioms Foundation.Hash.zero_query_advantage
#print axioms Foundation.Symmetric.SecretPrefixMAC.rom_run_sources
#print axioms Foundation.Symmetric.SecretPrefixMAC.rom_unsigned_fresh
#print axioms Foundation.Symmetric.SecretPrefixMAC.romGame_transcript
#print axioms Foundation.Symmetric.SecretPrefixMAC.success_le_key_hit_add_guess
#print axioms Foundation.Symmetric.SecretPrefixMAC.independent_key_hit_bound
#print axioms Foundation.Symmetric.SecretPrefixMAC.allowed_input_injective
#print axioms Foundation.Symmetric.SecretPrefixMAC.stopped_domains_eq
#print axioms Foundation.Symmetric.SecretPrefixMAC.keyHitProbability_eq_separated
#print axioms Foundation.Symmetric.SecretPrefixMAC.rom_security
#print axioms Foundation.Symmetric.SecretPrefixMAC.rom_security_bits
#print axioms CryptoOracle.Program.inlineState_run
#print axioms CryptoOracle.Program.sampleBitsWith_run
#print axioms CryptoOracle.Program.sampleBitsWith_queries
#print axioms Foundation.Hash.WorldBound.mono
#print axioms Foundation.Symmetric.SecretPrefixMAC.hashProcedure_run
#print axioms Foundation.Symmetric.SecretPrefixMAC.compiled_attack_run
#print axioms Foundation.Symmetric.SecretPrefixMAC.checkProgram_run
#print axioms Foundation.Symmetric.SecretPrefixMAC.hashDistinguisherKey_run
#print axioms Foundation.Symmetric.SecretPrefixMAC.hashDistinguisher_run
#print axioms Foundation.Symmetric.SecretPrefixMAC.Budget.compiled_worldBound
#print axioms Foundation.Symmetric.SecretPrefixMAC.worldDistinguisher_bound
#print axioms Foundation.Symmetric.SecretPrefixMAC.worldDistinguisher_real
#print axioms Foundation.Symmetric.SecretPrefixMAC.worldDistinguisher_ideal
#print axioms Foundation.Symmetric.SecretPrefixMAC.reduction_compression_queries
#print axioms Foundation.Symmetric.SecretPrefixMAC.constructed_security_of_indifferentiable
#print axioms Foundation.Probability.eventProb_mono_of_support
#print axioms Foundation.Probability.eventProb_congr_of_support
#print axioms Foundation.Probability.coupled_event_gap_le
#print axioms Foundation.Probability.coupled_map_gap_le
#print axioms CryptoOracle.RandomOracle.Avoided.mono
#print axioms CryptoOracle.RandomOracle.Avoided.append_tail
#print axioms CryptoOracle.RandomOracle.step_avoided_bound
#print axioms CryptoOracle.RandomOracle.run_avoided_bound
#print axioms Foundation.Hash.ForwardFresh.outputs
#print axioms Foundation.Hash.ForwardFresh.no_fixed_point
#print axioms Foundation.Hash.ForwardFresh.no_backward_edge
#print axioms Foundation.Hash.run_forward_failure_bound
#print axioms Foundation.Hash.real_forward_failure_bound
#print axioms Foundation.Hash.DataChain.remove_new_edge
#print axioms Foundation.Hash.simulator_complete_chain
#print axioms Foundation.Hash.no_late_chain
#print axioms Foundation.Hash.no_late_chain_append
#print axioms Foundation.Hash.TerminalConsistent.extend
#print axioms Foundation.Hash.simulator_preserves_terminal
#print axioms Foundation.Hash.ideal_step_private_extends
#print axioms Foundation.Hash.ideal_step_preserves_terminal
#print axioms Foundation.Hash.ideal_run_terminal
#print axioms Foundation.Hash.ideal_run_from_empty
#print axioms Foundation.Hash.ideal_terminal_failure_le_graph_failure
#print axioms CryptoOracle.RandomOracle.eager_lazy_complete
#print axioms CryptoOracle.RandomOracle.eager_unqueried_joint
#print axioms CryptoOracle.RandomOracle.eager_unqueried_guess_list_bound
#print axioms CryptoOracle.RandomOracle.eager_resample_unqueried
#print axioms CryptoOracle.RandomOracle.eager_unqueried_many_guess_bound
#print axioms CryptoOracle.RandomOracle.step_table_extends
#print axioms CryptoOracle.RandomOracle.run_table_extends
#print axioms CryptoOracle.RandomOracle.step_table_subset
#print axioms CryptoOracle.RandomOracle.run_table_subset
#print axioms Foundation.Hash.DataChain.mono
#print axioms Foundation.Hash.DataChain.append
#print axioms Foundation.Hash.DataChain.old_output
#print axioms Foundation.Hash.DataChain.old_output_append
#print axioms Foundation.Hash.iterate_append
#print axioms Foundation.Hash.iterate_data_chain
#print axioms Foundation.Hash.prefixFreeMD_chain
#print axioms Foundation.Hash.compression_step_chain_input
#print axioms Foundation.Hash.trackedRealWorld_project
#print axioms Foundation.Hash.trackedReal_run
#print axioms Foundation.Hash.trackedReal_event
#print axioms Foundation.Hash.PublicConsistent.public_subset
#print axioms Foundation.Hash.trackedReal_step_consistent
#print axioms Foundation.Hash.trackedReal_low_known
#print axioms Foundation.Hash.trackedReal_run_consistent
#print axioms Foundation.Hash.ExposedPaths.not_hidden
#print axioms Foundation.Hash.trackedReal_step_full_extends
#print axioms Foundation.Hash.trackedReal_step_paths
#print axioms Foundation.Hash.trackedReal_step_no_guess
#print axioms Foundation.Hash.trackedReal_run_full_extends
#print axioms Foundation.Hash.trackedReal_run_no_guess
#print axioms Foundation.Hash.trackedReal_run_paths
#print axioms Foundation.Hash.trackedReal_step_completed
#print axioms Foundation.Hash.trackedReal_run_completed
#print axioms Foundation.Hash.trackedReal_from_empty
#print axioms Foundation.Hash.trackedReal_public_search
#print axioms Foundation.Hash.trackedReal_reconstruction_failure_bound
#print axioms Foundation.Hash.privateOrder_bound
#print axioms Foundation.Hash.privateOrder_run
#print axioms Foundation.Hash.privateOrder_failure

#print axioms Foundation.Hash.ForwardFresh.data
#print axioms Foundation.Hash.DataForwardFresh.outputs
#print axioms Foundation.Hash.DataChain.remove_terminal
#print axioms Foundation.Hash.data_no_late_chain
#print axioms CryptoOracle.RandomOracle.TableConsistent.functional
#print axioms CryptoOracle.RandomOracle.TableConsistent.of_functional
#print axioms CryptoOracle.RandomOracle.TableConsistent.subset
#print axioms CryptoOracle.RandomOracle.TableConsistent.cons
#print axioms CryptoOracle.RandomOracle.step_table_consistent
#print axioms CryptoOracle.RandomOracle.run_table_consistent
#print axioms CryptoOracle.RandomOracle.run_empty_table_consistent
#print axioms Foundation.Hash.DataChain.forward_unique
#print axioms Foundation.Hash.DataChain.replay
#print axioms Foundation.Hash.prefixFreeMD_replay
#print axioms Foundation.Hash.trackedReal_step_table_consistent
#print axioms Foundation.Hash.trackedReal_run_table_consistent
#print axioms Foundation.Hash.CompletedPaths.hashes_consistent
#print axioms Foundation.Hash.trackedReal_hashes_consistent
#print axioms Foundation.Hash.CompletedPaths.terminal_agrees
#print axioms Foundation.Hash.trackedReal_high_known
#print axioms Foundation.Hash.trackedReal_terminal_known
#print axioms Foundation.Hash.trackedReal_terminal_simulator
#print axioms Foundation.Hash.terminalMessage_sound
#print axioms Foundation.Hash.iterate_data_terminal_old
#print axioms Foundation.Hash.prefixFreeMD_terminal_entries
#print axioms Foundation.Hash.rememberHash_entries
#print axioms Foundation.Hash.rememberHash_keeps
#print axioms Foundation.Hash.recordLowHash_entries
#print axioms Foundation.Hash.recordLowHash_keeps
#print axioms Foundation.Hash.CompletedPaths.remember_value
#print axioms Foundation.Hash.trackedReal_invariant_failure_bound
#print axioms Foundation.Hash.trackedReal_high_terminal
#print axioms Foundation.Hash.trackedReal_low_terminal
#print axioms Foundation.Hash.trackedReal_step_terminal
#print axioms Foundation.Hash.trackedReal_run_terminal
#print axioms Foundation.Hash.trackedReal_terminal_from_empty
#print axioms Foundation.Hash.trackedReal_exposed_terminal_from_empty
#print axioms Foundation.Hash.trackedReal_terminal_failure_bound
#print axioms Foundation.Hash.trackedReal_new_terminal_fresh
#print axioms Foundation.Hash.trackedReal_new_terminal_ideal
#print axioms Foundation.Hash.trackedReal_terminal_fresh_simulator
#print axioms Foundation.Hash.trackedReal_complete_terminal_simulator
#print axioms CryptoOracle.Program.run_preserves
#print axioms CryptoOracle.Program.run_state_map_of_invariant
#print axioms Foundation.Hash.prefixFreeMD_last_query
#print axioms CryptoOracle.RandomOracle.IndexedTable.erase_lookup
#print axioms CryptoOracle.RandomOracle.IndexedTable.valid_insert
#print axioms CryptoOracle.RandomOracle.IndexedTable.erase_insert
#print axioms CryptoOracle.RandomOracle.IndexedTable.erase_fallback
#print axioms CryptoOracle.RandomOracle.IndexedTable.step_valid
#print axioms CryptoOracle.RandomOracle.IndexedTable.step_erase
#print axioms CryptoOracle.RandomOracle.IndexedTable.run_erase
#print axioms CryptoOracle.RandomOracle.IndexedTable.run_valid
#print axioms CryptoOracle.RandomOracle.IndexedTable.step_records
#print axioms CryptoOracle.RandomOracle.IndexedTable.step_values_extend
#print axioms CryptoOracle.RandomOracle.IndexedTable.run_values_extend
#print axioms CryptoOracle.RandomOracle.IndexedTable.bounded_values
#print axioms CryptoOracle.RandomOracle.IndexedTable.run_response_label
#print axioms Foundation.Hash.publishIndex_valid
#print axioms Foundation.Hash.indexedReal_step_valid
#print axioms Foundation.Hash.indexedReal_step_erase
#print axioms Foundation.Hash.indexedReal_run_erase
#print axioms Foundation.Hash.indexedReal_terminal_from_empty
#print axioms Foundation.Hash.indexedReal_step_public_valid
#print axioms Foundation.Hash.indexedReal_run_valid
#print axioms Foundation.Hash.indexedReal_low_publishes
#print axioms Foundation.Hash.indexedReal_bounded_values
#print axioms Foundation.Hash.indexedReal_high_publishes
#print axioms Foundation.Hash.LatentFrame.trans
#print axioms Foundation.Hash.LatentFrame.freshSupply
#print axioms Foundation.Hash.reserveLabel_frame
#print axioms Foundation.Hash.reserveLabel_fresh
#print axioms Foundation.Hash.latentAdvance_frame
#print axioms Foundation.Hash.reserveMessage_frame
#print axioms Foundation.Hash.chooseLatent_frame
#print axioms Foundation.Hash.chooseLatent_fresh
#print axioms Foundation.Hash.finishLatent_freshSupply
#print axioms Foundation.Hash.latentWorld_eq
#print axioms Foundation.Hash.latentProgram_queries
#print axioms Foundation.Hash.latent_step_coherent
#print axioms Foundation.Hash.latent_step_project
#print axioms Foundation.Hash.latent_run_coherent
#print axioms Foundation.Hash.latent_run_project
#print axioms Foundation.Hash.latent_empty_coherent
#print axioms Foundation.Hash.latent_candidate_run
#print axioms Foundation.Hash.latent_inline_run
#print axioms Foundation.Hash.latent_backend_context
#print axioms Foundation.Hash.latent_compiled_run
#print axioms Foundation.Hash.latent_compiled_coherent
#print axioms Foundation.Hash.latent_unrevealed_joint
#print axioms Foundation.Hash.latent_compiled_queries
#print axioms Foundation.Hash.unrevealedLabels_fresh
#print axioms Foundation.Hash.unrevealedLabels_length
#print axioms Foundation.Hash.latent_unrevealed_guess_bound
#print axioms Foundation.Hash.latent_unrevealed_resample
#print axioms CryptoOracle.RandomOracle.eager_context_run_congr
#print axioms CryptoOracle.RandomOracle.eager_lazy_complete_context
#print axioms CryptoOracle.RandomOracle.eager_unqueried_joint_context
#print axioms CryptoOracle.RandomOracle.eager_resample_unqueried_context
#print axioms CryptoOracle.RandomOracle.eager_unqueried_many_guess_bound_context
#print axioms Foundation.Hash.compressionSimulator_terminal_eq
#print axioms CryptoOracle.Program.inlineState_queries
#print axioms CryptoOracle.RandomOracle.uniform_complete_many_guess_bound
#print axioms Foundation.Hash.nextLowGuesses_length
#print axioms Foundation.Hash.latent_prefixHit_iff
#print axioms Foundation.Hash.latent_prefix_guess_bound
#print axioms Foundation.Hash.latent_first_guess_bound
#print axioms Foundation.Hash.latent_online_guess_bound
#print axioms Foundation.Hash.latent_eager_run
#print axioms Foundation.Hash.latent_eager_candidate_result
#print axioms Foundation.Hash.latent_monitored_candidate_result
#print axioms CryptoOracle.Program.monitor_run_erase
#print axioms CryptoOracle.Program.monitor_firstHit
#print axioms CryptoOracle.Program.firstHit_prefix_bound
#print axioms CryptoOracle.Program.firstHit_mixed_bound
#print axioms CryptoOracle.Program.queryPrefix_queries
#print axioms CryptoOracle.Program.queryPrefix_trace
#print axioms Foundation.Hash.latent_coordinate_lazy
#print axioms Foundation.Hash.latent_compiled_coordinates
#print axioms CryptoOracle.RandomOracle.eager_lazy_context
#print axioms Foundation.Probability.eventProb_bind_eq

#print axioms Foundation.Hash.AllocationBound.refl
#print axioms Foundation.Hash.AllocationBound.mono
#print axioms Foundation.Hash.AllocationBound.trans
#print axioms Foundation.Hash.AllocationBound.graph_cons
#print axioms Foundation.Hash.reserveLabel_allocation
#print axioms Foundation.Hash.reserveLabel_selected_unused
#print axioms Foundation.Hash.latentAdvance_allocation
#print axioms Foundation.Hash.reserveMessage_allocation
#print axioms Foundation.Hash.chooseLatent_allocation
#print axioms Foundation.Hash.chooseLatent_selected_unused
#print axioms Foundation.Hash.finishLatent_allocation
#print axioms Foundation.Hash.choose_finish_allocation
#print axioms Foundation.Hash.latent_step_allocation
#print axioms Foundation.Hash.latent_run_allocation
#print axioms Foundation.Hash.latent_empty_allocation
#print axioms Foundation.Hash.latent_no_overflow
#print axioms Foundation.Hash.latent_fin_capacity
#print axioms Foundation.Hash.latent_eager_no_overflow
#print axioms Foundation.Hash.latent_budgeted_online_guess_bound
#print axioms Foundation.Hash.latentDecodedGraph_mono
#print axioms Foundation.Hash.reserveLabel_graph
#print axioms Foundation.Hash.reserveLabel_none_overflow
#print axioms Foundation.Hash.latentAdvance_graph_subset
#print axioms Foundation.Hash.reserveMessage_graph_subset
#print axioms Foundation.Hash.latentAdvance_graph_consistent
#print axioms Foundation.Hash.reserveMessage_graph_consistent
#print axioms Foundation.Hash.chooseLatent_graph_consistent
#print axioms Foundation.Hash.finishLatent_graph
#print axioms Foundation.Hash.latent_step_graph_consistent
#print axioms Foundation.Hash.latent_run_graph_consistent
#print axioms Foundation.Hash.latentAdvance_decoded_edge
#print axioms Foundation.Hash.reserveMessage_decoded_chain
#print axioms Foundation.Hash.latentDecodedGraph_consistent
#print axioms Foundation.Hash.reserveMessage_decoded_replay

#print axioms Foundation.Hash.CompletedPaths.hash_fresh_of_terminal_fresh
#print axioms Foundation.Hash.compressionSimulator_full_project
#print axioms Foundation.Hash.compressionSimulator_full_preserves
#print axioms Foundation.Hash.compressionSimulator_full_run
#print axioms Foundation.Hash.factored_real_resultState
#print axioms Foundation.Hash.factored_real_compiled
#print axioms Foundation.Hash.factored_real_compiled_queries

#print axioms Foundation.Hash.realCoordinateWorld_eq
#print axioms Foundation.Hash.realCoordinate_step_project
#print axioms Foundation.Hash.realCoordinate_step_valid
#print axioms Foundation.Hash.realCoordinate_run_project
#print axioms Foundation.Hash.real_coordinate_inline
#print axioms Foundation.Hash.real_coordinate_compiled
#print axioms Foundation.Hash.real_coordinate_eager
#print axioms Foundation.Hash.real_coordinate_real_marginal
#print axioms Foundation.Hash.realCoordinateProgram_queries
#print axioms Foundation.Hash.real_coordinate_compiled_queries
#print axioms Foundation.Hash.realCoordinate_step_resource
#print axioms Foundation.Hash.realCoordinate_run_resource
#print axioms Foundation.Hash.real_coordinate_compiled_no_fallback
#print axioms Foundation.Hash.real_coordinate_fin_capacity
#print axioms Foundation.Hash.real_coordinate_possible_no_fallback
#print axioms CryptoOracle.Program.possibleRequests_query
#print axioms CryptoOracle.Program.possibleRequests_next
#print axioms CryptoOracle.Program.possibleRequests_coin
#print axioms CryptoOracle.Program.restrictTo_val
#print axioms CryptoOracle.Program.restrictTo_queries
#print axioms CryptoOracle.RandomOracle.finite_restriction_run
#print axioms CryptoOracle.RandomOracle.finite_restriction_eager

#print axioms Foundation.Hash.coordinate_real_compiled
#print axioms Foundation.Hash.coordinate_real_eager_marginal
#print axioms Foundation.Hash.coordinate_real_fin_capacity

#print axioms CryptoOracle.RandomOracle.TableValues.lookup
#print axioms CryptoOracle.RandomOracle.eager_step_values
#print axioms CryptoOracle.RandomOracle.eager_context_step_values
#print axioms CryptoOracle.RandomOracle.eager_context_run_values
#print axioms Foundation.Hash.latent_eager_coherent
#print axioms Foundation.Hash.latent_eager_revealed_values
#print axioms Foundation.Hash.revealed_inverse_entry
#print axioms Foundation.Hash.revealed_inverse_consistent
#print axioms Foundation.Hash.revealed_inverse_lookup
#print axioms Foundation.Hash.latentParent_value
#print axioms Foundation.Hash.latentParent_revealed
#print axioms Foundation.Hash.latentParent_hidden
#print axioms Foundation.Hash.LatentDataRelation.known
#print axioms Foundation.Hash.LatentDataRelation.fresh
#print axioms Foundation.Hash.LatentDataRelation.pending
#print axioms Foundation.Hash.LatentDataRelation.choose_known
#print axioms Foundation.Hash.LatentDataRelation.hidden_coordinate
#print axioms Foundation.Hash.LatentDataRelation.hidden_guess
#print axioms Foundation.Hash.latentParent_canonical
#print axioms Foundation.Hash.LatentDataRelation.data_lookup

#print axioms Foundation.Hash.LatentDataRelation.reserve_edge
#print axioms Foundation.Hash.latentAdvance_data_relation
#print axioms Foundation.Hash.coordinate_real_data_fresh
#print axioms Foundation.Hash.coordinate_real_known
#print axioms Foundation.Hash.latentAdvance_real_step

#print axioms Foundation.Hash.LatentState.ChildrenUnique.cons
#print axioms Foundation.Hash.latentAdvance_children_unique
#print axioms Foundation.Hash.reserveMessage_children_unique
#print axioms Foundation.Hash.chooseLatent_children_unique
#print axioms Foundation.Hash.finishLatent_children_unique
#print axioms Foundation.Hash.latent_step_children_unique
#print axioms Foundation.Hash.latent_run_children_unique
#print axioms Foundation.Hash.LatentDataRelation.publish
#print axioms Foundation.Hash.LatentDataRelation.publish_data
#print axioms Foundation.Hash.latent_eager_children_unique
#print axioms Foundation.Hash.LatentDataRelation.terminal_row
#print axioms Foundation.Hash.LatentDataRelation.publish_none
#print axioms Foundation.Hash.LatentDataRelation.publish_pending
#print axioms Foundation.Hash.latent_pending_data_execution
#print axioms Foundation.Hash.LatentDataRelation.publish_orphan
#print axioms Foundation.Hash.finishLatent_values
#print axioms Foundation.Hash.coordinate_real_terminal_recognized

#print axioms Foundation.Hash.latentParent_finish_away
#print axioms Foundation.Hash.finishLatent_literal_stable

#print axioms CryptoOracle.Program.run_support_state_map
#print axioms Foundation.Hash.LatentDataRelation.chain_to_real
#print axioms Foundation.Hash.LatentDataRelation.chain_from_real
#print axioms Foundation.Hash.LatentDataRelation.visible
#print axioms Foundation.Hash.messagePrefix_eq_of_reconstructible
#print axioms Foundation.Hash.terminalMessage_eq_of_reconstructible
#print axioms Foundation.Hash.LatentDataRelation.terminal_recognition
#print axioms Foundation.Hash.simulator_step_support
#print axioms Foundation.Hash.simulator_run_support
#print axioms Foundation.Hash.coordinate_real_step_support
#print axioms Foundation.Hash.coordinate_real_run_support
#print axioms Foundation.Hash.coordinate_real_tracked_witness

#print axioms CryptoOracle.Program.mem_rightRequests
#print axioms CryptoOracle.Program.restrictRightTo_val
#print axioms CryptoOracle.Program.restrictRightTo_queries
#print axioms CryptoOracle.RandomOracle.reindex_context_step
#print axioms CryptoOracle.RandomOracle.reindex_context_run
#print axioms CryptoOracle.RandomOracle.finite_context_restriction_run
#print axioms CryptoOracle.RandomOracle.finite_context_restriction_eager
#print axioms Foundation.Hash.finite_hash_reorder_step
#print axioms Foundation.Hash.finite_hash_reorder_run
#print axioms Foundation.Hash.finite_hash_execution
#print axioms Foundation.Hash.coordinateHashDomain_real
#print axioms Foundation.Hash.coordinateHashDomain_ideal
#print axioms Foundation.Hash.finite_hash_real_execution
#print axioms Foundation.Hash.finite_hash_ideal_execution

#print axioms Foundation.Probability.support_witness_of_mixture_map_eq

#print axioms CryptoOracle.RandomOracle.extendFinite_apply
#print axioms CryptoOracle.RandomOracle.reindex_eager_step
#print axioms CryptoOracle.RandomOracle.reindex_eager_context_step
#print axioms CryptoOracle.RandomOracle.reindex_eager_context_run
#print axioms CryptoOracle.RandomOracle.finite_context_extension_run
#print axioms CryptoOracle.RandomOracle.finite_context_extension_eager

#print axioms Foundation.Hash.finite_hash_total_execution
#print axioms Foundation.Hash.finite_total_real_execution
#print axioms Foundation.Hash.finite_total_ideal_execution
#print axioms Foundation.Hash.finite_total_real_support
#print axioms Foundation.Hash.finite_total_ideal_support
#print axioms Foundation.Hash.finite_total_ideal_invariants
#print axioms Foundation.Hash.finite_total_real_fin_capacity

#print axioms CryptoOracle.Program.independentRuns_left
#print axioms CryptoOracle.Program.independentRuns_right
#print axioms CryptoOracle.Program.coupledRun_marginals
#print axioms CryptoOracle.Program.coupledRun_result_eq_of_trace_eq

#print axioms Foundation.Hash.coupled_coordinate_real_marginal
#print axioms Foundation.Hash.coupled_coordinate_ideal_marginal
#print axioms Foundation.Hash.coupled_real_marginal
#print axioms Foundation.Hash.coupled_ideal_marginal
#print axioms Foundation.Hash.coupled_world_result_eq
#print axioms Foundation.Hash.coupled_hash_gap_le

#print axioms Foundation.Hash.coupled_online_guess_bound
#print axioms Foundation.Hash.coupled_forward_failure_bound
#print axioms Foundation.Hash.coupled_forward_or_guess_bound
#print axioms Foundation.Hash.latent_empty_literal_avoids
#print axioms Foundation.Hash.LatentState.LiteralAvoids.stable
#print axioms Foundation.Hash.latentParent_literal_avoids
#print axioms Foundation.Hash.reserveLabel_literal_avoids
#print axioms Foundation.Hash.latentAdvance_literal_avoids
#print axioms Foundation.Hash.latentAdvance_parent_safe
#print axioms Foundation.Hash.reserveMessage_literal_avoids
#print axioms Foundation.Hash.chooseLatent_literal_avoids
#print axioms Foundation.Hash.finishLatent_literal_avoids
#print axioms Foundation.Hash.latentProgram_literal_avoids
#print axioms Foundation.Hash.latent_coordinate_step_literal_avoids
#print axioms Foundation.Hash.latentGuessHit_no_guess

#print axioms CryptoOracle.RandomOracle.eager_step_support
#print axioms CryptoOracle.RandomOracle.eager_context_step_support
#print axioms CryptoOracle.RandomOracle.eager_run_support
#print axioms CryptoOracle.RandomOracle.readCoordinates_queries
#print axioms CryptoOracle.RandomOracle.readCoordinates_stored
#print axioms CryptoOracle.RandomOracle.fresh_complete_function
#print axioms CryptoOracle.RandomOracle.uniform_function_bad_bound
#print axioms Foundation.Hash.latent_coordinate_eager_step_coherent
#print axioms Foundation.Hash.latent_coordinate_eager_step_values
#print axioms Foundation.Hash.latent_monitored_run_invariants
#print axioms Foundation.Hash.latent_monitored_run_literal_stable
#print axioms Foundation.Hash.coupled_literal_stable
#print axioms Foundation.Hash.coupled_coordinates_marginal
#print axioms Foundation.Hash.coupled_coordinates_bad_bound
#print axioms Foundation.Hash.coupled_coordinate_or_forward_or_guess_bound

#print axioms Foundation.Hash.real_coordinate_backend_hash_support
#print axioms Foundation.Hash.coordinate_compression_hash_support
#print axioms Foundation.Hash.compression_simulator_run_terminal
#print axioms Foundation.Hash.coordinate_real_run_terminal
#print axioms Foundation.Hash.coordinate_real_terminal_from_empty
#print axioms Foundation.Hash.coupled_real_terminal

#print axioms Foundation.Hash.real_coordinate_backend_hash_values
#print axioms Foundation.Hash.coordinate_compression_hash_values
#print axioms Foundation.Hash.coordinate_real_run_hash_values
#print axioms Foundation.Hash.coupled_real_hash_values

#print axioms Foundation.Hash.real_coordinate_eager_step_support
#print axioms Foundation.Hash.real_coordinate_eager_step_invariants
#print axioms Foundation.Hash.coordinate_compression_allocation_invariants
#print axioms Foundation.Hash.coordinate_real_step_allocation_invariants
#print axioms Foundation.Hash.coordinate_real_run_allocation_invariants
#print axioms Foundation.Hash.coordinate_real_allocation_from_empty
#print axioms Foundation.Hash.trackedReal_step_visible
#print axioms Foundation.Hash.LatentDataRelation.tracked_step_paths
#print axioms Foundation.Hash.coordinate_paired_tracked_step
#print axioms Foundation.Hash.coupled_real_allocation_invariants

#print axioms Foundation.Hash.coordinate_pair_step

#print axioms Foundation.Hash.latent_coordinate_eager_step_support
#print axioms Foundation.Hash.latent_coordinate_eager_run_support
#print axioms Foundation.Hash.latent_coordinate_step_allocation
#print axioms Foundation.Hash.latent_coordinate_run_allocation
#print axioms Foundation.Hash.latent_coordinate_step_children_unique
#print axioms Foundation.Hash.latent_coordinate_run_structural
#print axioms Foundation.Hash.latent_coordinate_structural_from_empty
#print axioms Foundation.Hash.WorldBound.query_cost
#print axioms Foundation.Hash.latent_coordinate_step_capacity
#print axioms Foundation.Hash.latent_coordinate_backend_hash_values
#print axioms Foundation.Hash.latent_coordinate_step_hash_values
#print axioms Foundation.Hash.latent_coordinate_run_hash_values
#print axioms Foundation.Hash.coupled_coordinate_support
#print axioms Foundation.Hash.coupled_ideal_structural

#print axioms Foundation.Hash.coordinate_pair_invariant_empty
#print axioms Foundation.Hash.coordinate_pair_invariant_step

#print axioms CryptoOracle.Program.monitor_run_unmarked
#print axioms Foundation.Hash.coordinate_real_step_extends
#print axioms Foundation.Hash.coordinate_real_run_extends
#print axioms Foundation.Hash.coordinate_coupled_trace_eq
#print axioms Foundation.Hash.coupled_trace_eq_of_good
#print axioms Foundation.Hash.candidate_gap_bound
#print axioms Foundation.Hash.prefixFreeMD_query_indifferentiable
#print axioms Foundation.Symmetric.SecretPrefixMAC.constructed_security

#print axioms CryptoOracle.Program.sampleBitsWith_bind
#print axioms Foundation.Symmetric.SecretPrefixMAC.publicDistinguisher_run
#print axioms Foundation.Symmetric.SecretPrefixMAC.PublicBudget.distinguisher_bound
#print axioms Foundation.Symmetric.SecretPrefixMAC.simulatorROMHandler_run
#print axioms Foundation.Symmetric.SecretPrefixMAC.compiledSimulator_run
#print axioms Foundation.Symmetric.SecretPrefixMAC.mergeProcedure_step
#print axioms Foundation.Symmetric.SecretPrefixMAC.mergeAttack_run
#print axioms Foundation.Symmetric.SecretPrefixMAC.mergeAttack_game
#print axioms Foundation.Symmetric.SecretPrefixMAC.Budget.mono_counts
#print axioms Foundation.Symmetric.SecretPrefixMAC.Budget.sampleBitsWith
#print axioms Foundation.Symmetric.SecretPrefixMAC.simulator_message_length
#print axioms Foundation.Symmetric.SecretPrefixMAC.PublicBudget.merged_budget
#print axioms Foundation.Symmetric.SecretPrefixMAC.PublicBudget.merged_from_empty
#print axioms Foundation.Symmetric.SecretPrefixMAC.simulated_rom_security
#print axioms Foundation.Symmetric.SecretPrefixMAC.public_reduction_compression_queries
#print axioms Foundation.Symmetric.SecretPrefixMAC.public_constructed_security

#print axioms CryptoOracle.WholeWitness.trace_length_le
#print axioms CryptoOracle.WholeWitness.mono
#print axioms CryptoOracle.WholeSecure.mono
#print axioms CryptoOracle.WholeReduction.compiler_halts
#print axioms CryptoOracle.WholeReduction.realizes_emitted
#print axioms CryptoOracle.WholeReduction.secure
#print axioms CryptoOracle.WholeReduction.id
#print axioms CryptoOracle.WholeReduction.comp
#print axioms CryptoLogic.General.Backends.Interactive.original_witness
#print axioms CryptoOracle.Examples.Heterogeneous.right_typed_run
#print axioms CryptoOracle.Examples.Heterogeneous.right_code_run
#print axioms CryptoOracle.Examples.Heterogeneous.witness
#print axioms CryptoOracle.Examples.Heterogeneous.backend_code
#print axioms Foundation.Hash.whole_high_packet_length
#print axioms Foundation.Hash.whole_low_packet_length
#print axioms Foundation.Hash.whole_result_gap

-- Native specialized prefix-free hash: code, full execution, stopping and encoded peak.
#print axioms CryptoOracle.Interactive.CallExecution.sending_run
#print axioms CryptoOracle.Interactive.CallExecution.reversing_run
#print axioms CryptoOracle.Interactive.CallExecution.run
#print axioms CryptoOracle.Interactive.StraightLine.public_one
#print axioms CryptoOracle.Interactive.StraightLine.public_run
#print axioms Foundation.Hash.Native.initializeActions_length
#print axioms Foundation.Hash.Native.initialize_execute
#print axioms Foundation.Hash.Native.initialized_run
#print axioms Foundation.Hash.Native.initialized_halts
#print axioms Foundation.Hash.Native.iterationSteps_fixed_width
#print axioms Foundation.Hash.Native.iterate_encoded_run
#print axioms Foundation.Hash.Native.prefixFree_run
#print axioms Foundation.Hash.Native.prefixFree_steps
#print axioms Foundation.Hash.Native.fixedBits_length
#print axioms Foundation.Hash.Native.fixedBits_decode_exists
#print axioms Foundation.Hash.Native.compression_packet_valid
#print axioms Foundation.Hash.Native.tableEncoding_length
#print axioms Foundation.Hash.Native.idealCompression_growth
#print axioms Foundation.Hash.Native.ideal_prefixFree_run
#print axioms Foundation.Hash.Native.ideal_prefixFree_halts
#print axioms Foundation.Hash.Native.ideal_prefixFree_encoded_peak
#print axioms Foundation.Hash.Native.iteration_run
#print axioms Foundation.Hash.Native.writeActions_length
#print axioms Foundation.Hash.Native.rightActions_length
#print axioms Foundation.Hash.Native.leftActions_length
#print axioms Foundation.Hash.Native.write_execute
#print axioms Foundation.Hash.Native.right_execute
#print axioms Foundation.Hash.Native.left_execute
#print axioms Foundation.Hash.Native.prepareActions_length
#print axioms Foundation.Hash.Native.prepare_execute
#print axioms Foundation.Hash.Native.prepare_run
#print axioms Foundation.Hash.Native.compressionCode_length
#print axioms Foundation.Hash.Native.compression_run

-- Typed compression representation and actual first-arrival execution certificates.
#print axioms Foundation.Hash.Native.compressionKey_encode
#print axioms Foundation.Hash.Native.compressionKey_decode
#print axioms Foundation.Hash.Native.compressionKey_injective
#print axioms Foundation.Hash.Native.typed_compression_step
#print axioms Foundation.Hash.Native.iterate_encoded_state_run
#print axioms Foundation.Hash.Native.typed_prefixFree_run
#print axioms Foundation.Hash.Native.loaded_bits
#print axioms Foundation.Hash.Native.typedHashFinish_packet
#print axioms Foundation.Hash.Native.typed_prefixFree_output
#print axioms Foundation.Hash.Native.typed_prefixFree_halts
#print axioms Foundation.Hash.Native.iterate_trace_length
#print axioms Foundation.Hash.Native.typed_prefixFree_queries
#print axioms Foundation.Hash.Native.typed_prefixFree_encoded_peak
#print axioms Foundation.Hash.Native.fixedProcedure_exit
#print axioms Foundation.Hash.Native.stoppedProcedure_costed
#print axioms Foundation.Hash.Native.stoppedProcedure_correct
#print axioms Foundation.Hash.Native.stoppedProcedure_bounded
#print axioms Foundation.Hash.Native.stoppedProcedure_halted
#print axioms Foundation.Hash.Native.stoppedProcedure_encoded_peak
#print axioms Foundation.Hash.Native.fixedProcedure
#print axioms Foundation.Hash.Native.stoppedProcedure

-- Runtime-input common hash code, joint semantics, stopping and peak storage.
#print axioms CryptoOracle.Interactive.FixedWidthCopy.cellCode_length
#print axioms CryptoOracle.Interactive.FixedWidthCopy.code_length
#print axioms CryptoOracle.Interactive.FixedWidthCopy.cell_run
#print axioms CryptoOracle.Interactive.FixedWidthCopy.frontier_move
#print axioms CryptoOracle.Interactive.FixedWidthCopy.run
#print axioms Foundation.Hash.Native.runtimePrefix_length
#print axioms Foundation.Hash.Native.runtimePrefix_execute
#print axioms Foundation.Hash.Native.runtimePrepareCode_length
#print axioms Foundation.Hash.Native.runtime_prepare_run
#print axioms Foundation.Hash.Native.runtimeDataCode_length
#print axioms Foundation.Hash.Native.runtime_data_run
#print axioms Foundation.Hash.Native.runtimeLoopCode_length
#print axioms Foundation.Hash.Native.runtime_native_one
#print axioms Foundation.Hash.Native.runtime_branch_lookup
#print axioms Foundation.Hash.Native.runtime_jump_lookup
#print axioms Foundation.Hash.Native.runtime_halt_lookup
#print axioms Foundation.Hash.Native.runtime_loop_data
#print axioms Foundation.Hash.Native.runtime_loop_terminal
#print axioms Foundation.Hash.Native.runtime_loop_run
#print axioms Foundation.Hash.Native.runtimeInput_tape
#print axioms Foundation.Hash.Native.runtime_initialized_run
#print axioms Foundation.Hash.Native.runtime_prefixFree_run
#print axioms Foundation.Hash.Native.runtime_prefixFree_halts
#print axioms Foundation.Hash.Native.runtimeHashCode_length
#print axioms Foundation.Hash.Native.runtimeHashSteps_formula
#print axioms Foundation.Hash.Native.typed_runtime_prefixFree_run
#print axioms Foundation.Hash.Native.typed_runtime_prefixFree_output
#print axioms Foundation.Hash.Native.typed_runtime_prefixFree_halts
#print axioms Foundation.Hash.Native.typed_runtime_prefixFree_queries
#print axioms Foundation.Hash.Native.typed_runtime_prefixFree_encoded_peak
#print axioms Foundation.Hash.Native.runtimeFixedProcedure_exit
#print axioms Foundation.Hash.Native.runtimeStoppedProcedure_costed
#print axioms Foundation.Hash.Native.runtimeStoppedProcedure_correct
#print axioms Foundation.Hash.Native.runtimeStoppedProcedure_bounded
#print axioms Foundation.Hash.Native.runtimeStoppedProcedure_halted
#print axioms Foundation.Hash.Native.runtimeStoppedProcedure_encoded_peak
#print axioms Foundation.Hash.Native.runtimeFixedProcedure
#print axioms Foundation.Hash.Native.runtimeStoppedProcedure

-- Physical output export and prepared native caller service.
#print axioms Machine.ResponseExport.run_fromHead
#print axioms CryptoOracle.Interactive.NativePacketComponent.ready_absorbing
#print axioms CryptoOracle.Interactive.NativePacketComponent.exporting_run
#print axioms CryptoOracle.Interactive.NativePacketComponent.export_run
#print axioms Foundation.Hash.Native.typedHashFinish_exportable
#print axioms Foundation.Hash.Native.runtimeExportable_support
#print axioms Foundation.Hash.Native.runtimeExportCertified
#print axioms Foundation.Hash.Native.runtimePacketBody
#print axioms Foundation.Hash.Native.runtimePacketDelivery
#print axioms Foundation.Hash.Native.runtimePacketWhole
#print axioms Foundation.Hash.Native.runtimePacketProcedure
#print axioms Foundation.Hash.Native.runtimePacketProcedure_budget
#print axioms Foundation.Hash.Native.runtimePacketProcedure_semantics
#print axioms Foundation.Hash.Native.runtimePacketProcedure_response_length
#print axioms Foundation.Hash.Native.runtimePacketHandler
#print axioms Foundation.Hash.Native.runtimeHashService
#print axioms Foundation.Hash.Native.runtimeHashService_entry
#print axioms Foundation.Hash.Native.runtimeHashService_budget
#print axioms Foundation.Hash.Native.runtimeHashService_semantics
#print axioms Foundation.Hash.Native.runtimeHashService_costed
#print axioms Foundation.Hash.Native.runtimeHashService_law

-- Exact framed input and the represented trailing loader blank.
#print axioms Foundation.Hash.Native.runtime_initialized_framed_run
#print axioms Foundation.Hash.Native.runtime_prefixFree_framed_run
#print axioms Foundation.Hash.Native.typed_runtime_prefixFree_framed_run
#print axioms Foundation.Hash.Native.runtimeLoadedFrame
#print axioms Foundation.Hash.Native.runtimeLoadedFinalInput
#print axioms Foundation.Hash.Native.typed_runtime_loaded_run
#print axioms Foundation.Hash.Native.typed_runtime_loaded_halts
#print axioms Foundation.Hash.Native.typed_runtime_loaded_queries
#print axioms Foundation.Hash.Native.typed_runtime_loaded_encoded_peak

-- Actual raw loading, ownership handoff and native first-halt execution.
#print axioms CryptoOracle.Interactive.NativePacketLaunch.step
#print axioms CryptoOracle.Interactive.NativePacketLaunch.handoffFrame
#print axioms CryptoOracle.Interactive.NativePacketLaunch.preparation_first_joint
#print axioms CryptoOracle.Interactive.NativePacketLaunch.launch_first_joint
#print axioms CryptoOracle.Interactive.NativePacketLaunch.launch_continues
#print axioms Foundation.Hash.Native.typed_runtime_input_length
#print axioms Foundation.Hash.Native.typed_runtime_launch_first_joint
#print axioms Foundation.Hash.Native.typed_runtime_launch_continues
#print axioms Foundation.Hash.Native.launchedHashBoundary
#print axioms Foundation.Hash.Native.runtimePreparationSteps
#print axioms Foundation.Hash.Native.launched_hash_stopped
#print axioms Foundation.Hash.Native.launched_hash_first_joint
#print axioms Foundation.Hash.Native.loaded_hash_stopped_frames
#print axioms Foundation.Hash.Native.launched_hash_frames
#print axioms Foundation.Hash.Native.launched_hash_continues

-- Real native request transfer and native-to-interactive execution.
#print axioms Machine.NativeRequestTransfer.native
#print axioms Machine.NativeRequestTransfer.input
#print axioms Machine.NativeRequestTransfer.component
#print axioms Machine.NativeRequestTransfer.fixedCode
#print axioms Machine.NativeRequestTransfer.component_code
#print axioms Machine.NativeRequestTransfer.code_length
#print axioms Machine.NativeRequestTransfer.component_entry
#print axioms Machine.NativeRequestTransfer.component_budget
#print axioms Machine.NativeRequestTransfer.supported_layout
#print axioms Machine.NativeRequestTransfer.run
#print axioms Machine.NativeRequestTransfer.first_joint
#print axioms Machine.NativeRequestTransfer.first_layout
#print axioms Machine.NativeRequestTransfer.first_bounded
#print axioms Machine.NativeRequestTransfer.initial_cells
#print axioms Machine.NativeRequestTransfer.storage_peak
#print axioms Machine.NativeRequestTransfer.space_polynomial
#print axioms CryptoOracle.Interactive.NativeCode.code
#print axioms CryptoOracle.Interactive.NativeCode.frame
#print axioms CryptoOracle.Interactive.NativeCode.running_step
#print axioms CryptoOracle.Interactive.NativeCode.first_joint
#print axioms Foundation.Hash.Native.runtimeTransferCode
#print axioms Foundation.Hash.Native.runtimeTransferSteps
#print axioms Foundation.Hash.Native.runtimeTransferStart
#print axioms Foundation.Hash.Native.runtime_transfer_first_joint
#print axioms Foundation.Hash.Native.runtime_transfer_layout
#print axioms Foundation.Hash.Native.runtime_transfer_encoded_peak

-- Cell equivalence retains genuine interactive timing and complete history.
#print axioms CryptoOracle.Interactive.CellEquivalence.Related
#print axioms CryptoOracle.Interactive.CellEquivalence.Frames
#print axioms CryptoOracle.Interactive.CellEquivalence.terminal
#print axioms CryptoOracle.Interactive.CellEquivalence.perform_bind
#print axioms CryptoOracle.Interactive.CellEquivalence.timed_bind
#print axioms CryptoOracle.Interactive.CellEquivalence.eval_map
#print axioms CryptoOracle.Interactive.CellEquivalence.first_map
#print axioms CryptoOracle.Interactive.CellEquivalence.packetObservation
#print axioms CryptoOracle.Interactive.CellEquivalence.packet_eq
#print axioms CryptoOracle.Interactive.CellEquivalence.appendTrace
#print axioms CryptoOracle.Interactive.CellEquivalence.eval_appendTrace
#print axioms Foundation.Hash.Native.typed_runtime_equivalent_packet
#print axioms Foundation.Hash.Native.typed_runtime_equivalent_halts
#print axioms Foundation.Hash.Native.runtime_transfer_hash_entry
#print axioms Foundation.Hash.Native.runtime_transfer_hash_packet
#print axioms Foundation.Hash.Native.typed_runtime_equivalent_queries
#print axioms Foundation.Hash.Native.typed_runtime_actual_encoded_peak
#print axioms Foundation.Hash.Native.typed_runtime_equivalent_first_joint

-- Actual native return jump and relocated runtime hash in one finite code.
#print axioms CryptoOracle.Interactive.NativeCode.running_step_of_lookup
#print axioms CryptoOracle.Interactive.NativeCode.subroutinePrefix
#print axioms CryptoOracle.Interactive.NativeCode.returnBoundary
#print axioms CryptoOracle.Interactive.NativeCode.subroutine_first_joint
#print axioms CryptoOracle.Interactive.NativeCode.subroutinePrefix_length
#print axioms CryptoOracle.Interactive.CodeRelocation.packet
#print axioms Foundation.Hash.Native.runtimeNativePrefix
#print axioms Foundation.Hash.Native.runtimeLinkedHashCode
#print axioms Foundation.Hash.Native.runtimeLinkedHashSteps
#print axioms Foundation.Hash.Native.runtimeNativePrefix_length
#print axioms Foundation.Hash.Native.runtimeLinkedHashCode_length
#print axioms Foundation.Hash.Native.runtime_linked_first_return
#print axioms Foundation.Hash.Native.runtime_linked_residual_packet
#print axioms Foundation.Hash.Native.runtime_linked_hash_packet
#print axioms Foundation.Hash.Native.runtime_linked_hash_halts
#print axioms Foundation.Hash.Native.runtime_linked_hash_queries
#print axioms Foundation.Hash.Native.runtime_linked_hash_encoded_peak

-- Raw loading, unchanged tape handoff, native copying and actual return.
#print axioms Foundation.Hash.Native.raw_linked_launch_first_joint
#print axioms Foundation.Hash.Native.raw_linked_stopped
#print axioms Foundation.Hash.Native.raw_linked_first_joint
#print axioms Foundation.Hash.Native.linked_hash_stopped_observation
#print axioms Foundation.Hash.Native.rawHashObservation
#print axioms Foundation.Hash.Native.raw_linked_hash_packet
#print axioms Foundation.Hash.Native.raw_linked_hash_continues
#print axioms Foundation.Hash.Native.raw_linked_hash_halted
#print axioms Foundation.Hash.Native.runtimeRawHashSteps_formula

-- Physical cell-aware export from the actual linked/raw hash execution.
#print axioms Machine.CellResponseExport.collect_equivalent
#print axioms Machine.CellResponseExport.run_fromHead
#print axioms CryptoOracle.Interactive.NativePacketComponent.export_cells_run
#print axioms CryptoOracle.Interactive.CellEquivalence.eval_postcondition
#print axioms CryptoOracle.Interactive.NativePacketLaunch.running_eval
#print axioms Foundation.Hash.Native.RuntimeCellExportable
#print axioms Foundation.Hash.Native.runtimeCellExportable_invariant
#print axioms Foundation.Hash.Native.typedHashFinish_cell_exportable
#print axioms Foundation.Hash.Native.typed_runtime_equivalent_cell_exportable
#print axioms Foundation.Hash.Native.runtime_cell_export_run
#print axioms Foundation.Hash.Native.runtimeCellExportable_relocation
#print axioms Foundation.Hash.Native.runtime_linked_hash_cell_exportable
#print axioms Foundation.Hash.Native.runtime_linked_first_cell_exportable
#print axioms Foundation.Hash.Native.runtimeRawExportSteps
#print axioms Foundation.Hash.Native.rawReturnedObservation
#print axioms Foundation.Hash.Native.runtime_cell_export_run_later
#print axioms Foundation.Hash.Native.raw_linked_export_frames
#print axioms Foundation.Hash.Native.raw_linked_export_packet

-- Genuine first physical return and the existing composable execution contract.
#print axioms Machine.CellResponseExport.run_fromHead_before_return
#print axioms Machine.CellResponseExport.first_return_fromHead_joint
#print axioms CryptoOracle.Interactive.NativePacketComponent.readyBoundary
#print axioms CryptoOracle.Interactive.NativePacketComponent.export_cells_before_ready
#print axioms CryptoOracle.Interactive.NativePacketComponent.export_cells_first_joint
#print axioms Foundation.Hash.Native.launchedReadyBoundary
#print axioms Foundation.Hash.Native.runtime_cell_export_first_joint
#print axioms Foundation.Hash.Native.launched_cell_export_first_joint
#print axioms Foundation.Hash.Native.raw_linked_export_first_joint
#print axioms Foundation.Hash.Native.raw_linked_export_first_packet
#print axioms Foundation.Hash.Native.raw_linked_export_continues
#print axioms Foundation.Hash.Native.launched_ready_absorbing
#print axioms Foundation.Hash.Native.raw_linked_export_ready
#print axioms Foundation.Hash.Native.runtimeRawFixedProcedure
#print axioms Foundation.Hash.Native.runtimeRawStoppedProcedure
#print axioms Foundation.Hash.Native.runtimeRawStoppedProcedure_budget
#print axioms Foundation.Hash.Native.runtimeRawStoppedProcedure_costed
#print axioms Foundation.Hash.Native.runtimeRawStoppedProcedure_operational
#print axioms Foundation.Hash.Native.runtimeRawStoppedProcedure_packet

-- Complete encoded peak storage from raw loading through physical export.
#print axioms CryptoOracle.Interactive.NativePacketComponent.Resources.fields
#print axioms CryptoOracle.Interactive.NativePacketComponent.Resources.encoding
#print axioms CryptoOracle.Interactive.NativePacketComponent.Resources.frameSize
#print axioms CryptoOracle.Interactive.NativePacketComponent.Resources.exportSize
#print axioms CryptoOracle.Interactive.NativePacketComponent.Resources.size
#print axioms CryptoOracle.Interactive.NativePacketComponent.Resources.increment
#print axioms CryptoOracle.Interactive.NativePacketComponent.Resources.frame_step
#print axioms CryptoOracle.Interactive.NativePacketComponent.Resources.step_size
#print axioms CryptoOracle.Interactive.NativePacketComponent.Resources.frame_encoding_length
#print axioms CryptoOracle.Interactive.NativePacketComponent.Resources.export_encoding_length
#print axioms CryptoOracle.Interactive.NativePacketComponent.Resources.encoding_length
#print axioms CryptoOracle.Interactive.NativePacketLaunch.Resources.fields
#print axioms CryptoOracle.Interactive.NativePacketLaunch.Resources.encoding
#print axioms CryptoOracle.Interactive.NativePacketLaunch.Resources.size
#print axioms CryptoOracle.Interactive.NativePacketLaunch.Resources.step_size
#print axioms CryptoOracle.Interactive.NativePacketLaunch.Resources.encoding_length
#print axioms CryptoOracle.Interactive.NativePacketLaunch.Resources.completeEncoding
#print axioms CryptoOracle.Interactive.NativePacketLaunch.Resources.bitBound
#print axioms CryptoOracle.Interactive.NativePacketLaunch.Resources.peak
#print axioms Foundation.Hash.Native.runtimeRaw_initial_size
#print axioms Foundation.Hash.Native.raw_linked_export_encoded_peak
#print axioms Foundation.Hash.Native.raw_linked_export_first_encoded_peak
#print axioms Foundation.Hash.Native.runtimeRawStoppedProcedure_encoded_peak

-- Raw hash packet handler and physical caller resumption.
#print axioms Foundation.Hash.Native.runtimeRawReady
#print axioms Foundation.Hash.Native.runtimeRawRead
#print axioms Foundation.Hash.Native.runtimeRawExit
#print axioms Foundation.Hash.Native.runtimeRawPacketProcedure
#print axioms Foundation.Hash.Native.runtimeRawPacketProcedure_response_length
#print axioms Foundation.Hash.Native.runtimeRawPacketProcedure_costed
#print axioms Foundation.Hash.Native.runtimeRawReady_absorbing
#print axioms Foundation.Hash.Native.runtimeRawPacketProcedure_semantics
#print axioms Foundation.Hash.Native.runtimeRawPacketHandler
#print axioms Foundation.Hash.Native.runtimeRawPacketHandler_exact
#print axioms CryptoOracle.Interactive.PacketResponseService.body_operational
#print axioms CryptoOracle.Interactive.PacketResponseService.transfer_operational
#print axioms CryptoOracle.Interactive.PacketResponseService.service_operational
#print axioms Foundation.Hash.Native.runtimeRawBegin
#print axioms Foundation.Hash.Native.runtimeRawHashService
#print axioms Foundation.Hash.Native.runtimeRawHashService_entry
#print axioms Foundation.Hash.Native.runtimeRawHashService_budget
#print axioms Foundation.Hash.Native.runtimeRawHashService_semantics
#print axioms Foundation.Hash.Native.runtimeRawHashService_costed
#print axioms Foundation.Hash.Native.runtimeRawHashService_operational
#print axioms Foundation.Hash.Native.runtimeRawHashService_packet
#print axioms Foundation.Hash.Native.runtimeRawHashService_law
#print axioms Foundation.Hash.Native.runtimeRawHashService_from_awaiting

-- Nonlinear physical storage envelopes and the complete raw hash caller.
#print axioms CryptoOracle.Interactive.PacketResponseEncoding.boundWith
#print axioms CryptoOracle.Interactive.PacketResponseEncoding.length_cap_with_bounds
#print axioms CryptoOracle.Interactive.PacketResponseEncoding.length_cap
#print axioms CryptoOracle.Interactive.PacketResponseEncoding.bitBoundWith
#print axioms CryptoOracle.Interactive.PacketResponseResources.peak_with_bounds
#print axioms CryptoOracle.Interactive.PacketResponseResources.peak
#print axioms Foundation.Hash.Native.runtimeRawSavedSize
#print axioms Foundation.Hash.Native.runtimeRawComponentBound
#print axioms Foundation.Hash.Native.runtimeRawSavedBound
#print axioms Foundation.Hash.Native.runtimeRawComponentBound_mono
#print axioms Foundation.Hash.Native.runtimeRawSavedBound_mono
#print axioms Foundation.Hash.Native.runtimeRawSaved_encoding
#print axioms Foundation.Hash.Native.runtimeRawBegin_size
#print axioms Foundation.Hash.Native.runtimeRawReady_size
#print axioms Foundation.Hash.Native.runtimeRawCallerEncoding
#print axioms Foundation.Hash.Native.runtimeRawCaller_encoded_peak

-- Physical public compression and adaptive shared-table native block semantics.
#print axioms CryptoOracle.Interactive.NativeCompressionCall.code
#print axioms CryptoOracle.Interactive.NativeCompressionCall.start
#print axioms CryptoOracle.Interactive.NativeCompressionCall.resumed
#print axioms CryptoOracle.Interactive.NativeCompressionCall.finish
#print axioms CryptoOracle.Interactive.NativeCompressionCall.call_run
#print axioms CryptoOracle.Interactive.NativeCompressionCall.finish_step
#print axioms CryptoOracle.Interactive.NativeCompressionCall.native_run
#print axioms CryptoOracle.Interactive.NativeCompressionCall.native_first_joint
#print axioms CryptoOracle.Interactive.NativeCompressionCall.component_first_joint
#print axioms CryptoOracle.Interactive.NativeCompressionCall.component_export_run
#print axioms CryptoOracle.Interactive.NativeCompressionCall.rawSteps
#print axioms CryptoOracle.Interactive.NativeCompressionCall.raw_export_run
#print axioms Foundation.Hash.Native.compressionPacket_length
#print axioms Foundation.Hash.Native.native_public_compression_run
#print axioms Foundation.Hash.Native.nativeWorldStep
#print axioms Foundation.Hash.Native.nativeWorldBegin
#print axioms Foundation.Hash.Native.nativeWorldReady
#print axioms Foundation.Hash.Native.nativeWorldPacket
#print axioms Foundation.Hash.Native.nativeWorld_ready_absorbing
#print axioms Foundation.Hash.Native.nativeWorld_hash_eval
#print axioms Foundation.Hash.Native.nativeWorld_compression_eval
#print axioms Foundation.Hash.Native.nativeWorldBegin_hash
#print axioms Foundation.Hash.Native.nativeWorldBegin_compression
#print axioms Foundation.Hash.Native.nativeWorldCallerStep
#print axioms Foundation.Hash.Native.nativeWorldCaller_dispatch
#print axioms Foundation.Hash.Native.nativeWorldBudget
#print axioms Foundation.Hash.Native.nativeWorldRead
#print axioms Foundation.Hash.Native.nativeWorldOracle
#print axioms Foundation.Hash.Native.nativeWorldOracle_step
#print axioms Foundation.Hash.Native.nativeWorld_adaptive_run

-- First physical compression return and the two-window continuing caller.
#print axioms CryptoOracle.Interactive.NativeCompressionCall.component_export_before_run
#print axioms CryptoOracle.Interactive.NativeCompressionCall.raw_export_before_run
#print axioms Foundation.Hash.Native.RuntimeCompressionInput
#print axioms Foundation.Hash.Native.native_public_compression_first_joint
#print axioms Foundation.Hash.Native.publicCompressionPacketProcedure
#print axioms Foundation.Hash.Native.publicCompressionPacketProcedure_operational
#print axioms Foundation.Hash.Native.publicCompressionPacketHandler
#print axioms Foundation.Hash.Native.publicCompressionPacketHandler_exact
#print axioms CryptoOracle.Interactive.PacketResponseService.Handler.transport
#print axioms CryptoOracle.Interactive.PacketResponseService.Handler.transport_exact
#print axioms CryptoOracle.Interactive.PacketResponseService.Handler.transport_operational
#print axioms Foundation.Hash.Native.nativeWorldPacketRead
#print axioms Foundation.Hash.Native.nativeWorldHandler
#print axioms Foundation.Hash.Native.nativeWorldHandler_exact
#print axioms Foundation.Hash.Native.nativeWorldHandler_entry
#print axioms Foundation.Hash.Native.nativeWorldHandler_budget
#print axioms Foundation.Hash.Native.nativeWorldHandler_responseCap
#print axioms Foundation.Hash.Native.nativeWorldHandler_packet
#print axioms Foundation.Hash.Native.nativeWorldService
#print axioms Foundation.Hash.Native.nativeWorldService_exit
#print axioms Foundation.Hash.Native.nativeWorldService_budget
#print axioms Foundation.Hash.Native.nativeWorldService_costed
#print axioms Foundation.Hash.Native.nativeWorldService_operational
#print axioms Foundation.Hash.Native.nativeWorldService_packet
#print axioms Foundation.Hash.Native.nativeWorldService_law
#print axioms Foundation.Hash.Native.nativeWorldService_from_awaiting
#print axioms Foundation.Hash.Native.nativeWorldService_compression_costed

-- Complete physical peak storage for both windows and the continuing caller.
#print axioms Foundation.Hash.Native.nativeWorldSize
#print axioms Foundation.Hash.Native.nativeWorldEncoding
#print axioms Foundation.Hash.Native.nativeWorldComponentBound
#print axioms Foundation.Hash.Native.nativeWorldComponentBound_mono
#print axioms Foundation.Hash.Native.nativeWorld_encoding_length
#print axioms Foundation.Hash.Native.nativeWorldIncrement
#print axioms Foundation.Hash.Native.nativeWorld_step_size
#print axioms Foundation.Hash.Native.nativeWorldBegin_size
#print axioms Foundation.Hash.Native.nativeWorldReady_size
#print axioms Foundation.Hash.Native.nativeWorldCallerEncoding
#print axioms Foundation.Hash.Native.nativeWorldCaller_encoded_peak
#print axioms Foundation.Hash.Native.nativeWorldService_encoded_peak

-- Actual source selection, certified native response, and preserved cache.
#print axioms CryptoOracle.Interactive.SourcePrefix.liftTo
#print axioms Foundation.Hash.Native.typed_runtime_input_injective
#print axioms Foundation.Hash.Native.nativeWorldPacket_injective
#print axioms Foundation.Hash.Native.nativeWorldSourceBoundary
#print axioms Foundation.Hash.Native.nativeWorldSourcePrefix
#print axioms Foundation.Hash.Native.nativeWorldAwaitTransfer
#print axioms Foundation.Hash.Native.nativeWorldWaitingService
#print axioms Foundation.Hash.Native.nativeWorldWaitingService_semantics
#print axioms Foundation.Hash.Native.NativeWorldAdmissible
#print axioms Foundation.Hash.Native.nativeWorldResponse
#print axioms Foundation.Hash.Native.nativeWorldResponse_entry
#print axioms Foundation.Hash.Native.nativeWorldResponse_exit
#print axioms Foundation.Hash.Native.nativeWorldResponse_budget
#print axioms Foundation.Hash.Native.nativeWorldSourcePrefix_operational
#print axioms Foundation.Hash.Native.nativeWorldWaitingService_operational
#print axioms Foundation.Hash.Native.nativeWorldResponse_operational
#print axioms Foundation.Hash.Native.nativeWorldResponse_awaiting_semantics
#print axioms Foundation.Hash.Native.nativeWorldService_cache_closed
#print axioms Foundation.Hash.Native.nativeWorldResponse_cache_closed
#print axioms Foundation.Hash.Native.nativeWorldCertifiedPrefix
#print axioms Foundation.Hash.Native.nativeWorldSourceCombined
#print axioms Foundation.Hash.Native.nativeWorldSourceRound
#print axioms Foundation.Hash.Native.nativeWorldSourceRound_entry
#print axioms Foundation.Hash.Native.nativeWorldSourceRound_exit
#print axioms Foundation.Hash.Native.nativeWorldSourceRound_budget
#print axioms Foundation.Hash.Native.nativeWorldCertifiedPrefix_erase
#print axioms Foundation.Hash.Native.nativeWorldSourceRound_semantics
#print axioms Foundation.Hash.Native.nativeWorldSourceRound_operational
#print axioms Foundation.Hash.Native.nativeWorldSourceRound_cache_closed
#print axioms Foundation.Hash.Native.nativeWorldSourceRound_law
#print axioms Foundation.Hash.Native.nativeWorldCaptureSelection
#print axioms Foundation.Hash.Native.nativeWorldCaptureSelection_valid
#print axioms Foundation.Hash.Native.nativeWorldCapturePrefix_costed
#print axioms Foundation.Hash.Native.nativeWorldCaptureRound
#print axioms Foundation.Hash.Native.nativeWorldCaptureRound_budget
#print axioms Foundation.Hash.Native.nativeWorldCaptureRound_operational
#print axioms Foundation.Hash.Native.nativeWorldCaptureRound_semantics
#print axioms Foundation.Hash.Native.nativeWorldCaptureRound_packet

-- Concrete adaptive native caller, genuine termination, and complete storage.
#print axioms Foundation.Hash.Native.nativeWorldSourceRound_semantics_of_pure
#print axioms CryptoOracle.Interactive.SourcePrefix.straight_run
#print axioms CryptoOracle.Interactive.PacketResponseHalt.Ready
#print axioms CryptoOracle.Interactive.PacketResponseHalt.halted
#print axioms CryptoOracle.Interactive.PacketResponseHalt.halted_terminal
#print axioms CryptoOracle.Interactive.PacketResponseHalt.halt_step
#print axioms CryptoOracle.Interactive.PacketResponseHalt.procedure
#print axioms CryptoOracle.Interactive.PacketResponseHalt.procedure_operational
#print axioms Foundation.Hash.Native.AdaptivePublicCaller.actions
#print axioms Foundation.Hash.Native.AdaptivePublicCaller.preparationCost
#print axioms Foundation.Hash.Native.AdaptivePublicCaller.code
#print axioms Foundation.Hash.Native.AdaptivePublicCaller.prefix_execute
#print axioms Foundation.Hash.Native.AdaptivePublicCaller.actions_execute
#print axioms Foundation.Hash.Native.AdaptivePublicCaller.secondMachine
#print axioms Foundation.Hash.Native.AdaptivePublicCaller.second_capture_run
#print axioms Foundation.Hash.Native.AdaptivePublicCaller.secondSelection
#print axioms Foundation.Hash.Native.AdaptivePublicCaller.secondSelection_valid
#print axioms Foundation.Hash.Native.AdaptivePublicCaller.secondRound
#print axioms Foundation.Hash.Native.AdaptivePublicCaller.secondRound_semantics
#print axioms Foundation.Hash.Native.AdaptivePublicCaller.secondRound_operational
#print axioms Foundation.Hash.Native.AdaptivePublicCaller.secondRound_packet
#print axioms Foundation.Hash.Native.AdaptivePublicCaller.table_encoding_injective
#print axioms Foundation.Hash.Native.AdaptivePublicCaller.firstMachine
#print axioms Foundation.Hash.Native.AdaptivePublicCaller.replyCaller
#print axioms Foundation.Hash.Native.AdaptivePublicCaller.replyObservation
#print axioms Foundation.Hash.Native.AdaptivePublicCaller.replyObservation_injective
#print axioms Foundation.Hash.Native.AdaptivePublicCaller.firstRound
#print axioms Foundation.Hash.Native.AdaptivePublicCaller.firstRound_packet
#print axioms Foundation.Hash.Native.AdaptivePublicCaller.FirstLayout
#print axioms Foundation.Hash.Native.AdaptivePublicCaller.firstRound_layout
#print axioms Foundation.Hash.Native.AdaptivePublicCaller.firstCertified
#print axioms Foundation.Hash.Native.AdaptivePublicCaller.selectedAnswer
#print axioms Foundation.Hash.Native.AdaptivePublicCaller.firstCertified_answers
#print axioms Foundation.Hash.Native.AdaptivePublicCaller.secondCap
#print axioms Foundation.Hash.Native.AdaptivePublicCaller.secondRound_budget
#print axioms Foundation.Hash.Native.AdaptivePublicCaller.secondFamily
#print axioms Foundation.Hash.Native.AdaptivePublicCaller.bothCalls
#print axioms Foundation.Hash.Native.AdaptivePublicCaller.bothCalls_entry
#print axioms Foundation.Hash.Native.AdaptivePublicCaller.bothCalls_exit
#print axioms Foundation.Hash.Native.AdaptivePublicCaller.bothCalls_budget
#print axioms Foundation.Hash.Native.AdaptivePublicCaller.bothCalls_operational
#print axioms Foundation.Hash.Native.AdaptivePublicCaller.afterFirst
#print axioms Foundation.Hash.Native.AdaptivePublicCaller.twoWorld
#print axioms Foundation.Hash.Native.AdaptivePublicCaller.bothCalls_packet
#print axioms Foundation.Hash.Native.AdaptivePublicCaller.final_halt_lookup
#print axioms Foundation.Hash.Native.AdaptivePublicCaller.twoWorld_ready
#print axioms Foundation.Hash.Native.AdaptivePublicCaller.bothCalls_ready
#print axioms Foundation.Hash.Native.AdaptivePublicCaller.readyCalls
#print axioms Foundation.Hash.Native.AdaptivePublicCaller.whole
#print axioms Foundation.Hash.Native.AdaptivePublicCaller.whole_semantics
#print axioms Foundation.Hash.Native.AdaptivePublicCaller.whole_budget
#print axioms Foundation.Hash.Native.AdaptivePublicCaller.whole_budget_polynomial
#print axioms Foundation.Hash.Native.AdaptivePublicCaller.whole_operational
#print axioms Foundation.Hash.Native.AdaptivePublicCaller.whole_packet
#print axioms Foundation.Hash.Native.AdaptivePublicCaller.whole_terminal
#print axioms Foundation.Hash.Native.AdaptivePublicCaller.whole_run
#print axioms Foundation.Hash.Native.AdaptivePublicCaller.firstHalt
#print axioms Foundation.Hash.Native.AdaptivePublicCaller.firstHalt_operational
#print axioms Foundation.Hash.Native.AdaptivePublicCaller.firstHalt_costed
#print axioms Foundation.Hash.Native.AdaptivePublicCaller.firstHalt_semantics
#print axioms Foundation.Hash.Native.AdaptivePublicCaller.transitionBound
#print axioms Foundation.Hash.Native.AdaptivePublicCaller.encodedBound
#print axioms Foundation.Hash.Native.AdaptivePublicCaller.whole_encoded_peak
#print axioms Foundation.Hash.Native.AdaptivePublicCaller.firstHalt_encoded_endpoint

#print axioms CryptoOracle.Interactive.NativeCode.closed_eval
#print axioms Machine.NativeBitSampler.closed
#print axioms Machine.NativeBitSampler.component
#print axioms Machine.NativeBitSampler.code
#print axioms Machine.NativeBitSampler.semantics
#print axioms Machine.NativeBitSampler.budget
#print axioms Machine.NativeBitSampler.before_halt
#print axioms CryptoOracle.Interactive.NativeUniformPacket.code
#print axioms CryptoOracle.Interactive.NativeUniformPacket.start
#print axioms CryptoOracle.Interactive.NativeUniformPacket.finish
#print axioms CryptoOracle.Interactive.NativeUniformPacket.native_run
#print axioms CryptoOracle.Interactive.NativeUniformPacket.native_before_halt
#print axioms CryptoOracle.Interactive.NativeUniformPacket.native_first_joint
#print axioms CryptoOracle.Interactive.NativeUniformPacket.component_first_joint
#print axioms CryptoOracle.Interactive.NativeUniformPacket.export_run
#print axioms CryptoOracle.Interactive.NativeUniformPacket.export_before_return
#print axioms CryptoOracle.Interactive.NativeUniformPacket.packet_run
#print axioms CryptoOracle.Interactive.NativeUniformPacket.packet_before_return
#print axioms CryptoOracle.Interactive.NativeUniformPacket.packet_first_joint
#print axioms CryptoOracle.Interactive.NativeUniformPacket.procedure
#print axioms CryptoOracle.Interactive.NativeUniformPacket.procedure_operational
#print axioms CryptoOracle.Interactive.NativeUniformPacket.handler
#print axioms CryptoOracle.Interactive.NativeUniformPacket.handler_exact
#print axioms CryptoOracle.Interactive.NativeUniformPacket.silentOracle
#print axioms CryptoOracle.Interactive.NativeUniformPacket.completeEncoding
#print axioms CryptoOracle.Interactive.NativeUniformPacket.storageBound
#print axioms CryptoOracle.Interactive.NativeUniformPacket.encoded_peak
#print axioms CryptoOracle.Interactive.NativeUniformPacket.first_return_encoded
#print axioms Foundation.Hash.Native.SimulatorRandom.decode
#print axioms Foundation.Hash.Native.SimulatorRandom.decode_bits
#print axioms Foundation.Hash.Native.SimulatorRandom.execution
#print axioms Foundation.Hash.Native.SimulatorRandom.backend_packet
#print axioms Foundation.Hash.Native.SimulatorRandom.packet_history
#print axioms Foundation.Hash.Native.SimulatorRandom.fresh_branch_observation

#print axioms CryptoOracle.Interactive.NativeUniformPacket.code_length
#print axioms CryptoOracle.Interactive.NativeUniformPacket.code_no_calls

#print axioms Machine.DelimitedTapeEquality.program

#print axioms Machine.DelimitedTapeEquality.code_length

#print axioms Machine.DelimitedTapeEquality.no_randomBit

#print axioms Machine.DelimitedTapeEquality.compare_eq

#print axioms Machine.DelimitedTapeEquality.start

#print axioms Machine.DelimitedTapeEquality.finish

#print axioms Machine.DelimitedTapeEquality.run

#print axioms Machine.DelimitedTapeEquality.before_halt

#print axioms Machine.DelimitedTapeEquality.status

#print axioms Machine.DelimitedTapeEquality.output_layout

#print axioms Machine.DelimitedTapeEquality.input_layout

#print axioms Machine.DelimitedTapeEquality.first_joint

#print axioms Machine.DelimitedTapeEquality.runs

#print axioms Machine.DelimitedTapeEquality.procedure

#print axioms Machine.DelimitedTapeEquality.component

#print axioms Machine.DelimitedTapeEquality.component_first_joint

#print axioms Machine.DelimitedTapeEquality.subroutine_first_joint

#print axioms Machine.DelimitedTapeEquality.encoded_peak

#print axioms Machine.DelimitedTapeEquality.first_encoded

#print axioms Foundation.Hash.Native.SimulatorLookup.entryBits

#print axioms Foundation.Hash.Native.SimulatorLookup.tableBits

#print axioms Foundation.Hash.Native.SimulatorLookup.tableBits_nil

#print axioms Foundation.Hash.Native.SimulatorLookup.tableBits_cons

#print axioms Foundation.Hash.Native.SimulatorLookup.entryBits_length

#print axioms Foundation.Hash.Native.SimulatorLookup.tableBits_length

#print axioms Foundation.Hash.Native.SimulatorLookup.compression_packet_eq_iff

#print axioms Foundation.Hash.Native.SimulatorLookup.comparisonInput

#print axioms Foundation.Hash.Native.SimulatorLookup.comparison_run

#print axioms Foundation.Hash.Native.SimulatorLookup.comparison_status

#print axioms Foundation.Hash.Native.SimulatorLookup.comparison_first_joint

#print axioms Machine.DelimitedTapeComparison.programWithDecision

#print axioms Machine.DelimitedTapeComparison.program_eq_decision

#print axioms Machine.DelimitedTapeComparison.decision_code_length

#print axioms Machine.DelimitedTapeComparison.decision_control_closed

#print axioms Machine.DelimitedTapeComparison.doneWithDecision

#print axioms Machine.DelimitedTapeComparison.eval_decision_stage_layout

#print axioms Machine.DelimitedTapeComparison.eval_decision_layout

#print axioms Machine.DelimitedTapeComparison.eval_equal_width_layout

#print axioms Machine.DelimitedTapeComparison.terminates_from_anyTape

#print axioms Machine.DelimitedTapeComparison.runs_lt_layout

#print axioms Machine.DelimitedTapeComparison.haltsWithin

#print axioms Machine.DelimitedTapeComparison.polynomialTime

#print axioms Machine.DelimitedTapeComparison.done_lt_status

-- Sequential lookup body and shared physical query rewind.

#print axioms CryptoOracle.Interactive.StraightLine.rewind_output
#print axioms CryptoOracle.Interactive.PacketWriter.writes_packet

#print axioms Foundation.Hash.Native.SimulatorLookup.skipActions

#print axioms Foundation.Hash.Native.SimulatorLookup.foundActions

#print axioms Foundation.Hash.Native.SimulatorLookup.missingActions

#print axioms Foundation.Hash.Native.SimulatorLookup.foundPc

#print axioms Foundation.Hash.Native.SimulatorLookup.copyPc

#print axioms Foundation.Hash.Native.SimulatorLookup.missingPc

#print axioms Foundation.Hash.Native.SimulatorLookup.headerPc

#print axioms Foundation.Hash.Native.SimulatorLookup.faultPc

#print axioms Foundation.Hash.Native.SimulatorLookup.lookupBody

#print axioms Foundation.Hash.Native.SimulatorLookup.lookupTail

#print axioms Foundation.Hash.Native.SimulatorLookup.lookupCode

#print axioms Foundation.Hash.Native.SimulatorLookup.skipActions_length

#print axioms Foundation.Hash.Native.SimulatorLookup.foundActions_length

#print axioms Foundation.Hash.Native.SimulatorLookup.missingActions_length

#print axioms Foundation.Hash.Native.SimulatorLookup.lookupCode_length

#print axioms Foundation.Hash.Native.SimulatorLookup.lookupCode_native

#print axioms Foundation.Hash.Native.SimulatorLookup.lookupBody_length

#print axioms Foundation.Hash.Native.SimulatorLookup.lookup_header_instruction

#print axioms Foundation.Hash.Native.SimulatorLookup.lookup_header_step

#print axioms Foundation.Hash.Native.SimulatorLookup.lookup_comparison_first_return

#print axioms Foundation.Hash.Native.SimulatorLookup.lookup_comparison_run

#print axioms Foundation.Hash.Native.SimulatorLookup.comparison_query_rewind

-- Full physical simulator-table lookup, actual first halt and peak encoding.

#print axioms Foundation.Hash.Native.SimulatorLookup.lookup_enter_record

#print axioms Foundation.Hash.Native.SimulatorLookup.scanStart

#print axioms Foundation.Hash.Native.SimulatorLookup.lookup_compare_record

#print axioms Foundation.Hash.Native.SimulatorLookup.missingFinish

#print axioms Foundation.Hash.Native.SimulatorLookup.lookup_missing_stage

#print axioms Foundation.Hash.Native.SimulatorLookup.lookup_missing_run

#print axioms Foundation.Hash.Native.SimulatorLookup.lookup_decision_step

#print axioms Foundation.Hash.Native.SimulatorLookup.foundFinish

#print axioms Foundation.Hash.Native.SimulatorLookup.lookup_found_value_stage

#print axioms Foundation.Hash.Native.SimulatorLookup.lookup_found_value_run

#print axioms Foundation.Hash.Native.SimulatorLookup.lookup_found_stage

#print axioms Foundation.Hash.Native.SimulatorLookup.lookup_found_run

#print axioms Foundation.Hash.Native.SimulatorLookup.lookup_skip_value_run

#print axioms Foundation.Hash.Native.SimulatorLookup.lookup_skip_run

#print axioms Foundation.Hash.Native.SimulatorLookup.lookupSteps

#print axioms Foundation.Hash.Native.SimulatorLookup.lookupFinish

#print axioms Foundation.Hash.Native.SimulatorLookup.lookup_run

#print axioms Foundation.Hash.Native.SimulatorLookup.lookupResponse

#print axioms Foundation.Hash.Native.SimulatorLookup.lookupFinish_output

#print axioms Foundation.Hash.Native.SimulatorLookup.lookupFinish_halted

#print axioms Foundation.Hash.Native.SimulatorLookup.lookupBudget

#print axioms Foundation.Hash.Native.SimulatorLookup.lookupBudget_eq

#print axioms Foundation.Hash.Native.SimulatorLookup.lookupSteps_le

#print axioms Foundation.Hash.Native.SimulatorLookup.lookupSteps_positive

#print axioms Foundation.Hash.Native.SimulatorLookup.lookup_stage_run

#print axioms Foundation.Hash.Native.SimulatorLookup.lookup_first_joint

#print axioms Foundation.Hash.Native.SimulatorLookup.lookup_output_run

#print axioms Foundation.Hash.Native.SimulatorLookup.LookupInput

#print axioms Foundation.Hash.Native.SimulatorLookup.lookupProcedure

#print axioms Foundation.Hash.Native.SimulatorLookup.lookupProcedure_operational

#print axioms Foundation.Hash.Native.SimulatorLookup.lookupProcedure_first_joint

#print axioms Foundation.Hash.Native.SimulatorLookup.lookupEncoding

#print axioms Foundation.Hash.Native.SimulatorLookup.lookupStorageBound

#print axioms Foundation.Hash.Native.SimulatorLookup.lookup_encoded_peak

#print axioms Foundation.Hash.Native.SimulatorLookup.lookup_first_encoded

#print axioms CryptoOracle.Interactive.NativeCode.nativeControl

#print axioms CryptoOracle.Interactive.NativeCode.native_only_step

#print axioms CryptoOracle.Interactive.NativeCode.native_only_eval

#print axioms CryptoOracle.Interactive.FixedWidthCopy.advance_input

#print axioms CryptoOracle.Interactive.FixedWidthCopy.advance_output

#print axioms CryptoOracle.Interactive.FixedWidthCopy.run

#print axioms CryptoOracle.Interactive.FixedWidthCopy.cellCodeWith

#print axioms CryptoOracle.Interactive.FixedWidthCopy.cellCode

#print axioms CryptoOracle.Interactive.FixedWidthCopy.codeWith

#print axioms CryptoOracle.Interactive.FixedWidthCopy.cellCodeWith_length

#print axioms CryptoOracle.Interactive.FixedWidthCopy.codeWith_length

#print axioms CryptoOracle.Interactive.FixedWidthCopy.codeWith_native

#print axioms CryptoOracle.Interactive.FixedWidthCopy.code

#print axioms CryptoOracle.Interactive.FixedWidthCopy.frontier

#print axioms CryptoOracle.Interactive.FixedWidthCopy.code_eq_with

#print axioms CryptoOracle.Interactive.FixedWidthCopy.backward_cell_run

#print axioms CryptoOracle.Interactive.FixedWidthCopy.backwardFrontier

#print axioms CryptoOracle.Interactive.FixedWidthCopy.backwardFrontier_move

#print axioms CryptoOracle.Interactive.FixedWidthCopy.backward_run

#print axioms CryptoOracle.Interactive.MarkedBackwardCopy.cellCode

#print axioms CryptoOracle.Interactive.MarkedBackwardCopy.code

#print axioms CryptoOracle.Interactive.MarkedBackwardCopy.cellCode_length

#print axioms CryptoOracle.Interactive.MarkedBackwardCopy.code_length

#print axioms CryptoOracle.Interactive.MarkedBackwardCopy.code_native

#print axioms CryptoOracle.Interactive.MarkedBackwardCopy.marked_append

#print axioms CryptoOracle.Interactive.MarkedBackwardCopy.cell_run

#print axioms CryptoOracle.Interactive.MarkedBackwardCopy.run

#print axioms CryptoOracle.Interactive.NativeCode.fullEncoding

#print axioms CryptoOracle.Interactive.NativeCode.storageBound

#print axioms CryptoOracle.Interactive.NativeCode.encoded_peak

#print axioms Foundation.Hash.Native.SimulatorRemember.keyPc

#print axioms Foundation.Hash.Native.SimulatorRemember.haltPc

#print axioms Foundation.Hash.Native.SimulatorRemember.faultPc

#print axioms Foundation.Hash.Native.SimulatorRemember.code

#print axioms Foundation.Hash.Native.SimulatorRemember.code_length

#print axioms Foundation.Hash.Native.SimulatorRemember.code_native

#print axioms Foundation.Hash.Native.SimulatorRemember.start

#print axioms Foundation.Hash.Native.SimulatorRemember.finish

#print axioms Foundation.Hash.Native.SimulatorRemember.stage_run

#print axioms Foundation.Hash.Native.SimulatorRemember.steps

#print axioms Foundation.Hash.Native.SimulatorRemember.run

#print axioms Foundation.Hash.Native.SimulatorRemember.first_joint

#print axioms Foundation.Hash.Native.SimulatorRemember.Input

#print axioms Foundation.Hash.Native.SimulatorRemember.procedure

#print axioms Foundation.Hash.Native.SimulatorRemember.procedure_operational

#print axioms Foundation.Hash.Native.SimulatorRemember.procedure_first_joint

#print axioms Foundation.Hash.Native.SimulatorRemember.encoding

#print axioms Foundation.Hash.Native.SimulatorRemember.storageBound

#print axioms Foundation.Hash.Native.SimulatorRemember.encoded_peak

#print axioms Foundation.Hash.Native.SimulatorRemember.first_encoded

#print axioms CryptoOracle.Interactive.CodeRelocation.host_native

#print axioms CryptoOracle.Interactive.NativeRandomAppend.code

#print axioms CryptoOracle.Interactive.NativeRandomAppend.code_length

#print axioms CryptoOracle.Interactive.NativeRandomAppend.code_native

#print axioms CryptoOracle.Interactive.NativeRandomAppend.run

#print axioms Foundation.Hash.Native.SimulatorRemember.startAfterRewind

#print axioms Foundation.Hash.Native.SimulatorRemember.stage_run_after_rewind

#print axioms Foundation.Hash.Native.SimulatorLookup.lookupFinish_missing

#print axioms Foundation.Hash.Native.SimulatorLookup.rewindInput

#print axioms Foundation.Hash.Native.SimulatorLookup.lookup_rewind_entry

#print axioms Foundation.Hash.Native.SimulatorLookup.rewind_table_layout

#print axioms Foundation.Hash.Native.SimulatorLookup.rewind_first_joint

#print axioms Foundation.Hash.Native.SimulatorLookup.rewind_first_return

#print axioms Foundation.Hash.Native.SimulatorFresh.code

#print axioms Foundation.Hash.Native.SimulatorFresh.code_length

#print axioms Foundation.Hash.Native.SimulatorFresh.code_native

#print axioms Foundation.Hash.Native.SimulatorFresh.start

#print axioms Foundation.Hash.Native.SimulatorFresh.finish

#print axioms Foundation.Hash.Native.SimulatorFresh.steps

#print axioms Foundation.Hash.Native.SimulatorFresh.stage_run

#print axioms Foundation.Hash.Native.SimulatorFresh.startAtFlag

#print axioms Foundation.Hash.Native.SimulatorFresh.stage_run_at_flag

#print axioms Foundation.Hash.Native.SimulatorFresh.run

#print axioms Foundation.Hash.Native.SimulatorFresh.first_joint

#print axioms Foundation.Hash.Native.SimulatorFresh.storedTable

#print axioms Foundation.Hash.Native.SimulatorFresh.fresh_branch_table

#print axioms Foundation.Hash.Native.SimulatorFresh.Input

#print axioms Foundation.Hash.Native.SimulatorFresh.procedure

#print axioms Foundation.Hash.Native.SimulatorFresh.procedure_operational

#print axioms Foundation.Hash.Native.SimulatorFresh.procedure_first_joint

#print axioms Foundation.Hash.Native.SimulatorFresh.encoded_peak

#print axioms Foundation.Hash.Native.SimulatorFreshAfterLookup.rewindPrefix

#print axioms Foundation.Hash.Native.SimulatorFreshAfterLookup.continuation

#print axioms Foundation.Hash.Native.SimulatorFreshAfterLookup.code

#print axioms Foundation.Hash.Native.SimulatorFreshAfterLookup.rewindPrefix_length

#print axioms Foundation.Hash.Native.SimulatorFreshAfterLookup.code_length

#print axioms Foundation.Hash.Native.SimulatorFreshAfterLookup.start

#print axioms Foundation.Hash.Native.SimulatorFreshAfterLookup.finish

#print axioms Foundation.Hash.Native.SimulatorFreshAfterLookup.rewindSteps

#print axioms Foundation.Hash.Native.SimulatorFreshAfterLookup.steps

#print axioms Foundation.Hash.Native.SimulatorFreshAfterLookup.rewind_first_return

#print axioms Foundation.Hash.Native.SimulatorFreshAfterLookup.stage_run

#print axioms Foundation.Hash.Native.SimulatorFreshAfterLookup.steps_eq

#print axioms Foundation.Hash.Native.SimulatorFreshAfterLookup.code_native

#print axioms Foundation.Hash.Native.SimulatorFreshAfterLookup.run

#print axioms Foundation.Hash.Native.SimulatorFreshAfterLookup.first_joint

#print axioms Foundation.Hash.Native.SimulatorFreshAfterLookup.encoded_peak

#print axioms Foundation.Hash.Native.SimulatorFreshAfterLookup.fresh_branch_table

#print axioms Foundation.Hash.Native.SimulatorFreshAfterLookup.Input

#print axioms Foundation.Hash.Native.SimulatorFreshAfterLookup.procedure

#print axioms Foundation.Hash.Native.SimulatorFreshAfterLookup.procedure_operational

#print axioms Foundation.Hash.Native.SimulatorFreshAfterLookup.procedure_first_joint

#print axioms Foundation.Hash.Native.SimulatorFreshAfterLookup.first_encoded


#print axioms Foundation.Hash.Native.SimulatorRememberResponse.haltPc

#print axioms Foundation.Hash.Native.SimulatorRememberResponse.faultPc

#print axioms Foundation.Hash.Native.SimulatorRememberResponse.tail

#print axioms Foundation.Hash.Native.SimulatorRememberResponse.code

#print axioms Foundation.Hash.Native.SimulatorRememberResponse.code_length

#print axioms Foundation.Hash.Native.SimulatorRememberResponse.code_native

#print axioms Foundation.Hash.Native.SimulatorRememberResponse.finish

#print axioms Foundation.Hash.Native.SimulatorRememberResponse.postlude_execute

#print axioms Foundation.Hash.Native.SimulatorRememberResponse.stage_run

#print axioms Foundation.Hash.Native.SimulatorRememberResponse.steps

#print axioms Foundation.Hash.Native.SimulatorRememberResponse.run

#print axioms Foundation.Hash.Native.SimulatorRememberResponse.first_joint

#print axioms Foundation.Hash.Native.SimulatorRememberResponse.export_run

#print axioms Foundation.Hash.Native.SimulatorRememberResponse.export_before_ready

#print axioms Foundation.Hash.Native.SimulatorRememberResponse.component_first_joint

#print axioms Foundation.Hash.Native.SimulatorRememberResponse.packetSteps

#print axioms Foundation.Hash.Native.SimulatorRememberResponse.packet_run

#print axioms Foundation.Hash.Native.SimulatorRememberResponse.packet_before_ready

#print axioms Foundation.Hash.Native.SimulatorRememberResponse.packet_first_joint

#print axioms Foundation.Hash.Native.SimulatorRememberResponse.procedure

#print axioms Foundation.Hash.Native.SimulatorRememberResponse.procedure_operational

#print axioms Foundation.Hash.Native.SimulatorRememberResponse.handler

#print axioms Foundation.Hash.Native.SimulatorRememberResponse.handler_exact

#print axioms Foundation.Hash.Native.SimulatorRememberResponse.encoded_peak

#print axioms CryptoOracle.Interactive.NativePacketSuffix.actions

#print axioms CryptoOracle.Interactive.NativePacketSuffix.restoredBefore

#print axioms CryptoOracle.Interactive.NativePacketSuffix.execute

#print axioms CryptoOracle.Interactive.NativePacketComponent.export_prefix_run

#print axioms CryptoOracle.Interactive.NativePacketComponent.export_prefix_before_ready

#print axioms CryptoOracle.Interactive.NativePacketComponent.export_prefix_first_joint

#print axioms Foundation.Hash.Native.SimulatorRemember.codeWithContinuation

#print axioms Foundation.Hash.Native.SimulatorRemember.codeWithContinuation_native

#print axioms Foundation.Hash.Native.SimulatorRemember.codeWithContinuation_length

#print axioms Foundation.Hash.Native.SimulatorRemember.continuation_instruction

#print axioms Foundation.Hash.Native.SimulatorRemember.continuation_run

#print axioms Foundation.Hash.Native.SimulatorRemember.continuation_run_after_rewind

#print axioms Machine.CellResponseExport.run_fromHead_withPrefix

#print axioms Machine.CellResponseExport.run_fromHead_withPrefix_before_return

#print axioms Machine.CellResponseExport.first_return_fromHead_withPrefix_joint

#print axioms Foundation.Hash.Native.SimulatorFreshResponse.code

#print axioms Foundation.Hash.Native.SimulatorFreshResponse.code_length

#print axioms Foundation.Hash.Native.SimulatorFreshResponse.code_native

#print axioms Foundation.Hash.Native.SimulatorFreshResponse.finish

#print axioms Foundation.Hash.Native.SimulatorFreshResponse.steps

#print axioms Foundation.Hash.Native.SimulatorFreshResponse.stage_run

#print axioms Foundation.Hash.Native.SimulatorFreshResponse.run

#print axioms Foundation.Hash.Native.SimulatorFreshResponse.first_joint

#print axioms Foundation.Hash.Native.SimulatorFreshResponse.component_first_joint

#print axioms Foundation.Hash.Native.SimulatorFreshResponse.export_run

#print axioms Foundation.Hash.Native.SimulatorFreshResponse.export_before_ready

#print axioms Foundation.Hash.Native.SimulatorFreshResponse.packetSteps

#print axioms Foundation.Hash.Native.SimulatorFreshResponse.packetSteps_eq

#print axioms Foundation.Hash.Native.SimulatorFreshResponse.packet_run

#print axioms Foundation.Hash.Native.SimulatorFreshResponse.packet_before_ready

#print axioms Foundation.Hash.Native.SimulatorFreshResponse.packet_first_joint

#print axioms Foundation.Hash.Native.SimulatorFreshResponse.fresh_branch_response

#print axioms Foundation.Hash.Native.SimulatorFreshResponse.procedure

#print axioms Foundation.Hash.Native.SimulatorFreshResponse.procedure_operational

#print axioms Foundation.Hash.Native.SimulatorFreshResponse.handler

#print axioms Foundation.Hash.Native.SimulatorFreshResponse.handler_exact

#print axioms Foundation.Hash.Native.SimulatorFreshResponse.encoded_peak

#print axioms Foundation.Hash.Native.SimulatorFreshResponse.first_encoded

#print axioms Foundation.Hash.Native.SimulatorRememberResponse.postlude_run

#print axioms Foundation.Hash.Native.SimulatorRememberResponse.stage_run_after_rewind

#print axioms Foundation.Hash.Native.SimulatorRememberResponse.packet_encoded_peak

#print axioms Foundation.Hash.Native.SimulatorRememberResponse.packet_first_encoded

#print axioms CryptoOracle.Interactive.NativePacketComponent.nativeControl

#print axioms CryptoOracle.Interactive.NativePacketComponent.native_only_step

#print axioms CryptoOracle.Interactive.NativePacketComponent.native_only_eval

#print axioms CryptoOracle.Interactive.NativePacketComponent.fullEncoding

#print axioms CryptoOracle.Interactive.NativePacketComponent.storageBound

#print axioms CryptoOracle.Interactive.NativePacketComponent.encoded_peak

#print axioms CryptoOracle.Interactive.NativePacketComponent.first_encoded

#print axioms Foundation.Hash.Native.SimulatorFreshAfterLookupResponse.code

#print axioms Foundation.Hash.Native.SimulatorFreshAfterLookupResponse.code_length

#print axioms Foundation.Hash.Native.SimulatorFreshAfterLookupResponse.code_native

#print axioms Foundation.Hash.Native.SimulatorFreshAfterLookupResponse.finish

#print axioms Foundation.Hash.Native.SimulatorFreshAfterLookupResponse.steps

#print axioms Foundation.Hash.Native.SimulatorFreshAfterLookupResponse.stage_run

#print axioms Foundation.Hash.Native.SimulatorFreshAfterLookupResponse.run

#print axioms Foundation.Hash.Native.SimulatorFreshAfterLookupResponse.first_joint

#print axioms Foundation.Hash.Native.SimulatorFreshAfterLookupResponse.component_first_joint

#print axioms Foundation.Hash.Native.SimulatorFreshAfterLookupResponse.export_run

#print axioms Foundation.Hash.Native.SimulatorFreshAfterLookupResponse.export_before_ready

#print axioms Foundation.Hash.Native.SimulatorFreshAfterLookupResponse.packetSteps

#print axioms Foundation.Hash.Native.SimulatorFreshAfterLookupResponse.packetSteps_eq

#print axioms Foundation.Hash.Native.SimulatorFreshAfterLookupResponse.packet_run

#print axioms Foundation.Hash.Native.SimulatorFreshAfterLookupResponse.packet_before_ready

#print axioms Foundation.Hash.Native.SimulatorFreshAfterLookupResponse.packet_first_joint

#print axioms Foundation.Hash.Native.SimulatorFreshAfterLookupResponse.fresh_branch_response

#print axioms Foundation.Hash.Native.SimulatorFreshAfterLookupResponse.procedure

#print axioms Foundation.Hash.Native.SimulatorFreshAfterLookupResponse.procedure_operational

#print axioms Foundation.Hash.Native.SimulatorFreshAfterLookupResponse.handler

#print axioms Foundation.Hash.Native.SimulatorFreshAfterLookupResponse.handler_exact

#print axioms Foundation.Hash.Native.SimulatorFreshAfterLookupResponse.encoded_peak

#print axioms Foundation.Hash.Native.SimulatorFreshAfterLookupResponse.first_encoded

#print axioms Foundation.Hash.Native.SimulatorFreshAfterLookup.afterRewind

#print axioms Foundation.Hash.Native.SimulatorFreshAfterLookup.codeWithBody

#print axioms Foundation.Hash.Native.SimulatorFreshAfterLookup.codeWithBody_length

#print axioms Foundation.Hash.Native.SimulatorFreshAfterLookup.codeWithBody_native

#print axioms Foundation.Hash.Native.SimulatorFreshAfterLookup.withBody_rewind_first_return

#print axioms Foundation.Hash.Native.SimulatorFreshAfterLookup.prepare_run

#print axioms Foundation.Hash.Native.SimulatorFreshAfterLookup.withBody_run

#print axioms Foundation.Hash.Native.SimulatorFreshResponse.stage_run_at_flag

#print axioms CryptoOracle.Interactive.NativeRandomAppend.overwrite_prefix

#print axioms Foundation.Probability.TimedExecution.eval_congr_of_active_final

#print axioms CryptoOracle.Interactive.HaltReturn.instruction

#print axioms CryptoOracle.Interactive.HaltReturn.host

#print axioms CryptoOracle.Interactive.HaltReturn.source_lookup

#print axioms CryptoOracle.Interactive.HaltReturn.host_length

#print axioms CryptoOracle.Interactive.HaltReturn.active_step

#print axioms CryptoOracle.Interactive.HaltReturn.active_eval

#print axioms CryptoOracle.Interactive.HaltReturn.return_run

#print axioms CryptoOracle.Interactive.HaltReturn.body_eval

#print axioms CryptoOracle.Interactive.HaltReturn.host_native

#print axioms Foundation.Hash.Native.SimulatorLookup.lookupFinish_halt_instruction

#print axioms Foundation.Hash.Native.SimulatorLookup.lookupHost

#print axioms Foundation.Hash.Native.SimulatorLookup.lookupHost_length

#print axioms Foundation.Hash.Native.SimulatorLookup.lookup_return_run

#print axioms Foundation.Hash.Native.SimulatorLookup.lookupSteps_missing

#print axioms Foundation.Hash.Native.SimulatorLookupFreshResponse.code

#print axioms Foundation.Hash.Native.SimulatorLookupFreshResponse.code_length

#print axioms Foundation.Hash.Native.SimulatorLookupFreshResponse.code_native

#print axioms Foundation.Hash.Native.SimulatorLookupFreshResponse.finish

#print axioms Foundation.Hash.Native.SimulatorLookupFreshResponse.continuation_run

#print axioms Foundation.Hash.Native.SimulatorLookupFreshResponse.steps

#print axioms Foundation.Hash.Native.SimulatorLookupFreshResponse.run

#print axioms Foundation.Hash.Native.SimulatorLookupFreshResponse.stage_run

#print axioms Foundation.Hash.Native.SimulatorLookupFreshResponse.first_joint

#print axioms Foundation.Hash.Native.SimulatorLookupFreshResponse.component_first_joint

#print axioms Foundation.Hash.Native.SimulatorLookupFreshResponse.export_run

#print axioms Foundation.Hash.Native.SimulatorLookupFreshResponse.export_before_ready

#print axioms Foundation.Hash.Native.SimulatorLookupFreshResponse.packetSteps

#print axioms Foundation.Hash.Native.SimulatorLookupFreshResponse.packetSteps_eq

#print axioms Foundation.Hash.Native.SimulatorLookupFreshResponse.packet_run

#print axioms Foundation.Hash.Native.SimulatorLookupFreshResponse.packet_before_ready

#print axioms Foundation.Hash.Native.SimulatorLookupFreshResponse.packet_first_joint

#print axioms Foundation.Hash.Native.SimulatorLookupFreshResponse.fresh_branch_response

#print axioms Foundation.Hash.Native.SimulatorLookupFreshResponse.procedure

#print axioms Foundation.Hash.Native.SimulatorLookupFreshResponse.procedure_operational

#print axioms Foundation.Hash.Native.SimulatorLookupFreshResponse.handler

#print axioms Foundation.Hash.Native.SimulatorLookupFreshResponse.handler_exact

#print axioms Foundation.Hash.Native.SimulatorLookupFreshResponse.encoded_peak

#print axioms Foundation.Hash.Native.SimulatorLookupFreshResponse.first_encoded

#print axioms Foundation.Hash.Native.SimulatorLookupFreshResponse.packetSteps_missing

#print axioms Foundation.Hash.Native.SimulatorLookup.missing_halt_instruction

#print axioms Foundation.Hash.Native.SimulatorLookup.found_halt_instruction

#print axioms CryptoOracle.Interactive.NativePacketFlagResponse.actions

#print axioms CryptoOracle.Interactive.NativePacketFlagResponse.execute

#print axioms Foundation.Hash.Native.SimulatorLookupHitResponse.body

#print axioms Foundation.Hash.Native.SimulatorLookupHitResponse.code

#print axioms Foundation.Hash.Native.SimulatorLookupHitResponse.body_length

#print axioms Foundation.Hash.Native.SimulatorLookupHitResponse.code_length

#print axioms Foundation.Hash.Native.SimulatorLookupHitResponse.code_native

#print axioms Foundation.Hash.Native.SimulatorLookupHitResponse.bodyFinish

#print axioms Foundation.Hash.Native.SimulatorLookupHitResponse.body_execute

#print axioms Foundation.Hash.Native.SimulatorLookupHitResponse.body_stage_run

#print axioms Foundation.Hash.Native.SimulatorLookupHitResponse.finish

#print axioms Foundation.Hash.Native.SimulatorLookupHitResponse.steps

#print axioms Foundation.Hash.Native.SimulatorLookupHitResponse.stage_run

#print axioms Foundation.Hash.Native.SimulatorLookupHitResponse.run

#print axioms Foundation.Hash.Native.SimulatorLookupHitResponse.first_joint

#print axioms Foundation.Hash.Native.SimulatorLookupHitResponse.component_first_joint

#print axioms Foundation.Hash.Native.SimulatorLookupHitResponse.export_run

#print axioms Foundation.Hash.Native.SimulatorLookupHitResponse.export_before_ready

#print axioms Foundation.Hash.Native.SimulatorLookupHitResponse.packetSteps

#print axioms Foundation.Hash.Native.SimulatorLookupHitResponse.packetSteps_eq

#print axioms Foundation.Hash.Native.SimulatorLookupHitResponse.packet_run

#print axioms Foundation.Hash.Native.SimulatorLookupHitResponse.packet_before_ready

#print axioms Foundation.Hash.Native.SimulatorLookupHitResponse.packet_first_joint

#print axioms Foundation.Hash.Native.SimulatorLookupHitResponse.finish_input

#print axioms Foundation.Hash.Native.SimulatorLookupHitResponse.cached_branch_response

#print axioms Foundation.Hash.Native.SimulatorLookupHitResponse.Input

#print axioms Foundation.Hash.Native.SimulatorLookupHitResponse.procedure

#print axioms Foundation.Hash.Native.SimulatorLookupHitResponse.procedure_operational

#print axioms Foundation.Hash.Native.SimulatorLookupHitResponse.handler

#print axioms Foundation.Hash.Native.SimulatorLookupHitResponse.handler_exact

#print axioms Foundation.Hash.Native.SimulatorLookupHitResponse.encoded_peak

#print axioms Foundation.Hash.Native.SimulatorLookupHitResponse.first_encoded

#print axioms CryptoOracle.Interactive.HaltReturn.active_step_of_fetch

#print axioms CryptoOracle.Interactive.HaltReturn.active_eval_of_fetch

#print axioms CryptoOracle.Interactive.HaltReturn.returnPrefix

#print axioms CryptoOracle.Interactive.HaltReturn.hostWithReturns

#print axioms CryptoOracle.Interactive.HaltReturn.returnPrefix_lookup

#print axioms CryptoOracle.Interactive.HaltReturn.hostWithReturns_lookup

#print axioms CryptoOracle.Interactive.HaltReturn.hostWithReturns_preserves

#print axioms CryptoOracle.Interactive.HaltReturn.return_run_with_targets

#print axioms CryptoOracle.Interactive.HaltReturn.body_eval_with_targets

#print axioms CryptoOracle.Interactive.HaltReturn.returnPrefix_native

#print axioms Foundation.Hash.Native.SimulatorLookup.lookup_return_targets

#print axioms Foundation.Hash.Native.SimulatorLookup.lookupFinish_pc

#print axioms Foundation.Hash.Native.SimulatorLookupHitResponse.body_stage_run_with_tail

#print axioms Foundation.Hash.Native.SimulatorLookupDispatch.tail

#print axioms Foundation.Hash.Native.SimulatorLookupDispatch.returnAt

#print axioms Foundation.Hash.Native.SimulatorLookupDispatch.code

#print axioms Foundation.Hash.Native.SimulatorLookupDispatch.code_length

#print axioms Foundation.Hash.Native.SimulatorLookupDispatch.code_native

#print axioms Foundation.Hash.Native.SimulatorLookupDispatch.hit_return

#print axioms Foundation.Hash.Native.SimulatorLookupDispatch.missing_return

#print axioms Foundation.Hash.Native.SimulatorLookupDispatch.hit_stage_run

#print axioms Foundation.Hash.Native.SimulatorLookupDispatch.missing_stage_run

#print axioms Foundation.Hash.Native.SimulatorLookupDispatch.steps

#print axioms Foundation.Hash.Native.SimulatorLookupDispatch.result

#print axioms Foundation.Hash.Native.SimulatorLookupDispatch.stage_run

#print axioms Foundation.Hash.Native.SimulatorLookupDispatch.result_terminal

#print axioms Foundation.Hash.Native.SimulatorLookupDispatch.steps_positive

#print axioms Foundation.Hash.Native.SimulatorLookupDispatch.run

#print axioms Foundation.Hash.Native.SimulatorLookupDispatch.first_joint

#print axioms Foundation.Hash.Native.SimulatorLookupDispatch.encoded_peak

#print axioms Foundation.Hash.Native.SimulatorLookupDispatch.returned

#print axioms Foundation.Hash.Native.SimulatorLookupDispatch.returned_fst

#print axioms Foundation.Hash.Native.SimulatorLookupDispatch.exportControl

#print axioms Foundation.Hash.Native.SimulatorLookupDispatch.export_stage

#print axioms Foundation.Hash.Native.SimulatorLookupDispatch.component_first_joint

#print axioms Foundation.Hash.Native.SimulatorLookupDispatch.packetSteps

#print axioms Foundation.Hash.Native.SimulatorLookupDispatch.packet_stage_run

#print axioms Foundation.Hash.Native.SimulatorLookupDispatch.packet_run

#print axioms Foundation.Hash.Native.SimulatorLookupDispatch.packet_before_ready

#print axioms Foundation.Hash.Native.SimulatorLookupDispatch.packet_first_joint

#print axioms Foundation.Hash.Native.SimulatorLookupDispatch.returned_length

#print axioms Foundation.Hash.Native.SimulatorLookupDispatch.response_correct

#print axioms Foundation.Hash.Native.SimulatorLookupDispatch.packetSteps_hit

#print axioms Foundation.Hash.Native.SimulatorLookupDispatch.packetSteps_missing

#print axioms Foundation.Hash.Native.SimulatorLookupDispatch.PacketInput

#print axioms Foundation.Hash.Native.SimulatorLookupDispatch.packetProcedure

#print axioms Foundation.Hash.Native.SimulatorLookupDispatch.packetProcedure_operational

#print axioms Foundation.Hash.Native.SimulatorLookupDispatch.packetHandler

#print axioms Foundation.Hash.Native.SimulatorLookupDispatch.packetHandler_exact

#print axioms Foundation.Hash.Native.SimulatorLookupDispatch.packet_encoded_peak

#print axioms Foundation.Hash.Native.SimulatorLookupDispatch.packet_first_encoded

#print axioms Foundation.Hash.Native.SimulatorLookupHitResponse.export_run_with_code

#print axioms Foundation.Hash.Native.SimulatorLookupHitResponse.export_before_ready_with_code

#print axioms Foundation.Hash.Native.SimulatorFreshAfterLookupResponse.export_run_with_code

#print axioms Foundation.Hash.Native.SimulatorFreshAfterLookupResponse.export_before_ready_with_code

#print axioms CryptoOracle.Interactive.CodeRelocation.frame_zero

#print axioms CryptoOracle.Interactive.CodeRelocation.frame_add

#print axioms Foundation.Hash.Native.SimulatorLookup.lookupSplit

#print axioms Foundation.Hash.Native.SimulatorLookup.lookupSplit_table

#print axioms Foundation.Hash.Native.SimulatorLookup.lookupSplit_unread_nonempty

#print axioms Foundation.Hash.Native.SimulatorLookup.lookupSplit_prefix_length

#print axioms Foundation.Hash.Native.SimulatorLookup.lookupFinish_input

#print axioms Foundation.Hash.Native.SimulatorLookup.rewind_suffix_layout

#print axioms Foundation.Hash.Native.SimulatorLookup.lookupRewindInput

#print axioms Foundation.Hash.Native.SimulatorLookup.lookupRewind_entry

#print axioms Foundation.Hash.Native.SimulatorLookup.lookupRewind_table

#print axioms Foundation.Hash.Native.SimulatorLookupRestore.code

#print axioms Foundation.Hash.Native.SimulatorLookupRestore.code_length

#print axioms Foundation.Hash.Native.SimulatorLookupRestore.code_native

#print axioms Foundation.Hash.Native.SimulatorLookupRestore.rewindSteps

#print axioms Foundation.Hash.Native.SimulatorLookupRestore.steps

#print axioms Foundation.Hash.Native.SimulatorLookupRestore.finish

#print axioms Foundation.Hash.Native.SimulatorLookupRestore.rewind_first_joint

#print axioms Foundation.Hash.Native.SimulatorLookupRestore.lookup_return

#print axioms Foundation.Hash.Native.SimulatorLookupRestore.first_joint

#print axioms Foundation.Hash.Native.SimulatorLookupRestore.run

#print axioms Foundation.Hash.Native.SimulatorLookupRestore.steps_le

#print axioms Foundation.Hash.Native.SimulatorLookupRestore.encoded_peak

#print axioms Foundation.Hash.Native.SimulatorLookupRestore.procedure

#print axioms Foundation.Hash.Native.SimulatorLookupRestore.procedure_operational

#print axioms Foundation.Hash.Native.SimulatorLookupRestore.procedure_first_joint

#print axioms Foundation.Hash.Native.SimulatorLookupRestore.finish_table

#print axioms Foundation.Hash.Native.SimulatorLookupRestore.finish_output

#print axioms Foundation.Probability.TimedExecution.runToBoundary_joint_of_active_final

#print axioms Foundation.Hash.Native.SimulatorLookupRestore.codeWithBody

#print axioms Foundation.Hash.Native.SimulatorLookupRestore.codeWithBody_length

#print axioms Foundation.Hash.Native.SimulatorLookupRestore.codeWithBody_native

#print axioms Foundation.Hash.Native.SimulatorLookupRestore.afterRewind

#print axioms Foundation.Hash.Native.SimulatorLookupRestore.body_rewind_run

#print axioms Foundation.Hash.Native.SimulatorLookupRestore.withBody_run

#print axioms Foundation.Hash.Native.SimulatorLookupRestoredHit.code

#print axioms Foundation.Hash.Native.SimulatorLookupRestoredHit.code_length

#print axioms Foundation.Hash.Native.SimulatorLookupRestoredHit.code_native

#print axioms Foundation.Hash.Native.SimulatorLookupRestoredHit.bodyFinish

#print axioms Foundation.Hash.Native.SimulatorLookupRestoredHit.finish

#print axioms Foundation.Hash.Native.SimulatorLookupRestoredHit.steps

#print axioms Foundation.Hash.Native.SimulatorLookupRestoredHit.body_stage_run

#print axioms Foundation.Hash.Native.SimulatorLookupRestoredHit.stage_run

#print axioms Foundation.Hash.Native.SimulatorLookupRestoredHit.run

#print axioms Foundation.Hash.Native.SimulatorLookupRestoredHit.first_joint

#print axioms Foundation.Hash.Native.SimulatorLookupRestoredHit.finish_table

#print axioms Foundation.Hash.Native.SimulatorLookupRestoredHit.component_first_joint

#print axioms Foundation.Hash.Native.SimulatorLookupRestoredHit.export_stage

#print axioms Foundation.Hash.Native.SimulatorLookupRestoredHit.packetSteps

#print axioms Foundation.Hash.Native.SimulatorLookupRestoredHit.packetSteps_eq

#print axioms Foundation.Hash.Native.SimulatorLookupRestoredHit.packet_run

#print axioms Foundation.Hash.Native.SimulatorLookupRestoredHit.packet_before_ready

#print axioms Foundation.Hash.Native.SimulatorLookupRestoredHit.packet_first_joint

#print axioms Foundation.Hash.Native.SimulatorLookupRestoredHit.cached_branch_response

#print axioms Foundation.Hash.Native.SimulatorLookupRestoredHit.Input

#print axioms Foundation.Hash.Native.SimulatorLookupRestoredHit.procedure

#print axioms Foundation.Hash.Native.SimulatorLookupRestoredHit.procedure_operational

#print axioms Foundation.Hash.Native.SimulatorLookupRestoredHit.handler

#print axioms Foundation.Hash.Native.SimulatorLookupRestoredHit.handler_exact

#print axioms Foundation.Hash.Native.SimulatorLookupRestoredHit.packetSteps_le

#print axioms Foundation.Hash.Native.SimulatorLookupRestoredHit.encoded_peak

#print axioms Foundation.Hash.Native.SimulatorLookupRestoredHit.first_encoded

#print axioms CryptoOracle.Interactive.NativePacketFlagResponse.stage_run

#print axioms CryptoOracle.Interactive.CodeRelocation.native

#print axioms CryptoOracle.Interactive.CodeRelocation.instruction

#print axioms CryptoOracle.Interactive.CodeRelocation.instruction_add

#print axioms CryptoOracle.Interactive.CodeRelocation.host_assoc

#print axioms CryptoOracle.Interactive.CodeRelocation.lookup

#print axioms CryptoOracle.Interactive.CodeRelocation.native_next

#print axioms CryptoOracle.Interactive.CodeRelocation.control

#print axioms CryptoOracle.Interactive.CodeRelocation.transitionResult

#print axioms CryptoOracle.Interactive.CodeRelocation.transition_eq

#print axioms CryptoOracle.Interactive.CodeRelocation.terminal

#print axioms CryptoOracle.Interactive.CodeRelocation.timed_step

#print axioms CryptoOracle.Interactive.CodeRelocation.eval

#print axioms CryptoOracle.Interactive.CodeRelocation.code_length

#print axioms CryptoOracle.Interactive.CodeRelocation.control_cells

#print axioms CryptoOracle.Interactive.CodeRelocation.cells

#print axioms CryptoOracle.Interactive.CodeRelocation.procedure

#print axioms CryptoOracle.Interactive.CodeRelocation.procedure_budget

#print axioms CryptoOracle.Interactive.CodeRelocation.procedure_costed

#print axioms Foundation.Hash.Native.SimulatorLookupRestoredHit.body_stage_run_with_tail

#print axioms Foundation.Hash.Native.SimulatorLookupRestoredHit.export_stage_with_code

#print axioms Foundation.Hash.Native.SimulatorLookupDispatch.hitBody

#print axioms Foundation.Hash.Native.SimulatorLookupDispatch.hitBody_length

#print axioms Foundation.Hash.Native.SimulatorLookupDispatch.hitBody_native

#print axioms Foundation.Hash.Native.SimulatorLookupDispatch.returned_table_layout

#print axioms Foundation.Hash.Native.SimulatorLookupDispatch.response_correct_with_table

#print axioms Foundation.Hash.Native.SimulatorLookupDispatch.packetSteps_le

#print axioms Machine.NativeBitstringRewind.Scratch.Input

#print axioms Machine.NativeBitstringRewind.Scratch.initial

#print axioms Machine.NativeBitstringRewind.Scratch.finish

#print axioms Machine.NativeBitstringRewind.Scratch.trace

#print axioms Machine.NativeBitstringRewind.Scratch.run

#print axioms Machine.NativeBitstringRewind.Scratch.component

#print axioms Machine.NativeBitstringRewind.Scratch.code_eq

#print axioms Machine.NativeBitstringRewind.Scratch.initial_cells

#print axioms Machine.NativeBitstringRewind.Scratch.storage_peak

#print axioms Foundation.Hash.Native.SimulatorLookupContextRestore.code

#print axioms Foundation.Hash.Native.SimulatorLookupContextRestore.rewindSteps

#print axioms Foundation.Hash.Native.SimulatorLookupContextRestore.steps

#print axioms Foundation.Hash.Native.SimulatorLookupContextRestore.rewindInput

#print axioms Foundation.Hash.Native.SimulatorLookupContextRestore.entry

#print axioms Foundation.Hash.Native.SimulatorLookupContextRestore.finish

#print axioms Foundation.Hash.Native.SimulatorLookupContextRestore.rewind_first_joint

#print axioms Foundation.Hash.Native.SimulatorLookupContextRestore.lookup_return

#print axioms Foundation.Hash.Native.SimulatorLookupContextRestore.first_joint

#print axioms Foundation.Hash.Native.SimulatorLookupContextRestore.run

#print axioms Foundation.Hash.Native.SimulatorLookupContextRestore.finish_table

#print axioms Foundation.Hash.Native.SimulatorLookupContextRestore.restored_entry

#print axioms Foundation.Hash.Native.SimulatorLookupContextRestore.steps_le

#print axioms Foundation.Hash.Native.SimulatorLookupContextRestore.encoded_peak

#print axioms Foundation.Hash.Native.SimulatorLookupContextRestore.Input

#print axioms Foundation.Hash.Native.SimulatorLookupContextRestore.input_before

#print axioms Foundation.Hash.Native.SimulatorLookupContextRestore.procedure

#print axioms Foundation.Hash.Native.SimulatorLookupContextRestore.procedure_operational

#print axioms Foundation.Hash.Native.SimulatorLookupContextRestore.procedure_first_joint

#print axioms CryptoOracle.Interactive.NativeCode.CellEquivalent

#print axioms CryptoOracle.Interactive.NativeCode.CellEquivalent.symm

#print axioms CryptoOracle.Interactive.NativeCode.CellEquivalent.trans

#print axioms CryptoOracle.Interactive.NativeCode.CellEquivalent.running_right

#print axioms CryptoOracle.Interactive.NativeCode.CellEquivalent.terminal

#print axioms CryptoOracle.Interactive.NativeCode.step_bind_eq_of_cellEquivalent

#print axioms CryptoOracle.Interactive.NativeCode.eval_bind_eq_of_cellEquivalent

#print axioms CryptoOracle.Interactive.NativeCode.eval_map_eq_of_cellEquivalent

#print axioms CryptoOracle.Interactive.NativeCode.first_bind_eq_of_cellEquivalent

#print axioms CryptoOracle.Interactive.NativeCode.encoded_peak_from

#print axioms Foundation.Hash.Native.SimulatorQueryLoading.code

#print axioms Foundation.Hash.Native.SimulatorQueryLoading.Control

#print axioms Foundation.Hash.Native.SimulatorQueryLoading.step

#print axioms Foundation.Hash.Native.SimulatorQueryLoading.boundary

#print axioms Foundation.Hash.Native.SimulatorQueryLoading.observe

#print axioms Foundation.Hash.Native.SimulatorQueryLoading.loadingFrame

#print axioms Foundation.Hash.Native.SimulatorQueryLoading.loadedFrame

#print axioms Foundation.Hash.Native.SimulatorQueryLoading.prepareSteps

#print axioms Foundation.Hash.Native.SimulatorQueryLoading.executing_run

#print axioms Foundation.Hash.Native.SimulatorQueryLoading.prepare_run

#print axioms Foundation.Hash.Native.SimulatorQueryLoading.loaded_entry

#print axioms Foundation.Hash.Native.SimulatorQueryLoading.query_run

#print axioms Foundation.Hash.Native.SimulatorQueryLoading.query_halts

#print axioms Foundation.Hash.Native.SimulatorQueryLoading.boundary_absorbing

#print axioms Foundation.Hash.Native.SimulatorQueryLoading.prepare_first_joint

#print axioms Foundation.Hash.Native.SimulatorQueryLoading.executing_first

#print axioms Foundation.Hash.Native.SimulatorQueryLoading.query_first_joint

#print axioms Foundation.Hash.Native.SimulatorQueryLoading.query_returned

#print axioms Foundation.Hash.Native.SimulatorQueryLoading.query_table_reusable

#print axioms Foundation.Hash.Native.SimulatorQueryLoading.query_steps_le

#print axioms Foundation.Hash.Native.SimulatorQueryLoading.encodingView

#print axioms Foundation.Hash.Native.SimulatorQueryLoading.controlEncoding

#print axioms Foundation.Hash.Native.SimulatorQueryLoading.fullEncoding

#print axioms Foundation.Hash.Native.SimulatorQueryLoading.executing_encoding_length

#print axioms Foundation.Hash.Native.SimulatorQueryLoading.admission_run

#print axioms Foundation.Hash.Native.SimulatorQueryLoading.after_admission_run

#print axioms Foundation.Hash.Native.SimulatorQueryLoading.storageBound

#print axioms Foundation.Hash.Native.SimulatorQueryLoading.encoded_peak

#print axioms CryptoOracle.Interactive.NativeCode.localControl

#print axioms CryptoOracle.Interactive.NativeCode.nativeControl_local

#print axioms CryptoOracle.Interactive.NativeCode.local_only_step

#print axioms CryptoOracle.Interactive.NativeCode.local_only_eval
