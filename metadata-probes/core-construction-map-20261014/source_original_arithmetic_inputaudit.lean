/-
  Owned audit probe for source_original_arithmetic_input-v1
  (run core-construction-map-20261014, agent dsh_original_input_owner).

  Purpose: query PUBLIC types/axioms of the four owned source modules against the
  existing cached environment.  No source edits, no builds, no implementation
  printing.  All `#check` lines print types only; all `#print axioms` lines print
  axiom dependencies of the named declaration.
-/

import LeanFormal.IUT.IUTIII.Theorem311.SourceOriginalInput
import LeanFormal.IUT.IUTIII.Theorem311.InitialThetaInputCore
import LeanFormal.IUT.IUTIII.Theorem311.SourceHodgeTheaterBridge
import LeanFormal.IUT.IUTIII.Theorem311.SourceProcessionBoundary

set_option linter.unusedVariables false

namespace LeanFormal.IUT.AuditProbe

open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source

/-! ## A. Root input contract of the original Theta input -/

#check @Theorem311Source.OriginalInput
#check @Theorem311Source.OriginalInput.initial
#check @Theorem311Source.OriginalInput.family
#check @Theorem311Source.OriginalInput.index_equiv
#check @Theorem311Source.OriginalInput.arithmetic_alignment
#check @Theorem311Source.SourceTheorem311Index
#check @Theorem311Source.OriginalInput.theaterAt
#check @Theorem311Source.OriginalInput.initialThetaInput
#check @Theorem311Source.InitialThetaInput
#check @Theorem311Source.InitialThetaInput.arithmetic
#check @Theorem311Source.InitialThetaInput.selectedPlaces
#check @Theorem311Source.InitialThetaInput.badPlaces
#check @Theorem311Source.InitialThetaInput.badIncluded
#check @Theorem311Source.InitialThetaInput.stableReduction_proved
#check @Theorem311Source.InitialThetaInput.torsionImage_proved
#check @Theorem311Source.InitialThetaInput.cusp_positive

/-! ## B. External declarations the root contract consumes (type query only) -/

#check @InitialThetaArithmeticData
#check @InitialThetaArithmeticData.l
#check @InitialThetaArithmeticData.F
#check @InitialThetaArithmeticData.Fmod
#check @InitialThetaArithmeticData.K
#check @InitialThetaArithmeticData.curve
#check @SourceDefinition31Data
#check @SourceDefinition31Data.arithmetic
#check @SourceDefinition31Data.toInitialThetaInput
#check @SourceHodgeTheaterFamily
#check @SourceHodgeTheaterFamily.index
#check @SourceHodgeTheaterFamily.theater
#check @SourceHodgeTheaterFamily.link
#check @SourceHodgeTheaterFamily.distinct
#check @SourceHodgeTheaterFamily.link_refl
#check @SourceHodgeTheaterFamily.link_symm
#check @SourceHodgeTheaterFamily.link_trans
#check @SourceHodgeTheaterFamily.permutation
#check @HodgeTheater
#check @HodgeTheater.thetaPacket
#check @HodgeTheater.arithmetic
#check @HodgeTheater.primeStrip
#check @HodgeTheaterLink
#check @PrimeGeFive

/-! ## C. Bridge realization records -/

#check @SourceHodgeTheaterBridge.SourceHodgeTheaterSystem
#check @SourceHodgeTheaterBridge.SourceLGPProcession
#check @SourceHodgeTheaterBridge.SourcePacketRealization
#check @SourceHodgeTheaterBridge.SourceVerticalRealization
#check @SourceHodgeTheaterBridge.SourceEvaluationBridge
#check @SourceHodgeTheaterBridge.SourceTheorem311Realization
#check @SourceHodgeTheaterBridge.SourceTheorem311Realization.input
#check @SourceHodgeTheaterBridge.source_realization_theorem311
#check @SourceHodgeTheaterBridge.source_bridge_conditional_output
#check @SourceHodgeTheaterBridge.source_hodge_groupoid_closed
#check @SourceHodgeTheaterBridge.source_procession_closed
#check @SourceHodgeTheaterBridge.source_packet_closed
#check @SourceHodgeTheaterBridge.source_vertical_closed
#check @SourceHodgeTheaterBridge.source_evaluation_closed

/-! ## D. Procession boundary record and its concrete finite instance -/

#check @SourceProcessionBoundary.Input
#check @SourceProcessionBoundary.Input.theater
#check @SourceProcessionBoundary.Input.history
#check @SourceProcessionBoundary.Input.carrier
#check @SourceProcessionBoundary.Input.route_normal_form
#check @SourceProcessionBoundary.Input.SourceTheorem311Certificate
#check @SourceProcessionBoundary.Input.sourceTheorem311Certificate
#check @SourceProcessionBoundary.Input.concreteInput
#check @SourceProcessionBoundary.Input.concreteInput_profile_base

/-! ## E. Axiom audit of named declarations (no bodies printed) -/

#print axioms Theorem311Source.OriginalInput.indexOf_apply
#print axioms Theorem311Source.OriginalInput.theaterAt_arithmetic
#print axioms Theorem311Source.OriginalInput.initial_selected_nonempty
#print axioms Theorem311Source.OriginalInput.initial_arithmetic_sqrt_neg_one
#print axioms Theorem311Source.OriginalInput.initialThetaInput_eq_projection
#print axioms SourceHodgeTheaterBridge.source_hodge_groupoid_closed
#print axioms SourceHodgeTheaterBridge.source_realization_theorem311
#print axioms SourceHodgeTheaterBridge.source_bridge_conditional_output
#print axioms SourceProcessionBoundary.Input.sourceTheorem311Certificate_theta
#print axioms SourceProcessionBoundary.Input.concreteInput_profile_base

end LeanFormal.IUT.AuditProbe
