/-
  Owned audit probe #2 for source_original_arithmetic_input-v1
  (run core-construction-map-20261014, agent dsh_original_input_owner).

  Queries only public types/axioms.  No source edits, no builds, no bodies.
-/

import LeanFormal.IUT.IUTIII.Theorem311.SourceOriginalInput
import LeanFormal.IUT.IUTIII.Theorem311.InitialThetaInputCore
import LeanFormal.IUT.IUTIII.Theorem311.SourceHodgeTheaterBridge
import LeanFormal.IUT.IUTIII.Theorem311.SourceProcessionBoundary

set_option linter.unusedVariables false

namespace LeanFormal.IUT.AuditProbe2

open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source

/-! ## Arithmetic input structure and its carrier -/

#check @InitialThetaArithmeticData
#check @InitialThetaArithmeticData.F
#check @InitialThetaArithmeticData.Fmod
#check @InitialThetaArithmeticData.K
#check @InitialThetaArithmeticData.curve
#check @InitialThetaArithmeticData.tower
#check @PuncturedEllipticCurve
#check @InitialThetaTower
#check @InitialThetaTower.sqrtNegOne
#check @InitialThetaTower.degreePrimeToL
#check @InitialThetaTower.Fmod
#check @InitialThetaTower.F
#check @InitialThetaTower.K

/-! ## Definition 3.1 data consumed by the root contract -/

#check @SourceDefinition31Data
#check @SourceDefinition31Data.arithmetic
#check @SourceDefinition31Data.selectedPlaces
#check @SourceDefinition31Data.badPlaces
#check @SourceDefinition31Data.reduction
#check @SourceDefinition31Data.torsion
#check @SourceDefinition31Data.orbicurve
#check @SourceDefinition31Data.sections
#check @SourceDefinition31Data.cusp
#check @SourceDefinition31Data.toInitialThetaInput
#check @SourceDefinition31Data.source_condition_bundle

/-! ## Theorem 3.11 output record (consumer of the conditional bridge) -/

#check @Input
#check @Input.labelPrime
#check @Input.prime
#check @Input.packet
#check @Input.initial
#check @Input.labelledKummer
#check @Input.horizontal
#check @Theorem311Output
#check @Theorem311Output.input

/-! ## Probe-side axiom check of the two conditional top-level exports -/

#print axioms SourceHodgeTheaterBridge.source_realization_theorem311
#print axioms SourceHodgeTheaterBridge.source_bridge_conditional_output
#print axioms SourceHodgeTheaterBridge.SourceTheorem311Realization.input
#print axioms SourceTheorem311Realization.input
#print axioms SourceProcessionBoundary.Input.concreteInput
#print axioms SourceProcessionBoundary.Input.sourceTheorem311Certificate
#print axioms Theorem311Source.OriginalInput.arithmetic_alignment_trans

end LeanFormal.IUT.AuditProbe2
