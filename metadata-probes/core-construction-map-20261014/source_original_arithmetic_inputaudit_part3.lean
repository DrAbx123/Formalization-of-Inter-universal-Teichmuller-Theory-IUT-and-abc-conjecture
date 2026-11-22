/-
  Owned audit probe #3 for source_original_arithmetic_input-v1
  (run core-construction-map-20261014, agent dsh_original_input_owner).

  Resolve the external public types that the owned modules consume.  Types and
  axioms only; no bodies, no source reads.
-/

import LeanFormal.IUT.IUTIII.Theorem311.SourceOriginalInput
import LeanFormal.IUT.IUTIII.Theorem311.InitialThetaInputCore
import LeanFormal.IUT.IUTIII.Theorem311.SourceHodgeTheaterBridge
import LeanFormal.IUT.IUTIII.Theorem311.SourceProcessionBoundary

set_option linter.unusedVariables false

namespace LeanFormal.IUT.AuditProbe3

open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source

/-! ## A. The derived-prerequisite Input record consumed by the bridge -/

#check @Input
#check @Input.prime
#check @Input.packet
#check @Input.localPacket
#check @Input.initial
#check @Input.vertical
#check @Input.vertical_monotone
#check @Input.verticalSite
#check @Input.labelledCount
#check @Input.evaluation
#check @Input.labelledKummer
#check @Input.family
#check @Input.horizontal
#check @Input.kummer_horizontal_compat
#check @Input.labelled_horizontal_compat
#check @Input.evaluation_horizontal_compat
#check @Theorem311Output

/-! ## B. Arithmetic/field-tower structure behind the initial Theta data -/

#check @ThetaFieldTower
#check @ThetaFieldTower.sqrtNegOne
#check @ThetaFieldTower.degreePrimeToL
#check @InitialThetaArithmeticData.tower
#check @SourceReductionClause
#check @SourceTorsionClause
#check @SourceOrbicurveClause
#check @SourceSectionClause
#check @SourceCuspClause

/-! ## C. Axiom audit of the conditional assembly and the owning-module carriers -/

#print axioms Input
#print axioms Theorem311Output
#print axioms SourceHodgeTheaterBridge.SourceTheorem311Realization.input
#print axioms SourceHodgeTheaterBridge.source_realization_theorem311
#print axioms SourceProcessionBoundary.Input.routeOutput
#print axioms SourceProcessionBoundary.Input.sourceTheorem311Certificate

end LeanFormal.IUT.AuditProbe3
