/-
  Owned audit probe #5 for source_original_arithmetic_input-v1
  (run core-construction-map-20261014, agent dsh_original_input_owner).

  Types and axioms only; no bodies, no sibling source reads.
-/

import LeanFormal.IUT.IUTIII.Theorem311.SourceOriginalInput
import LeanFormal.IUT.IUTIII.Theorem311.InitialThetaInputCore
import LeanFormal.IUT.IUTIII.Theorem311.SourceHodgeTheaterBridge
import LeanFormal.IUT.IUTIII.Theorem311.SourceProcessionBoundary

set_option linter.unusedVariables false

namespace LeanFormal.IUT.AuditProbe5

open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source

/-! ## A. The derived-prerequisite input record the bridge builds -/

#check @DerivedPrerequisiteInput
#check @DerivedPrerequisiteInput.labelPrime
#check @DerivedPrerequisiteInput.prime
#check @DerivedPrerequisiteInput.packet
#check @DerivedPrerequisiteInput.localPacket
#check @DerivedPrerequisiteInput.initial
#check @DerivedPrerequisiteInput.vertical
#check @DerivedPrerequisiteInput.vertical_monotone
#check @DerivedPrerequisiteInput.verticalSite
#check @DerivedPrerequisiteInput.labelledCount
#check @DerivedPrerequisiteInput.labelledCount_pos
#check @DerivedPrerequisiteInput.evaluation
#check @DerivedPrerequisiteInput.labelledKummer
#check @DerivedPrerequisiteInput.family
#check @DerivedPrerequisiteInput.horizontal
#check @DerivedPrerequisiteInput.kummer_horizontal_compat
#check @DerivedPrerequisiteInput.labelled_horizontal_compat
#check @DerivedPrerequisiteInput.evaluation_horizontal_compat

/-! ## B. Definition 3.1 clause records -/

#check @SourceReductionClause
#check @SourceReductionClause.stableReduction
#check @SourceReductionClause.multiplicativeReduction
#check @SourceReductionClause.qParameter
#check @SourceTorsionClause
#check @SourceTorsionClause.torsionCarrier
#check @SourceTorsionClause.representation
#check @SourceTorsionClause.imageContainsSL2
#check @SourceOrbicurveClause
#check @SourceOrbicurveClause.coverToPunctured
#check @SourceOrbicurveClause.cuspCount
#check @SourceOrbicurveClause.exactSequence
#check @SourceSectionClause
#check @SourceSectionClause.sectionMap
#check @SourceCuspClause
#check @SourceCuspClause.epsilon

/-! ## C. Concrete arithmetic instances present in the cached environment -/

#check @concreteGaussianInitialThetaArithmeticData
#check @gaussianInitialThetaArithmeticData
#check @gaussianInitialThetaArithmeticData_sqrtNegOne
#check @concreteGaussianInitialThetaArithmeticData_curve

/-! ## D. Axiom audit of the arithmetic carriers and concrete instances -/

#print axioms InitialThetaArithmeticData
#print axioms SourceDefinition31Data
#print axioms concreteGaussianInitialThetaArithmeticData
#print axioms gaussianInitialThetaArithmeticData
#print axioms SourceProcessionBoundary.Input.indeterminacyEvidence

end LeanFormal.IUT.AuditProbe5
