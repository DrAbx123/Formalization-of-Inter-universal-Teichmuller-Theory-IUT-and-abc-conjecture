import LeanFormal.IUT.IUTI.InitialTheta.SourceDefinition31Boundary

/-! # Stage-4 host: SourceDefinition31Data assembly adapter from slot providers

Source anchor: IUT I, Definition 3.1 (complete source contract: arithmetic, selected/bad
places, reduction, torsion, orbicurve, sections, cusp, and the five arithmetic-compatibility
pairs).

CONSUMER: qpilot's modelSourceDefinition31Data assembly. This file gives the structure of
the eight data slots plus five compatibility pairs as an explicit provider record, and the
deterministic assembly function into SourceDefinition31Data l. The record makes the exact
providers checkable field by field (see S3136ModelSourceClauseInventoryActual for the
current inhabitant status of each slot).

LABEL: prerequisite component (assembly adapter). Registry frozen; new file only. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 1000000

namespace LeanFormal.IUT.XiFPaper.S3136SourceDefinition31DataAssemblyAdapterActual

open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source

variable {l : PrimeGeFive}

/-- The eight SourceDefinition31Data slots plus the five compatibility pairs, as explicit
providers. -/
structure LGPSource31SlotProviders (l : PrimeGeFive) where
  arithmetic : InitialThetaArithmeticData l
  selectedPlaces : Type
  badPlaces : Type
  reduction : SourceReductionClause selectedPlaces badPlaces
  torsion : SourceTorsionClause l
  orbicurve : SourceOrbicurveClause
  sections : SourceSectionClause
  cusp : SourceCuspClause
  arithmetic_reduction_compatibility : Prop
  arithmetic_reduction_compatibility_proved : arithmetic_reduction_compatibility
  arithmetic_torsion_compatibility : Prop
  arithmetic_torsion_compatibility_proved : arithmetic_torsion_compatibility
  arithmetic_orbicurve_compatibility : Prop
  arithmetic_orbicurve_compatibility_proved : arithmetic_orbicurve_compatibility
  arithmetic_section_compatibility : Prop
  arithmetic_section_compatibility_proved : arithmetic_section_compatibility
  arithmetic_cusp_compatibility : Prop
  arithmetic_cusp_compatibility_proved : arithmetic_cusp_compatibility

/-- Deterministic assembly of the complete Definition 3.1 source contract from the slot
providers. -/
def lgpSourceDefinition31Data_of_slots (P : LGPSource31SlotProviders l) :
    SourceDefinition31Data l where
  arithmetic := P.arithmetic
  selectedPlaces := P.selectedPlaces
  badPlaces := P.badPlaces
  reduction := P.reduction
  torsion := P.torsion
  orbicurve := P.orbicurve
  sections := P.sections
  cusp := P.cusp
  arithmetic_reduction_compatibility := P.arithmetic_reduction_compatibility
  arithmetic_reduction_compatibility_proved := P.arithmetic_reduction_compatibility_proved
  arithmetic_torsion_compatibility := P.arithmetic_torsion_compatibility
  arithmetic_torsion_compatibility_proved := P.arithmetic_torsion_compatibility_proved
  arithmetic_orbicurve_compatibility := P.arithmetic_orbicurve_compatibility
  arithmetic_orbicurve_compatibility_proved := P.arithmetic_orbicurve_compatibility_proved
  arithmetic_section_compatibility := P.arithmetic_section_compatibility
  arithmetic_section_compatibility_proved := P.arithmetic_section_compatibility_proved
  arithmetic_cusp_compatibility := P.arithmetic_cusp_compatibility
  arithmetic_cusp_compatibility_proved := P.arithmetic_cusp_compatibility_proved

/-- The assembled structure has the provider arithmetic. -/
theorem lgpSourceDefinition31Data_of_slots_arithmetic (P : LGPSource31SlotProviders l) :
    (lgpSourceDefinition31Data_of_slots P).arithmetic = P.arithmetic := rfl

#check LGPSource31SlotProviders
#check lgpSourceDefinition31Data_of_slots
#check lgpSourceDefinition31Data_of_slots_arithmetic

end LeanFormal.IUT.XiFPaper.S3136SourceDefinition31DataAssemblyAdapterActual
end