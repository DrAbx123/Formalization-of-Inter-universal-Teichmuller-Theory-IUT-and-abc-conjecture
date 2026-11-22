import tmp.sheaf.xif.paper.S3136SourceDefinition31DataAssemblyAdapterActual
import tmp.sheaf.xif.paper.S3136ModelReductionClauseProviderActual

/-! # Stage-4 host: conditional SourceDefinition31Data from native data + slots

Source anchors: IUT I, Definition 3.1 (complete source contract); IUT I, Example
3.2, (iv) (concrete Gaussian arithmetic); IUT III, Definition 3.1 (bad places).

CONSUMER: qpilot's modelSourceDefinition31Data assembly. Given a native initial
Theta datum T, the actual split-input family at its bad lifts, the four remaining
clause data (torsion/orbicurve/sections/cusp) and the five compatibility pairs,
this file assembles the complete Definition 3.1 source contract. The reduction
slot is the proved native reduction clause provider; every other slot is passed
explicitly (no placeholder, no opaque Prop as a slot).

LABEL: conditional assembly component. Registry frozen; new file only. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 1000000

namespace LeanFormal.IUT.XiFPaper.S3136Source31AssemblyConditionalActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.XiFPaper.NativeSplitSufficientConditionActual
open LeanFormal.IUT.XiFPaper.S3136ModelReductionClauseProviderActual
open LeanFormal.IUT.XiFPaper.S3136SourceDefinition31DataAssemblyAdapterActual

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]

/-- Conditional assembly of the complete Definition 3.1 source contract from the
native datum, the split-input family (reduction slot) and the remaining slots. -/
def lgpSource31Data_native
    (F : NativeSplitInputFamily (l := l) T)
    (torsion : SourceTorsionClause l)
    (orbicurve : SourceOrbicurveClause)
    (sections : SourceSectionClause)
    (cusp : SourceCuspClause)
    (c_red : Prop) (h_red : c_red)
    (c_tor : Prop) (h_tor : c_tor)
    (c_orb : Prop) (h_orb : c_orb)
    (c_sec : Prop) (h_sec : c_sec)
    (c_cusp : Prop) (h_cusp : c_cusp) :
    SourceDefinition31Data l where
  arithmetic := T.arithmetic
  selectedPlaces := Selected (nativePlaceSelection T)
  badPlaces := Bad (nativePlaceSelection T)
  reduction := lgpModelReductionClauseProvider (l := l) T F
  torsion := torsion
  orbicurve := orbicurve
  sections := sections
  cusp := cusp
  arithmetic_reduction_compatibility := c_red
  arithmetic_reduction_compatibility_proved := h_red
  arithmetic_torsion_compatibility := c_tor
  arithmetic_torsion_compatibility_proved := h_tor
  arithmetic_orbicurve_compatibility := c_orb
  arithmetic_orbicurve_compatibility_proved := h_orb
  arithmetic_section_compatibility := c_sec
  arithmetic_section_compatibility_proved := h_sec
  arithmetic_cusp_compatibility := c_cusp
  arithmetic_cusp_compatibility_proved := h_cusp

/-- The assembled contract has the native datum arithmetic. -/
theorem lgpSource31Data_native_arithmetic
    (F : NativeSplitInputFamily (l := l) T)
    (torsion : SourceTorsionClause l)
    (orbicurve : SourceOrbicurveClause)
    (sections : SourceSectionClause)
    (cusp : SourceCuspClause)
    (c_red : Prop) (h_red : c_red)
    (c_tor : Prop) (h_tor : c_tor)
    (c_orb : Prop) (h_orb : c_orb)
    (c_sec : Prop) (h_sec : c_sec)
    (c_cusp : Prop) (h_cusp : c_cusp) :
    (lgpSource31Data_native (l := l) T F torsion orbicurve sections cusp
      c_red h_red c_tor h_tor c_orb h_orb c_sec h_sec c_cusp h_cusp).arithmetic
      = T.arithmetic := rfl

#check lgpSource31Data_native
#check lgpSource31Data_native_arithmetic

end LeanFormal.IUT.XiFPaper.S3136Source31AssemblyConditionalActual
end