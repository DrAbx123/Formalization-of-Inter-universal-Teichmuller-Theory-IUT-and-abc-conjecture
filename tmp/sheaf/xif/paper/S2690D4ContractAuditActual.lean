import LeanFormal.IUT.IUTI.InitialTheta.SourcePlaceTateComparisonSynthesis
import tmp.sheaf.xif.paper.S1280SourceDefinition31Actual
import LeanFormal.IUT.IUTII.Frobenioid.Example36TateUniformization

noncomputable section
open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlaceTateComparisonConstruction
open LeanFormal.IUT.InitialThetaSource.PlaceQParameterUniformization
open LeanFormal.IUT.XiFPaper.S1280SourceDefinition31Actual
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT.XiFPaper.S2690D4ContractAuditActual

universe u
variable {l : PrimeGeFive}

/-- The S1280 D4 contract target: the one-way uniformization-contract family
over the S1280 bad moduli set.  This is the minimal missing input isolated by
`SourcePlaceTateComparisonSynthesis`. -/
abbrev S2690ContractTarget : Type :=
  BadPlaceUniformizationContract.{0} (S1280Selection l)

/-- From a D4 card, recover the one-way contract family by applying
`TateCurveComparison.toUniformization` to the comparison field. -/
noncomputable def S2690ContractOfCards
    (C : BadPlaceTateUniformizationCards (S1280Selection l)) :
    S2690ContractTarget (l := l) where
  parameter := C.parameter
  realization := fun w hw => (C.comparison w hw).toUniformization
  order_coprime := C.order_coprime

/-- The D4 card and the one-way contract family are equivalent. -/
theorem S2690Cards_nonempty_iff_contract_nonempty :
    Nonempty (BadPlaceTateUniformizationCards (S1280Selection l)) ↔
      Nonempty (S2690ContractTarget (l := l)) :=
  ⟨fun h => ⟨S2690ContractOfCards h.some⟩,
   fun h => ⟨h.some.toTateUniformizationCards⟩⟩

/-- The Example36 missing contract at the concrete five place: the exact
`CurveIndexedTateUniformization` with no constructor. -/
def S2690MissingConcreteFiveUniformization : Prop :=
  LeanFormal.IUT.IUTII.Frobenioid.Example36.TateInverseJ.MissingCurveIndexedTateUniformizationAtFive

#check S2690ContractTarget
#check S2690Cards_nonempty_iff_contract_nonempty
#check S2690MissingConcreteFiveUniformization

end LeanFormal.IUT.XiFPaper.S2690D4ContractAuditActual
end