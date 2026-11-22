import tmp.sheaf.xif.paper.S2690D4ContractAuditActual
import tmp.sheaf.xif.paper.SourceQvCandidateActual
import tmp.sheaf.xif.paper.S2682CurveIndexedTateSplitActual

noncomputable section
open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlaceTateComparisonConstruction
open LeanFormal.IUT.InitialThetaSource.PlaceQParameterUniformization
open LeanFormal.IUT.XiFPaper.S1280SourceDefinition31Actual
open LeanFormal.IUT.XiFPaper.SourceQvCandidateActual
open LeanFormal.IUT.XiFPaper.S2682CurveIndexedTateSplitActual
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT.XiFPaper.S2692D4ConditionalContractActual

universe u
variable {l : PrimeGeFive}

/-- Actual q parameter at each bad place, from `sourceQvCandidate` and the
actual S1280 split-multiplicative reduction. -/
noncomputable def S2692Parameter
    (w : NumberField.FinitePlace (S1280Arithmetic l).F)
    (hw : NumberFieldFinitePlace.comap (k := (S1280Arithmetic l).Fmod) w ∈
      (S1280Selection l).V_mod_bad) :
    NumberFieldFinitePlace.FinitePlaceQCandidate w :=
  sourceQvCandidate w (S1280Arithmetic l).curve (S1280ReductionCards_split l w hw)

/-- Conditional D4 contract: actual parameter, actual coordinate half as an
explicit input, and the analytic half as an explicit gap field.  No analytic
data is manufactured. -/
structure S2692ConditionalContract where
  coordinate : ∀ (w : NumberField.FinitePlace (S1280Arithmetic l).F)
    (hw : NumberFieldFinitePlace.comap (k := (S1280Arithmetic l).Fmod) w ∈
      (S1280Selection l).V_mod_bad),
    CurveIndexedTateUniformizationCoordinate (S1280Arithmetic l).curve w
      (S2692Parameter w hw)
  analyticGap : ∀ (w : NumberField.FinitePlace (S1280Arithmetic l).F)
    (hw : NumberFieldFinitePlace.comap (k := (S1280Arithmetic l).Fmod) w ∈
      (S1280Selection l).V_mod_bad),
    CurveIndexedTateUniformizationAnalyticGap (S1280Arithmetic l).curve w
      (S2692Parameter w hw)
  order_coprime : ∀ (w : NumberField.FinitePlace (S1280Arithmetic l).F)
    (hw : NumberFieldFinitePlace.comap (k := (S1280Arithmetic l).Fmod) w ∈
      (S1280Selection l).V_mod_bad),
    Nat.Coprime (S2692Parameter w hw).order l.value

/-- Assemble the conditional contract into the actual `BadPlaceUniformizationContract`. -/
noncomputable def S2692ConditionalContract.toContract
    (K : S2692ConditionalContract (l := l)) :
    BadPlaceUniformizationContract (S1280Selection l) where
  parameter := S2692Parameter
  realization := fun w hw => assemble (K.coordinate w hw) (K.analyticGap w hw).some
  order_coprime := K.order_coprime

#check S2692Parameter
#check S2692ConditionalContract.toContract

end LeanFormal.IUT.XiFPaper.S2692D4ConditionalContractActual
end