import tmp.sheaf.xif.paper.S2928CorrectedTConstructionActual
import tmp.sheaf.xif.paper.ClauseEToD7Actual
import tmp.sheaf.xif.paper.S2847A6ArithmeticActual

noncomputable section
open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.XiFPaper.S2928CorrectedTConstructionActual
open LeanFormal.IUT.XiFPaper.ClauseEToD7Actual
open LeanFormal.IUT.XiFPaper.S2847A6ArithmeticActual
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 0

namespace LeanFormal.IUT.XiFPaper.S2931CorrectedD7IntakeActual

local instance : Fact (Irreducible (Polynomial.X ^ 2 - Polynomial.C (-1) : Polynomial ℚ)) :=
  ⟨gaussianPolynomial_irreducible⟩
local instance : Field S2847A6.F := S2847A6.fieldF
local instance : NumberField S2847A6.F := S2847A6.numberFieldF

noncomputable abbrev correctedLayer
    (_T : SourceNativeInitialThetaDataCorrected) :
    SourceValuationSectionLayer S2847A6 :=
  SourceValuationSectionLayer.canonical S2847A6

structure ClauseEToD7PlaceDataCorrected
    (T : SourceNativeInitialThetaDataCorrected) where
  placeEquiv :
    (correctedLayer T).valuationCarrier ≃
      {v : NumberFieldPlace S2847A6.K // v ∈ T.source.V}
  placeEquiv_comap :
    ∀ x : (correctedLayer T).valuationCarrier,
      NumberFieldPlace.comap (k := S2847A6.Fmod)
          (placeEquiv x).1 =
        (correctedLayer T).sectionMap x

structure ClauseEToD7LocalGroupDataCorrected
    (T : SourceNativeInitialThetaDataCorrected) where
  localGroupCarrier : (correctedLayer T).valuationCarrier → Type
  modifiedLocalGroupCarrier :
    (correctedLayer T).modifiedValuationCarrier → Type
  localGroupEquiv :
    ∀ x : (correctedLayer T).valuationCarrier,
      localGroupCarrier x ≃
        modifiedLocalGroupCarrier ((correctedLayer T).sectionMap x)
  finitePlaceData : Prop
  finitePlaceData_proved : finitePlaceData
  infinitePlaceData : Prop
  infinitePlaceData_proved : infinitePlaceData

structure ClauseEToD7CompatibilityCorrected
    (T : SourceNativeInitialThetaDataCorrected) where
  placeEquiv :
    (correctedLayer T).valuationCarrier ≃
      {v : NumberFieldPlace S2847A6.K // v ∈ T.source.V}
  localGroupCarrier : (correctedLayer T).valuationCarrier → Type
  modifiedLocalGroupCarrier :
    (correctedLayer T).modifiedValuationCarrier → Type
  localGroupEquiv :
    ∀ x : (correctedLayer T).valuationCarrier,
      localGroupCarrier x ≃
        modifiedLocalGroupCarrier ((correctedLayer T).sectionMap x)
  finitePlaceData : Prop
  finitePlaceData_proved : finitePlaceData
  infinitePlaceData : Prop
  infinitePlaceData_proved : infinitePlaceData

noncomputable def ClauseEToD7CompatibilityCorrected_of_data
    (T : SourceNativeInitialThetaDataCorrected)
    (P : ClauseEToD7PlaceDataCorrected T)
    (H : ClauseEToD7LocalGroupDataCorrected T) :
    ClauseEToD7CompatibilityCorrected T where
  placeEquiv := P.placeEquiv
  localGroupCarrier := H.localGroupCarrier
  modifiedLocalGroupCarrier := H.modifiedLocalGroupCarrier
  localGroupEquiv := H.localGroupEquiv
  finitePlaceData := H.finitePlaceData
  finitePlaceData_proved := H.finitePlaceData_proved
  infinitePlaceData := H.infinitePlaceData
  infinitePlaceData_proved := H.infinitePlaceData_proved

structure NativeD7IntakeCorrected where
  T : SourceNativeInitialThetaDataCorrected
  compatibility : ClauseEToD7CompatibilityCorrected T

noncomputable def S2931CorrectedD7Intake
    (T : SourceNativeInitialThetaDataCorrected)
    (P : ClauseEToD7PlaceDataCorrected T)
    (H : ClauseEToD7LocalGroupDataCorrected T) :
    NativeD7IntakeCorrected where
  T := T
  compatibility := ClauseEToD7CompatibilityCorrected_of_data T P H

#check correctedLayer
#check ClauseEToD7PlaceDataCorrected
#check ClauseEToD7LocalGroupDataCorrected
#check ClauseEToD7CompatibilityCorrected
#check NativeD7IntakeCorrected
#check S2931CorrectedD7Intake

end LeanFormal.IUT.XiFPaper.S2931CorrectedD7IntakeActual
end
