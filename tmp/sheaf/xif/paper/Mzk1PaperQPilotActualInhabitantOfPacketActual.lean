/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.QPilotLineActualConstruction
import tmp.sheaf.xif.paper.S1266SourceInd3Actual
import LeanFormal.IUT.IUTIII.Theorem311.SourceArithmeticHolomorphicLanding
import LeanFormal.IUT.Foundations.LocalFields.IntegralUnits
import Mathlib.Tactic
/-! # PaperQPilotObjectActual inhabitant from NativeC1PaperSource + donor -/
noncomputable section
namespace LeanFormal.IUT.XiFPaper.Mzk1PaperQPilotActualInhabitantOfPacketActual
open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.N8Closure.NativeC1PaperSource
open LeanFormal.IUT.N8Closure.C3Actual
open LeanFormal.IUT.N8Closure.PaperQPilotObjectActual
open LeanFormal.IUT.XiFPaper.QPilotLineActualConstruction
open LeanFormal.IUT.XiFPaper.S1266SourceInd3Actual
open LeanFormal.IUT.N8Closure.NativeInput
open LeanFormal.IUT.LocalFieldIntegralUnits
universe u
variable {l : PrimeGeFive}
variable (P : NativeC1PaperSource l)
variable (D : SourcePilotRegionDonors (I := P.input))
variable (oneColumn : SourceOneColumnArithmeticHolomorphicStructure (NativePlaces P.X.S))
noncomputable def paperQPilotObjectActualOfPacket :
    PaperQPilotObjectActual (I := P.input) :=
  paperQPilotObjectActual P D
    (ind3TimesMuStrip (l := l) (V := NativePlaces P.X.S) (I := P.input) 1 0)
    oneColumn
theorem paperQPilotObjectActualOfPacket_nonempty
    (D : SourcePilotRegionDonors (I := P.input))
    (oneColumn : SourceOneColumnArithmeticHolomorphicStructure (NativePlaces P.X.S)) :
    Nonempty (PaperQPilotObjectActual.{0, 0, 0, 0, 0, 0, 0, 0, 0} (I := P.input)) :=
  ⟨paperQPilotObjectActualOfPacket (P := P) (D := D) (oneColumn := oneColumn)⟩
def residualInputs : List String := ["NativeC1PaperSource P", "SourcePilotRegionDonors D", "strip via ind3TimesMuStrip", "oneColumn parameter"]
theorem residualInputs_length : residualInputs.length = 4 := rfl
end LeanFormal.IUT.XiFPaper.Mzk1PaperQPilotActualInhabitantOfPacketActual
end