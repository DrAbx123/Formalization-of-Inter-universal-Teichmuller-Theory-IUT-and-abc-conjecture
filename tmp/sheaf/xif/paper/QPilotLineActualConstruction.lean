import tmp.sheaf.xif.paper.QPilotObjectActual
import tmp.sheaf.n8.closure.NativeC1PaperSource
import tmp.sheaf.n8.closure.C2Actual
import tmp.sheaf.xif.paper.C3ActualThetaPacketWitnessConstruction
noncomputable section
namespace LeanFormal.IUT.XiFPaper.QPilotLineActualConstruction
open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.N8Closure.PaperQPilotObjectActual
open LeanFormal.IUT.N8Closure.SourceInputBinding
open LeanFormal.IUT.N8Closure.SourceLogKummerRealization
open LeanFormal.IUT.N8Closure.NativeC1PaperSource
open LeanFormal.IUT.N8Closure.C2Actual
open LeanFormal.IUT.N8Closure.NativeInput
open LeanFormal.IUT.N8Closure.C3Actual
open LeanFormal.IUT.N8Closure.SourcePilotRegion
open LeanFormal.IUT.N8Closure.C3ActualThetaPacketWitnessConstruction
variable {l : PrimeGeFive} (P : NativeC1PaperSource l)
variable (D : SourcePilotRegionDonors (l:=l) (V:=NativePlaces P.X.S) (I:=P.input))
noncomputable def qPilotLineActual : QPilotLineActual (I:=P.input) where
  C1 := P.sourceInputBinding
  C2 := sourceLogKummerDataActual P.input P.sourceInputBinding
  C3 := actualC3OfDonors (l:=l) (V:=NativePlaces P.X.S) (I:=P.input) D

open LeanFormal.IUT.IUTII.Frobenioid.Example36.SourceTheaterCarrier
open LeanFormal.IUT.N8Closure.PaperQPilotObjectActual

noncomputable def paperQPilotObjectActual
    (P : NativeC1PaperSource l)
    (D : SourcePilotRegionDonors (I:=P.input))
    (strip : SourceFTimesMuPrimeStrip (NativePlaces P.X.S))
    (oneColumn : SourceOneColumnArithmeticHolomorphicStructure (NativePlaces P.X.S)) :
    PaperQPilotObjectActual (I:=P.input) where
  line := qPilotLineActual (l:=l) P D
  strip := strip
  oneColumn := oneColumn
  logKummer := (qPilotLineActual (l:=l) P D).C2
  logKummer_eq := rfl
  oneZero := oneZeroPoint
  oneZero_eq := rfl
end LeanFormal.IUT.XiFPaper.QPilotLineActualConstruction
end