import tmp.sheaf.xif.paper.S1391C3LSourcePilotActual
import tmp.sheaf.xif.paper.S1354C3LDonorRestructureActual
import tmp.sheaf.n8.closure.C3Actual
import tmp.sheaf.n8.closure.T11Native
import tmp.sheaf.n8.closure.C3T11NamedClosure
import tmp.sheaf.xif.PaperXiFInclusion

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.N8Closure.SourcePilotRegion
open LeanFormal.IUT.N8Closure.C3Actual
open LeanFormal.IUT.XiFPaper.S1391C3LSourcePilotActual
open LeanFormal.IUT.Theorem311Source.S1354C3LDonorRestructureActual
open LeanFormal.IUT.XiFPaper

universe ua upi umon ui
variable {l : PrimeGeFive}
variable (I : OriginalInput.{0, 0, upi, umon, ui} l (FinitePrimePlace 2 7))
variable {p : Nat} [Fact p.Prime]
variable (place : FinitePlaceAtPrime (I.initial.arithmetic.Fmod) p)

#check C3LDonor
#check SourcePilotRegionDonors
#check sourcePilotRegionDataOfDonors
#check oldSourcePilotToCore
#check paperQParameter
#check ABCBridge.N8.T11Reductions.ThetaPacketWitness
#check ABCBridge.N8.T11Native.ThetaPacketIdentification
#check ABCBridge.N8.C3T11NamedClosure.c3T11_thetaPacketIdentification
#check LeanFormal.IUT.XiFPaper.actualSourcePilotRegionDataL
#check LeanFormal.IUT.XiFPaper.S1391C3LSourcePilotActual.actualSourcePilotRegionDataL

end
