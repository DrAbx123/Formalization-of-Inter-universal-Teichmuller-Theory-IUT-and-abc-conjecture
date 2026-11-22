import tmp.sheaf.xif.paper.S1391C3LSourcePilotActual
import tmp.sheaf.xif.paper.S1354C3LDonorRestructureActual
import tmp.sheaf.n8.closure.C3Actual

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

universe ua upi umon ui
variable {l : PrimeGeFive}
variable (I : OriginalInput.{0, 0, upi, umon, ui} l (FinitePrimePlace 2 7))
variable {p : Nat} [Fact p.Prime]
variable (place : FinitePlaceAtPrime (I.initial.arithmetic.Fmod) p)

#check C3LDonor
#check SourcePilotRegionDonors
#check sourcePilotRegionDataOfDonors
#check oldSourcePilotToCore
#check actualSourcePilotRegionDataL
#check actualC3LDonor
#check actualSourcePilotRegionLData
#check oldSourcePilotOfCoreAndBlock
#check CompletionRootBlock
#check completionFirstFieldObstruction

end
