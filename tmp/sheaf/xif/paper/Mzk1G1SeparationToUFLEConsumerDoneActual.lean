/- R5 consumer (fresh-name) -/
import tmp.sheaf.xif.paper.Mzk1G1UniversalSeparationToUFLEActual
import tmp.sheaf.xif.paper.Mzk1G1SeparationInputActual
import Mathlib.Tactic
noncomputable section
namespace LeanFormal.IUT.XiFPaper.Mzk1G1SeparationToUFLEConsumerDoneActual
open LeanFormal.IUT.XiFPaper.Mzk1G1UniversalSeparationToUFLEActual
open LeanFormal.IUT.XiFPaper.Mzk1G1SeparationInputActual
open LeanFormal.IUT.XiFPaper.Mzk1G1DifferentBoundConservativeActual
open LeanFormal.IUT.XiFPaper.Mzk1G1UniversalResidueRootGenerationActual
open LeanFormal.IUT.XiFPaper.G1DisjointFamilyActual
variable {p : Nat} [Fact p.Prime]
theorem universalLocalFieldExists_of_separationInput' (d B : Nat)
    (hsep : SeparationInput (p := p) d B) :
    UniversalLocalFieldExists (p := p) d :=
  universalLocalFieldExists_of_separationInput d B hsep
theorem universalLocalFieldExists_of_conservative (d : Nat)
    (hsep : SeparationInput (p := p) d (differentBoundConservative d)) :
    UniversalLocalFieldExists (p := p) d :=
  universalLocalFieldExists_of_separationInput' d (differentBoundConservative d) hsep
#print axioms universalLocalFieldExists_of_separationInput'
#print axioms universalLocalFieldExists_of_conservative
end LeanFormal.IUT.XiFPaper.Mzk1G1SeparationToUFLEConsumerDoneActual
