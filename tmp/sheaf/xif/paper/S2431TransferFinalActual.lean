import tmp.sheaf.xif.paper.S2430TorsionDescentSubagentActual
import tmp.sheaf.xif.paper.S2194TransferCompatProofActual
import tmp.sheaf.xif.paper.S2200TransferNaturalityActual
import tmp.sheaf.xif.paper.S2371HnatExplicitActual

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.XiFPaper.S2431TransferFinalActual

open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S2000CohomologicalPsiCnsActual
open LeanFormal.IUT.XiFPaper.S2017VerlagerungActual
open LeanFormal.IUT.XiFPaper.S2027LocalArtinActual
open LeanFormal.IUT.XiFPaper.S2169MuQZConjugationActual
open LeanFormal.IUT.XiFPaper.S2179StageConjEquivActual
open LeanFormal.IUT.XiFPaper.S2300VerlagerungNaturalActual
open LeanFormal.IUT.XiFPaper.S2371HnatExplicitActual
open LeanFormal.IUT.XiFPaper.S2430TorsionDescentSubagentActual
open LeanFormal.IUT.XiFPaper.S2194TransferCompatProofActual
open LeanFormal.IUT.XiFPaper.S2200TransferNaturalityActual

variable (p : Nat) [Fact (Nat.Prime p)]

theorem S2431S2179TransferCompatible : S2179TransferCompatible (p := p) :=
  S2430_transferCompatible p

theorem S2431S2194TransferCompatibilityRequired :
    S2194TransferCompatibilityRequired (p := p) :=
  S2431S2179TransferCompatible p

theorem S2431S2194TransferNaturalityRequired :
    S2194TransferNaturalityRequired (p := p) :=
  S2431S2179TransferCompatible p

theorem S2431S2200TransferNaturalityRequired :
    S2200TransferNaturalityRequired (p := p) := by
  intro g H K h v
  obtain ⟨h', hsq⟩ := S2371_verlagerung_natural p g H K h
  exact ⟨h', DFunLike.congr_fun hsq v⟩

theorem S2431S2200TransferCompatRequired :
    S2200TransferCompatRequired (p := p) :=
  S2431S2194TransferCompatibilityRequired p

#check S2431S2179TransferCompatible
#check S2431S2194TransferCompatibilityRequired
#check S2431S2194TransferNaturalityRequired
#check S2431S2200TransferNaturalityRequired
#check S2431S2200TransferCompatRequired

#print axioms S2431S2179TransferCompatible
#print axioms S2431S2200TransferNaturalityRequired

end LeanFormal.IUT.XiFPaper.S2431TransferFinalActual

end