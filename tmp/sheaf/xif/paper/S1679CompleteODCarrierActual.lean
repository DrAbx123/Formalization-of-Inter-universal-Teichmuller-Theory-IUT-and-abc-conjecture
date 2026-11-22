import tmp.sheaf.xif.paper.S1673ODSubmoduleConstructActual
import tmp.sheaf.xif.paper.PaperLineBundleCarrierBase

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000
namespace LeanFormal.IUT.XiFPaper.S1679CompleteODCarrierActual
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.PaperLineBundleCarrierActual
open LeanFormal.IUT.XiFPaper.S1673ODSubmoduleConstructActual

/-- Actual PaperLineBundleCarrier from the complete S1673 O(-D) total and
localization. -/
noncomputable def s1679Carrier (l : PrimeGeFive) :
    PaperLineBundleCarrier (k := s1673K l) where
  total := ↥(s1673Total l)
  localization := s1673Localization l

@[simp] theorem s1679Carrier_total (l : PrimeGeFive) :
    (s1679Carrier l).total = ↥(s1673Total l) := rfl

@[simp] theorem s1679Carrier_localization (l : PrimeGeFive)
    (v : NumberField.FinitePlace (s1673K l)) (x : ↥(s1673Total l)) :
    (s1679Carrier l).localization v x = s1673Localization l v x := rfl

/-- Actual identification: the carrier's total is the complete O(-D)
submodule type, not S1423Module, a free lattice or a completion carrier. -/
def S1679PaperLineBundleIdentified (l : PrimeGeFive) : Prop :=
  (s1679Carrier l).total = ↥(s1673Total l)

theorem s1679_identified (l : PrimeGeFive) :
    S1679PaperLineBundleIdentified l := rfl

end LeanFormal.IUT.XiFPaper.S1679CompleteODCarrierActual
end