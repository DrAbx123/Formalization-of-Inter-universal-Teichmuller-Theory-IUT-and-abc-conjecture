import tmp.sheaf.xif.paper.S1895OIdentificationsActual
import tmp.sheaf.xif.paper.S1487OQPilotScalarEqualityActual

noncomputable section
open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.XiFPaper.S1895OIdentificationsActual
open LeanFormal.IUT.XiFPaper.S1280SourceDefinition31Actual
open LeanFormal.IUT.XiFPaper.S1487OQPilotScalarEqualityActual

namespace ProbeS1927B

abbrev fmod (D : S1895PaperInput) : Type := (S1895PaperInput.I D).initial.arithmetic.Fmod

example (D : S1895PaperInput) : (S1280Place D.l) = S1487FivePlace.val := rfl

example (D : S1895PaperInput) (b : (S1895PaperInput.I D).initial.badPlaces) :
    b.1 = S1280Place D.l := by
  have hb : b.1 ∈ (S1280Selection D.l).V_mod_bad := b.2
  rw [S1280Selection_V_mod_bad] at hb
  exact Set.mem_singleton_iff.mp hb

example (D : S1895PaperInput) (b : (S1895PaperInput.I D).initial.badPlaces) :
    NumberField.InfinitePlace (fmod D) → NNReal := fun _ => 0

end ProbeS1927B
