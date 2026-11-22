import tmp.sheaf.xif.paper.S1895OIdentificationsActual
import tmp.sheaf.xif.paper.S1487OQPilotScalarEqualityActual

noncomputable section
open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.XiFPaper.S1895OIdentificationsActual
open LeanFormal.IUT.XiFPaper.S1280SourceDefinition31Actual
open LeanFormal.IUT.XiFPaper.S1487OQPilotScalarEqualityActual

namespace ProbeQ

abbrev fmod (D : S1895PaperInput) : Type := (S1895PaperInput.I D).initial.arithmetic.Fmod

example (D : S1895PaperInput) (b : (S1895PaperInput.I D).initial.badPlaces) :
    b.1 = S1280Place D.l := by
  have hb : b.1 ∈ ({S1280Place D.l} :
      Set (NumberField.FinitePlace (S1280Arithmetic D.l).Fmod)) := by
    simpa [S1280Selection_V_mod_bad] using b.2
  exact Set.mem_singleton_iff.mp hb

example (D : S1895PaperInput) (b : (S1895PaperInput.I D).initial.badPlaces) :
    (S1487Cand.order : NNReal) = (S1487Cand.order : NNReal) := rfl

end ProbeQ
