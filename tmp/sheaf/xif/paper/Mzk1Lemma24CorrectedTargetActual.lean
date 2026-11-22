import LeanFormal.IUT.Audit.Status

noncomputable section

namespace LeanFormal.IUT.XiFPaper.Mzk1Lemma24CorrectedTargetActual

/-- SUPERSEDED: this file's earlier corrected-target draft (with criticalValues imported
from the ported TauCeti library and an arbitrary rational S_phi) was replaced by
RestatedLemma24InterfaceActual (Lead A280): fixed specialSet {0,1,infinity} and C-point
critical values.  Kept only as a pointer; do not cite. -/
def SupersededPointer : Audit.Obligation :=
  { id := "MZK1.lemma24.corrected-target.superseded"
    source := "Lead A277-A281 restatement"
    status := Audit.VerificationStatus.interface
    note := "SUPERSEDED by tmp/sheaf/xif/paper/RestatedLemma24InterfaceActual.lean (fixed specialSet {0,1,infinity}, CV over C, composition law statements). The earlier draft in this file was not citable (missing Polynomial.criticalValues import / arbitrary rational target). No closure claim."
    dependsOn := [ "MZK1.lemma24.restated-target" ]
    sorryItems := [] }

end LeanFormal.IUT.XiFPaper.Mzk1Lemma24CorrectedTargetActual
end
