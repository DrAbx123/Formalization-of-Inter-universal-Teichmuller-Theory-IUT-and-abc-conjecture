import tmp.sheaf.xif.paper.S2159MuQZActionActual

-- S2169: attempted Gv conjugation action on muQZ.  The conjugation
-- permutation of open subgroups is actual; the stage equivalences and
-- transfer compatibility remain exact missing.

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.XiFPaper.S2169MuQZConjugationActual

open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S2000CohomologicalPsiCnsActual
open LeanFormal.IUT.XiFPaper.S2017VerlagerungActual
open LeanFormal.IUT.XiFPaper.S2027LocalArtinActual
open LeanFormal.IUT.XiFPaper.S2159MuQZActionActual

variable (p : Nat) [Fact (Nat.Prime p)]

/-- Conjugation of an open subgroup by an element of Gv. -/
noncomputable def S2169ConjIndex (g : Gv p) (H : Index p) : Index p :=
  H.comap (MulAut.conj g).toMonoidHom (IsTopologicalGroup.continuous_conj g)

/-- Exact first missing: stage conjugation equivalences over the
conjugation permutation of open subgroups. -/
abbrev S2169StageConjugationRequired (g : Gv p) : Type :=
  ∀ H : Index p, Stage p H ≃+ Stage p (S2169ConjIndex p g H)

/-- Exact transfer-compatibility condition for a stage conjugation family. -/
def S2169TransferCompatible
    (c : ∀ g : Gv p, S2169StageConjugationRequired p g) : Prop :=
  ∀ (g : Gv p) (H K : Index p) (h : H ≤ K) (v : Stage p K),
    ∃ h' : S2169ConjIndex p g H ≤ S2169ConjIndex p g K,
      c g H (toStage p h v) = toStage p h' (c g K v)

/-- Exact muQZ action first missing, with the stage/transfer data explicit. -/
structure S2169MuQZActionData where
  stageConj : ∀ g : Gv p, S2169StageConjugationRequired p g
  transfer_compat : S2169TransferCompatible p stageConj
  muQZAction : Gv p →* MulAut (Multiplicative (muQZ p))
  action_compat :
    ∀ (g : Gv p) (H : Index p) (v : Stage p H),
      Multiplicative.toAdd (muQZAction g (Multiplicative.ofAdd (muQZof p H v))) =
        muQZof p (S2169ConjIndex p g H) (stageConj g H v)

abbrev S2169MuQZActionRequired : Type :=
  S2169MuQZActionData p

#check S2169ConjIndex
#check S2169StageConjugationRequired
#check S2169TransferCompatible
#check S2169MuQZActionData
#check S2169MuQZActionRequired

#print axioms S2169ConjIndex

end LeanFormal.IUT.XiFPaper.S2169MuQZConjugationActual

end