import tmp.sheaf.xif.paper.S2179StageConjEquivActual

-- S2189: transfer compatibility as exact missing; conditional additive
-- action on muQZ from it.

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.XiFPaper.S2189TransferCompatActual

open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S2000CohomologicalPsiCnsActual
open LeanFormal.IUT.XiFPaper.S2017VerlagerungActual
open LeanFormal.IUT.XiFPaper.S2027LocalArtinActual
open LeanFormal.IUT.XiFPaper.S2169MuQZConjugationActual
open LeanFormal.IUT.XiFPaper.S2179StageConjEquivActual

variable (p : Nat) [Fact (Nat.Prime p)]

/-- Exact transfer compatibility missing. -/
abbrev S2189TransferCompatibilityRequired : Prop :=
  S2179TransferCompatible (p := p)

/-- Conditional additive endomorphism of muQZ from transfer compatibility. -/
noncomputable def S2189MuQZEndOfTransfer
    (h : S2189TransferCompatibilityRequired p) (g : Gv p) :
    muQZ p →+ muQZ p :=
  muQZ_lift p (muQZ p)
    (fun H : Index p =>
      (muQZof p (S2169ConjIndex p g H)).comp
        (S2179StageConj p g H).toAddMonoidHom)
    (by
      intro H K hHK v
      obtain ⟨h', hEq⟩ := h g H K hHK v
      change muQZof p (S2169ConjIndex p g H)
          (S2179StageConj p g H (toStage p hHK v)) =
        muQZof p (S2169ConjIndex p g K) (S2179StageConj p g K v)
      rw [hEq, muQZof_transfer (p := p) (H := S2169ConjIndex p g H)
        (K := S2169ConjIndex p g K) h'])

/-- Exact missing inverse/group-law/continuity data for a full MulAut action. -/
structure S2189MuQZMulAutData where
  transfer_compat : S2189TransferCompatibilityRequired p
  action : Gv p →* MulAut (Multiplicative (muQZ p))
  action_compat :
    ∀ (g : Gv p) (H : Index p) (v : Stage p H),
      Multiplicative.toAdd (action g (Multiplicative.ofAdd (muQZof p H v))) =
        muQZof p (S2169ConjIndex p g H) (S2179StageConj p g H v)

abbrev S2189MuQZMulAutRequired : Type :=
  S2189MuQZMulAutData p

#check S2189TransferCompatibilityRequired
#check S2189MuQZEndOfTransfer
#check S2189MuQZMulAutData
#check S2189MuQZMulAutRequired

#print axioms S2189MuQZEndOfTransfer

end LeanFormal.IUT.XiFPaper.S2189TransferCompatActual

end