import tmp.sheaf.xif.paper.S2189TransferCompatActual

-- S2194: transfer compatibility proof attempt.  The exact missing is the
-- naturality of transfer under conjugation; no fake proof.

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.XiFPaper.S2194TransferCompatProofActual

open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S2000CohomologicalPsiCnsActual
open LeanFormal.IUT.XiFPaper.S2017VerlagerungActual
open LeanFormal.IUT.XiFPaper.S2027LocalArtinActual
open LeanFormal.IUT.XiFPaper.S2169MuQZConjugationActual
open LeanFormal.IUT.XiFPaper.S2179StageConjEquivActual
open LeanFormal.IUT.XiFPaper.S2189TransferCompatActual

variable (p : Nat) [Fact (Nat.Prime p)]

/-- Exact missing transfer compatibility. -/
abbrev S2194TransferCompatibilityRequired : Prop :=
  S2179TransferCompatible (p := p)

/-- Exact missing naturality statement, exposed with the actual stage
conjugation map. -/
def S2194TransferNaturalityRequired : Prop :=
  ∀ (g : Gv p) (H K : Index p) (h : H ≤ K) (v : Stage p K),
    ∃ h' : S2169ConjIndex p g H ≤ S2169ConjIndex p g K,
      S2179StageConj p g H (toStage p h v) =
        toStage p h' (S2179StageConj p g K v)

/-- Exact full MulAut action surface from S2189. -/
abbrev S2194MuQZMulAutRequired : Type :=
  S2189MuQZMulAutRequired p

/-- Conditional reduction target: transfer compatibility plus the full
MulAut action data. -/
abbrev S2194TransferToMulAutRequired : Type :=
  S2194TransferCompatibilityRequired p →
    S2194MuQZMulAutRequired p

#check S2194TransferCompatibilityRequired
#check S2194TransferNaturalityRequired
#check S2194MuQZMulAutRequired
#check S2194TransferToMulAutRequired

end LeanFormal.IUT.XiFPaper.S2194TransferCompatProofActual

end