import tmp.sheaf.xif.paper.S2200TransferNaturalityActual

-- S2207: transfer naturality proof attempt.  The exact missing remains
-- the conjugation naturality of MonoidHom.transfer/verlagerungOpen.

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.XiFPaper.S2207TransferNaturalityProofActual

open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S2000CohomologicalPsiCnsActual
open LeanFormal.IUT.XiFPaper.S2017VerlagerungActual
open LeanFormal.IUT.XiFPaper.S2027LocalArtinActual
open LeanFormal.IUT.XiFPaper.S2169MuQZConjugationActual
open LeanFormal.IUT.XiFPaper.S2200TransferNaturalityActual

variable (p : Nat) [Fact (Nat.Prime p)]

/-- Exact first missing: transfer naturality under conjugation. -/
abbrev S2207TransferNaturalityRequired : Prop :=
  S2200TransferNaturalityRequired (p := p)

/-- The transfer-def/product-formula route would need this explicit
naturality statement for MonoidHom.transfer; it is not present in
Mathlib's transfer API. -/
def S2207TransferDefNaturalityInput : Prop :=
  ∀ (H K : Index p) (h : H ≤ K) (g : Gv p)
    (v : Abelianization ↥K),
    ∃ h' : S2169ConjIndex p g H ≤ S2169ConjIndex p g K,
      Abelianization.map (S2200ConjEquiv p g H).toMonoidHom
          (verlagerungOpen p h v) =
        verlagerungOpen p h'
          (Abelianization.map (S2200ConjEquiv p g K).toMonoidHom v)

/-- Stage and MulAut targets. -/
abbrev S2207TransferCompatRequired : Prop :=
  S2200TransferCompatRequired (p := p)
abbrev S2207MuQZMulAutRequired : Type :=
  S2200MuQZMulAutRequired p

#check S2207TransferNaturalityRequired
#check S2207TransferDefNaturalityInput
#check S2207TransferCompatRequired
#check S2207MuQZMulAutRequired

end LeanFormal.IUT.XiFPaper.S2207TransferNaturalityProofActual

end