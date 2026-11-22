import tmp.sheaf.xif.paper.S2207TransferNaturalityProofActual

-- S2211: explicit-transversal attempt for transfer naturality.
-- Mathlib's Transfer API provides diff/transfer_def/product formula but no
-- transport of LeftTransversal along a group isomorphism; that transport
-- is the exact first missing.

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.XiFPaper.S2211TransferConjProofActual

open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S2000CohomologicalPsiCnsActual
open LeanFormal.IUT.XiFPaper.S2017VerlagerungActual
open LeanFormal.IUT.XiFPaper.S2169MuQZConjugationActual
open LeanFormal.IUT.XiFPaper.S2027LocalArtinActual
open LeanFormal.IUT.XiFPaper.S2207TransferNaturalityProofActual

variable (p : Nat) [Fact (Nat.Prime p)]

/-- Exact transfer naturality target, unchanged. -/
abbrev S2211TransferNaturalityRequired : Prop :=
  S2207TransferNaturalityRequired (p := p)

/-- Exact first missing API: conjugated LeftTransversal transport.  The
type records the property that would be needed from the transversal
API; no inhabitant is asserted. -/
def S2211ConjugatedTransversalTransportRequired : Prop :=
  ∀ (H : Subgroup (Gv p)) (T : H.LeftTransversal)
    (e : Gv p ≃* Gv p),
    Nonempty (H.map e.toMonoidHom).LeftTransversal

/-- Same for the concrete open subgroups of S2017. -/
def S2211OpenSubgroupTransversalTransportRequired : Prop :=
  ∀ (H K : Index p) (h : H ≤ K) (g : Gv p),
    Nonempty (S2169ConjIndex p g K).toSubgroup.LeftTransversal

#check S2211TransferNaturalityRequired
#check S2211ConjugatedTransversalTransportRequired
#check S2211OpenSubgroupTransversalTransportRequired

end LeanFormal.IUT.XiFPaper.S2211TransferConjProofActual

end