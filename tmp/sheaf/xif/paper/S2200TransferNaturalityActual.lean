import tmp.sheaf.xif.paper.S2194TransferCompatProofActual

-- S2200: conjugation naturality of transfer, exact surface.

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.XiFPaper.S2200TransferNaturalityActual

open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S2000CohomologicalPsiCnsActual
open LeanFormal.IUT.XiFPaper.S2017VerlagerungActual
open LeanFormal.IUT.XiFPaper.S2027LocalArtinActual
open LeanFormal.IUT.XiFPaper.S2169MuQZConjugationActual
open LeanFormal.IUT.XiFPaper.S2173StageConjugationActual
open LeanFormal.IUT.XiFPaper.S2179StageConjEquivActual
open LeanFormal.IUT.XiFPaper.S2194TransferCompatProofActual

variable (p : Nat) [Fact (Nat.Prime p)]

/-- Canonical conjugation equivalence for open subgroups. -/
noncomputable def S2200ConjEquiv (g : Gv p) (H : Index p) :
    ↥H ≃* ↥(S2169ConjIndex p g H) := by
  let e := S2173ConjSubgroupEquiv (p := p) g.symm H
  have h := S2179MapConjEqComap (p := p) g H
  exact e.trans (MulEquiv.subgroupCongr h)

/-- Exact transfer naturality under conjugation. -/
def S2200TransferNaturalityRequired : Prop :=
  ∀ (g : Gv p) (H K : Index p) (h : H ≤ K) (v : Abelianization ↥K),
    ∃ h' : S2169ConjIndex p g H ≤ S2169ConjIndex p g K,
      Abelianization.map (S2200ConjEquiv p g H).toMonoidHom
          (verlagerungOpen p h v) =
        verlagerungOpen p h'
          (Abelianization.map (S2200ConjEquiv p g K).toMonoidHom v)

/-- Exact stage-level compatibility target. -/
abbrev S2200TransferCompatRequired : Prop :=
  S2194TransferCompatibilityRequired (p := p)

/-- Exact MulAut action target. -/
abbrev S2200MuQZMulAutRequired : Type :=
  S2194MuQZMulAutRequired p

#check S2200ConjEquiv
#check S2200TransferNaturalityRequired
#check S2200TransferCompatRequired
#check S2200MuQZMulAutRequired

#print axioms S2200ConjEquiv

end LeanFormal.IUT.XiFPaper.S2200TransferNaturalityActual

end