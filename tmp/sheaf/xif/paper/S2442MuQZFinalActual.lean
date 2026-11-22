import tmp.sheaf.xif.paper.S2432MuQZMulAutDoneActual
import tmp.sheaf.xif.paper.S2431TransferFinalActual

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.XiFPaper.S2442MuQZFinalActual

open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S2000CohomologicalPsiCnsActual
open LeanFormal.IUT.XiFPaper.S2017VerlagerungActual
open LeanFormal.IUT.XiFPaper.S2027LocalArtinActual
open LeanFormal.IUT.XiFPaper.S2169MuQZConjugationActual
open LeanFormal.IUT.XiFPaper.S2179StageConjEquivActual
open LeanFormal.IUT.XiFPaper.S2189TransferCompatActual
open LeanFormal.IUT.XiFPaper.S2432MuQZMulAutDoneActual

variable (p : Nat) [Fact (Nat.Prime p)]

/-- Corrected honest data: g^-1-indexed action. -/
abbrev S2442MuQZMulAutData : Type :=
  S2432MuQZMulAutData p

noncomputable def S2442MuQZMulAutData_actual : S2442MuQZMulAutData p :=
  S2432MuQZMulAutData_actual p

/-- Actual action: Gv p ->* MulAut (Multiplicative (muQZ p)). -/
noncomputable def S2442MuQZAction :
    Gv p →* MulAut (Multiplicative (muQZ p)) :=
  S2432MuQZAction p

theorem S2442MuQZAction_compat (g : Gv p) (H : Index p) (v : Stage p H) :
    Multiplicative.toAdd (S2442MuQZAction p g
      (Multiplicative.ofAdd (muQZof p H v))) =
      muQZof p (S2169ConjIndex p g⁻¹ H) (S2179StageConj p g⁻¹ H v) :=
  S2432MuQZAction_compat p g H v

/-- Actual anti-composition law for the underlying additive action. -/
theorem S2442MuQZEnd_comp (g h : Gv p) :
    (S2432MuQZEnd p g).comp (S2432MuQZEnd p h) =
      S2432MuQZEnd p (h * g) :=
  S2432MuQZEnd_comp p g h

/-- Actual inverse laws. -/
theorem S2442MuQZEnd_comp_inv (g : Gv p) :
    (S2432MuQZEnd p g).comp (S2432MuQZEnd p g⁻¹) =
      AddMonoidHom.id (muQZ p) :=
  S2432MuQZEnd_comp_inv p g

theorem S2442MuQZEnd_inv_comp (g : Gv p) :
    (S2432MuQZEnd p g⁻¹).comp (S2432MuQZEnd p g) =
      AddMonoidHom.id (muQZ p) :=
  S2432MuQZEnd_inv_comp p g

/-- Per-automorphism continuity for the declared discrete topology on muQZ. -/
theorem S2442MuQZAction_continuous (g : Gv p) :
    letI : TopologicalSpace (muQZ p) := ⊥
    Continuous (fun x : muQZ p =>
      Multiplicative.toAdd (S2442MuQZAction p g (Multiplicative.ofAdd x))) :=
  S2432MuQZAction_continuous p g

/-- Exact first missing for the literal g-indexed S2189 data: it is equivalent
to S2432EndComm. -/
def S2442S2189LiteralRequired : Prop :=
  Nonempty (S2189MuQZMulAutData p)

theorem S2442S2189Literal_iff_EndComm :
    S2442S2189LiteralRequired p ↔ S2432EndComm p :=
  (S2432EndComm_iff_nonempty_s2189 p).symm

/-- Exact first missing: joint continuity needs a declared topology T. -/
def S2442JointContinuityRequired (T : TopologicalSpace (muQZ p)) : Prop :=
  S2432ActionJointContinuous p T

/-- The S2159 muHat action is filled by the actual muQZ action. -/
noncomputable def S2442MuHatAction : Gv p →* MulAut (muHatZ p) :=
  S2432MuHatAction p

#check S2442MuQZMulAutData_actual
#check S2442MuQZAction_compat
#check S2442MuQZEnd_comp
#check S2442MuQZEnd_comp_inv
#check S2442MuQZEnd_inv_comp
#check S2442MuQZAction_continuous
#check S2442S2189Literal_iff_EndComm
#check S2442JointContinuityRequired
#check S2442MuHatAction

#print axioms S2442MuQZMulAutData_actual
#print axioms S2442MuQZAction_compat
#print axioms S2442MuQZEnd_comp
#print axioms S2442MuQZAction_continuous

end LeanFormal.IUT.XiFPaper.S2442MuQZFinalActual

end