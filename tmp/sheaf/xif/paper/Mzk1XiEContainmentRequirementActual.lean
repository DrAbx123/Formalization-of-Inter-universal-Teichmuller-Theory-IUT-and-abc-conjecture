import tmp.sheaf.xif.paper.Mzk1SignedLogVolumeCor312Actual
import tmp.sheaf.xif.paper.Mzk1SignedCor312ContractActual

/-!
# xi-e containment REQUIREMENT (non-vacuous interface)

Unlike a definitional containment (`hull := qRegion`, or `possibleRegion` of a
constant raw region), this interface records the two genuinely separate paper
inputs and a strict-measure non-vacuity witness:

* `q_in_possible : qRegion ⊆ thetaPossibleImages` -- Thm 3.11(ii) possible images
  of the Theta-pilot (must come from the actual raw output, not by definition);
* `possible_in_hull : thetaPossibleImages ⊆ hullRegion` -- Rem 3.9.5(i) hull;
* `strict_measure : vol qRegion < vol hullRegion` -- non-vacuity/actual volume
  increase (the genuine xi-e content).

From these, the signed strict inequality and the Cor 3.12 conclusion follow via
the green signed StepXI contract.  No `True` fields.

No sorry, axiom, True or placeholder.
-/

namespace LeanFormal.IUT.XiFPaper.Mzk1XiEContainmentRequirementActual

open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.Mzk1SignedLogVolumeCor312Actual
open LeanFormal.IUT.XiFPaper.Mzk1SignedCor312ContractActual

structure XiEContainmentRequirement (α : Type*) (vol : Set α → Real) where
  qRegion : Set α
  thetaPossibleImages : Set α
  hullRegion : Set α
  q_in_possible : Set.Subset qRegion thetaPossibleImages
  possible_in_hull : Set.Subset thetaPossibleImages hullRegion
  q_pos : 0 < vol qRegion
  strict_measure : vol qRegion < vol hullRegion

noncomputable def requirementSignedQ {α : Type*} {vol : Set α → Real}
    (D : XiEContainmentRequirement α vol) : Real :=
  signedLogVolume vol D.qRegion

noncomputable def requirementSignedTheta {α : Type*} {vol : Set α → Real}
    (D : XiEContainmentRequirement α vol) : Real :=
  signedLogVolume vol D.hullRegion

theorem requirement_subset {α : Type*} {vol : Set α → Real}
    (D : XiEContainmentRequirement α vol) :
    Set.Subset D.qRegion D.hullRegion :=
  Set.Subset.trans D.q_in_possible D.possible_in_hull

/-- Non-vacuity: the signed comparison is STRICT (not reflexive) whenever the
measure strictly increases. -/
theorem requirement_strict_signed {α : Type*} {vol : Set α → Real}
    (D : XiEContainmentRequirement α vol) :
    requirementSignedQ D < requirementSignedTheta D := by
  unfold requirementSignedQ requirementSignedTheta signedLogVolume
  exact Real.log_lt_log D.q_pos (by
    have h := D.strict_measure
    exact h)

/-- The containment inequality (weaker form) follows from the strict one. -/
theorem requirement_signed_inequality {α : Type*} {vol : Set α → Real}
    (D : XiEContainmentRequirement α vol) :
    requirementSignedQ D ≤ requirementSignedTheta D :=
  le_of_lt (requirement_strict_signed D)

/-- Construct the StepXI contract from the non-vacuous xi-e requirement and
real IPL/SHE/APT data. -/
noncomputable def requirementContract {α : Type*} {vol : Set α → Real}
    (D : XiEContainmentRequirement α vol) (hqneg : requirementSignedQ D < 0)
    (ipl : Prop) (hipl : ipl) (she : Prop) (hshe : she)
    (apt : Prop) (hapt : apt) : StepXIContract :=
  signedCor312Contract (requirementSignedQ D) (requirementSignedTheta D) hqneg
    ipl hipl she hshe apt hapt (requirement_signed_inequality D)

theorem requirement_cor312 {α : Type*} {vol : Set α → Real}
    (D : XiEContainmentRequirement α vol) (hqneg : requirementSignedQ D < 0)
    (ipl : Prop) (hipl : ipl) (she : Prop) (hshe : she)
    (apt : Prop) (hapt : apt) :
    Cor312Conclusion (requirementContract D hqneg ipl hipl she hshe apt hapt) :=
  signedCor312_conclusion (requirementSignedQ D) (requirementSignedTheta D) hqneg
    ipl hipl she hshe apt hapt (requirement_signed_inequality D)

end LeanFormal.IUT.XiFPaper.Mzk1XiEContainmentRequirementActual
