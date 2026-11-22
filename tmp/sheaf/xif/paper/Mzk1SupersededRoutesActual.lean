import Mathlib

/-! # Mzk1SupersededRoutesActual — pruned routes record (A473/A475)

Real Lean record (no sorry/axiom): routes parked/superseded in the C/D area, with reasons.
Kept as explicit data so later consumers do not re-attack dead routes.  Registry 14041. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace LeanFormal.IUT.XiFPaper.Mzk1SupersededRoutesActual

/-- Row record: superseded/parked routes in the C/D areas. -/
def supersededRoutesRows : List (String × String) :=
  [ ("D.rrBridge / bridge_of_maps", "PARKED PRAGMATIC-DEAD-END (scheme-side maps repo-missing; A475 evidence)"),
    ("redfix:Mzk1GeomCoreLineBundleJointGenericActual", "PARK retracted after A475: NeronModelInfra exists in tmp/external/flt-lean"),
    ("old BetaAvoidingBelyiBaseInput (beta=infty)", "REFUTED; replaced by finite-beta corrected spec (Mzk1Rational24TargetBottomActual)"),
    ("literal 0/1 critical-value statement on unnormalized gPoly", "REFUTED (Mzk1CritValueInImageProofActual.s3135_critValueInImage_refuted)") ]

theorem supersededRoutesRows_length : supersededRoutesRows.length = 4 := rfl

end LeanFormal.IUT.XiFPaper.Mzk1SupersededRoutesActual
end
