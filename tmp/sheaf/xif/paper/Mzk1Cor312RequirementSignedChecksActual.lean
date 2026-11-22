import tmp.sheaf.xif.paper.Mzk1XiEContainmentRequirementActual
import tmp.sheaf.xif.paper.Mzk1SignedLogVolumeCor312Actual

/-!
# A544 chain-independent check: requirement strict signed inequality and C_Theta

Checks the non-vacuous xi-e requirement against the signed log-volume and the
paper `C_Theta >= -1` form, without importing the pending final assembly.

No sorry, axiom, True or placeholder.
-/

namespace LeanFormal.IUT.XiFPaper.Mzk1Cor312RequirementSignedChecksActual

open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.Mzk1XiEContainmentRequirementActual
open LeanFormal.IUT.XiFPaper.Mzk1SignedLogVolumeCor312Actual

universe u

/-- The requirement's non-vacuity witness is exactly the strict volume increase. -/
theorem requirement_strict_measure_exact {α : Type u} {vol : Set α → Real}
    (D : XiEContainmentRequirement α vol) :
    vol D.qRegion < vol D.hullRegion :=
  D.strict_measure

/-- Strict signed inequality of the requirement (not reflexive). -/
theorem requirement_signed_strict {α : Type u} {vol : Set α → Real}
    (D : XiEContainmentRequirement α vol) :
    requirementSignedQ D < requirementSignedTheta D :=
  requirement_strict_signed D

/-- The requirement's signed inequality in `C_Theta` form: if the hull reading is
`C * |log q|` and the q reading is `-|log q|` with `|log q| > 0`, then
`C >= -1`. -/
theorem requirement_CTheta_ge_neg_one {qMag C : Real} (hq : 0 < qMag)
    (hineq : -qMag ≤ C * qMag) : -1 ≤ C := by
  have hmul : (-1 : Real) * qMag ≤ C * qMag :=
    calc (-1 : Real) * qMag = -qMag := by ring
      _ ≤ C * qMag := hineq
  exact le_of_mul_le_mul_right hmul hq

/-- Strict `C_Theta` form of the requirement. -/
theorem requirement_CTheta_gt_neg_one {qMag C : Real} (hq : 0 < qMag)
    (hineq : -qMag < C * qMag) : -1 < C := by
  have hmul : (-1 : Real) * qMag < C * qMag :=
    calc (-1 : Real) * qMag = -qMag := by ring
      _ < C * qMag := hineq
  exact lt_of_mul_lt_mul_right hmul (le_of_lt hq)

end LeanFormal.IUT.XiFPaper.Mzk1Cor312RequirementSignedChecksActual
