import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

/-!
# A530 xi comparison mechanism audit: NO containment between the two pilots

Paper sources:
* IUT III 860-904: `-|log(q)|` is the log-volume of the q-pilot object;
  `-|log(Theta)|` is the log-volume of the holomorphic hull of the possible
  images of the Theta-pilot object.  They are different objects; neither is a
  subset of the other.  `-|log(Theta)|` is regarded as a positive multiple of
  `-|log(q)|` plus a possible error term (896-898).
* IUT III 10329-10353: both are procession-normalized mono-analytic log-volumes;
  Cor 3.12 concludes `-|log(Theta)| >= -|log(q)|` and `C_Theta >= -1`.
* IUT III 10823-10898 (xi-d)-(xi-f): the actual mechanism is the multiradial
  construction algorithm + IPL/SHE: the q-pilot log-volume is a possible
  Theta-pilot output log-volume, hence the formal inclusion
  `-|log(q)| in R_{<= -|log(Theta)|}`; no geometric subset `qRegion <= hull`
  is used.

Consequence: a monotone log-volume on a containment `qRegion <= hull` gives
`-logVolume hull <= -logVolume qRegion`, the WRONG direction from Cor 3.12.
This file records that direction error and the correct signed comparison
interface (`theta = C*q + err`, `C_Theta >= -1`), leaving the multiradial
comparison itself as an explicit named input. -/

namespace LeanFormal.IUT.XiFPaper.Mzk1XiComparisonMechanismAuditActual

/-- A monotone log-volume and containment give the reverse signed direction. -/
theorem containment_gives_reverse_direction {X : Type*} (logVolume : Set X → Real)
    (mono : ∀ {S T : Set X}, S ⊆ T → logVolume S ≤ logVolume T)
    {qRegion hull : Set X} (hsub : qRegion ⊆ hull) :
    -logVolume hull ≤ -logVolume qRegion := by
  have h := mono hsub
  linarith

/-- The paper comparison interface: two DIFFERENT signed pilot log-volumes
(`-|log Theta|`, `-|log q|`), a positive-multiple coefficient `C`, and an error
term, with the paper inequality as an explicit named field. -/
structure XiSignedComparison where
  /-- `-|log(Theta)|`: signed Theta-pilot hull log-volume. -/
  thetaSigned : Real
  /-- `-|log(q)|`: signed q-pilot log-volume. -/
  qSigned : Real
  /-- Positive-multiple coefficient in `theta = C*q + err`. -/
  C : Real
  /-- Error term. -/
  err : Real
  q_neg : qSigned < 0
  relation : thetaSigned = C * qSigned + err
  /-- Paper `C_Theta`: coefficient with `-|log(Theta)| <= C_Theta*|log(q)|`. -/
  CTheta : Real
  theta_le_CTheta : thetaSigned ≤ CTheta * (-qSigned)
  /-- NAMED multiradial comparison (Thm 3.11/xi-e), not containment. -/
  multiradial_comparison : qSigned ≤ thetaSigned

/-- Cor 3.12 conclusion `C_Theta >= -1`, from the multiradial comparison and the
definition of `C_Theta`. -/
theorem cTheta_ge_neg_one (D : XiSignedComparison) : -1 ≤ D.CTheta := by
  have hqpos : (0 : Real) < -D.qSigned := neg_pos.mpr D.q_neg
  have h : D.qSigned ≤ D.CTheta * (-D.qSigned) :=
    le_trans D.multiradial_comparison D.theta_le_CTheta
  nlinarith [h, hqpos]

/-- The signed Cor 3.12 inequality, exactly as a theorem from the named
multiradial comparison. -/
theorem cor312_signed_inequality (D : XiSignedComparison) :
    D.qSigned ≤ D.thetaSigned := D.multiradial_comparison

/-- The coefficient form `C_Theta >= -1` is the paper's equivalent formulation. -/
theorem cTheta_ge_neg_one_iff (D : XiSignedComparison) :
    D.qSigned ≤ D.thetaSigned ↔ -1 ≤ D.CTheta := by
  constructor
  · intro _; exact cTheta_ge_neg_one D
  · intro _; exact D.multiradial_comparison

end LeanFormal.IUT.XiFPaper.Mzk1XiComparisonMechanismAuditActual

end
