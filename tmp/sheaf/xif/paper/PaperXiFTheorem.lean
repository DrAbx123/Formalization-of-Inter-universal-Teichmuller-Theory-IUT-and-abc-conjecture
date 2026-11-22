import tmp.sheaf.xif.paper.PaperXiFSpec
import tmp.sheaf.xif.PaperXiFInclusion

/-! # Paper xi-f: from the actual inclusion data to the scalar xi-f statement

This file composes the conditional paper-level `PaperXiFInclusion` (actual
PaperQPilotObject + PaperSignedHull + PaperQPilotLogVolume) with the scalar
statement layer `PaperXiFSpec`. It does not assert an inhabitant of the
link; it proves that, given the actual paper inclusion data, the scalar
xi-f statement and its Cor3.12 lower bound follow.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace LeanFormal.IUT.XiFPaper

open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.N8Closure.SourcePilotRegion
open LeanFormal.IUT.XiFPaper

universe ua uv upi umon ui uL uC uG uX uLabel

variable {l : PrimeGeFive} {V : Type uv}
variable {Label : Type uL} {Choice : Type uC} [AddGroup Label] [Preorder Choice]
variable {I : OriginalInput.{ua, uv, upi, umon, ui} l V}
variable {G : Type uG} [Group G] [TopologicalSpace G]
variable {envStrip : FPrimeStrip V}
variable {X : Type uX} {label : Type uLabel} [Fintype label]
variable {O : PaperQPilotObject (Label := Label) (Choice := Choice) I G envStrip}
variable {P : PaperSignedHull X label}
variable {C3 : SourcePilotRegionData I}

/-- The paper xi-f scalar statement holds for the actual q parameter and the
actual signed hull log-volume, given the paper-level inclusion data. -/
theorem paperXiF_of_inclusion (J : PaperXiFInclusion O P C3) :
    paperXiF (paperQParameter C3) P.signedHullLogVolume := by
  unfold paperXiF paperHullRay paperSignedLog
  rw [← J.qPilotLogVolume_eq_neg_abs_qParameter]
  exact J.qPilot_le_signedHull

/-- Packaged scalar xi-f data from the actual paper inclusion. -/
def paperXiFScalarDataOfInclusion (J : PaperXiFInclusion O P C3) :
    PaperXiFScalarData where
  q := paperQParameter C3
  q_pos := paperQParameter_pos C3
  q_log_ne_zero := paperQParameter_log_ne_zero C3
  thetaHullLog := P.signedHullLogVolume
  xi_f := paperXiF_of_inclusion J

/-- The final Cor3.12 lower bound from the actual paper inclusion. -/
theorem paperXiF_cTheta_lowerBound (J : PaperXiFInclusion O P C3) {cTheta : Real}
    (hc : P.signedHullLogVolume ≤ cTheta * |Real.log (paperQParameter C3)|) :
    -1 ≤ cTheta :=
  (paperXiFScalarDataOfInclusion J).cTheta_lowerBound hc

/-- The signed q-pilot log-volume is the paper `-|log q|`. -/
theorem paperXiF_qPilot_eq_paperSignedLog (J : PaperXiFInclusion O P C3) :
    O.qPilotLogVolume = paperSignedLog (paperQParameter C3) := by
  rw [J.qPilotLogVolume_eq_neg_abs_qParameter]
  rfl

end XiFPaper
end LeanFormal.IUT

end