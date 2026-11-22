import tmp.sheaf.xif.paper.Mzk1Stage4S1902HullConcreteActual

/-! # Mzk1Stage4S1902HullDataEvidenceActual (stage4 lane; supplementary evidence)

A615 module (supplementary evidence; canonical instances are hull's
`Mzk1S1902IQHullInterfaceActual` and mainline's `Mzk1S1902BridgeInterfaceActual`, which
this file does NOT modify): normalized measure evidence for the concrete hull data.
No new mathematics.  Registry frozen 14041. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 1000000

namespace LeanFormal.IUT.XiFPaper.Mzk1Stage4S1902HullDataEvidenceActual

open MeasureTheory
open scoped ENNReal
open LeanFormal.IUT.XiFPaper.Mzk1Stage4S1902HullConcreteActual

/-- The concrete hull's real-valued measure is `2`. -/
theorem concreteHull_toReal :
    (volume (concreteHull.region)).toReal = 2 := by
  rw [concreteHull_measure]
  norm_num

/-- Normalized (half) measure of the concrete hull is `1`. -/
theorem concreteHull_normalized :
    (volume (concreteHull.region)).toReal / 2 = 1 := by
  rw [concreteHull_toReal]
  norm_num

/-- The concrete hull data's measure value equals the model constant 2. -/
theorem concreteHull_measure_value :
    (volume concreteHull.region).toReal = (2 : Real) :=
  concreteHull_toReal

#check concreteHull_toReal
#check concreteHull_normalized
#check concreteHull_measure_value

end LeanFormal.IUT.XiFPaper.Mzk1Stage4S1902HullDataEvidenceActual
end
