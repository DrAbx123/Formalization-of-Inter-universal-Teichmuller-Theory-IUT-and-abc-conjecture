/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.gogopex.Iut.Stage1.PilotComparison
import tmp.sheaf.gogopex.Iut.Stage1.CorollarySchema

/-! # A516: O5 pilot-comparison objects (Gogopex Stage1 consumers) -/

noncomputable section

namespace LeanFormal.IUT.Objects.GogopexPilot

open Iut RealLineCopy

/-- The pilot-comparison object: the Stage 1 comparison data of Gogopex, packaging the
q- and Theta-pilot log-volumes with their signed comparison. -/
structure PilotComparisonObject where
  /-- The Gogopex Stage 1 comparison. -/
  data : Stage1.Stage1Comparison

variable (D : PilotComparisonObject)

/-- The object yields the Corollary 3.12 signed inequality (Gogopex consumer). -/
theorem PilotComparisonObject.corollary312 :
    corollary312_from_stage1_comparison D.data :=
  Stage1.corollary312_from_stage1_comparison D.data

/-- The Theta-pilot side tag is `theta`. -/
theorem PilotComparisonObject.theta_side : D.data.theta.side = PilotSide.theta := 
  D.data.theta_side

/-- The q-pilot side tag is `q`. -/
theorem PilotComparisonObject.q_side : D.data.q.side = PilotSide.q := 
  D.data.q_side

/-- The q-pilot stored magnitude is positive. -/
theorem PilotComparisonObject.q_positive : 0 < D.data.q.value := 
  D.data.q_positive

/-- Build a pilot-comparison object from the signed q/Theta comparison data. -/
def pilotComparisonObjectOf (C : Stage1.Corollary312ComparisonData) :
    PilotComparisonObject where
  data := C.stage1Comparison

/-- The built object's comparison is exactly the Gogopex Corollary 3.12 inequality. -/
theorem pilotComparisonObjectOf_comparison (C : Stage1.Corollary312ComparisonData) :
    (pilotComparisonObjectOf C).data.comparison = C.corollary312 :=
  C.stage1Comparison_comparison_eq_corollary312

end LeanFormal.IUT.Objects.GogopexPilot
