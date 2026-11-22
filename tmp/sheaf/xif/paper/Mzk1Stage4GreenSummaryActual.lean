import tmp.sheaf.xif.paper.Mzk1Stage4ABCStage5EvidenceActual
import tmp.sheaf.xif.paper.Mzk1Stage4Gap2NumericWitnessActual
import tmp.sheaf.xif.paper.Mzk1Stage4HeightRegionNumericsActual
import tmp.sheaf.xif.paper.Mzk1Stage4FinalAcceptanceSelfcheckActual

/-! # Mzk1Stage4GreenSummaryActual (stage4 lane; unique filename)

A577 module: stage4-lane green summary — one consumer statement per green stage4 result.
Registry frozen 14041. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 2000000

namespace LeanFormal.IUT.XiFPaper.Mzk1Stage4GreenSummaryActual

open LeanFormal.IUT.XiFPaper.Mzk1Stage4Gap2NumericWitnessActual
open LeanFormal.IUT.XiFPaper.Mzk1Stage4HeightRegionNumericsActual

/-- Green summary: numeric Gap2 height bound witness. -/
theorem green_gap2 : ∃ A : Real, (1 : Real) <= (1 + 1 / 10) * 1 + A :=
  gap2_numeric_witness

/-- Green summary: numeric Theorem 1.10 instance. -/
theorem green_theorem110 :
    (1 / 6 : Real) * degQ11 <= theorem110RHS :=
  theorem110_11a1_l13

/-- Green summary: `e_mod^*` numeric value. -/
theorem green_eModStar : eModStar = 552960 :=
  eModStar_eq

/-- Green summary: the log bound for 11. -/
theorem green_log_bound : Real.log (11 : Real) < 11 :=
  log_eleven_bound

#check green_gap2
#check green_theorem110
#check green_eModStar
#check green_log_bound

end LeanFormal.IUT.XiFPaper.Mzk1Stage4GreenSummaryActual
end
