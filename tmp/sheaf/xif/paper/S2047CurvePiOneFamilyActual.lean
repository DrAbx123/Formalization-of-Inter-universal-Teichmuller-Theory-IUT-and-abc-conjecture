import tmp.sheaf.xif.paper.S2038PaperOActual

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000
namespace LeanFormal.IUT.XiFPaper.S2047CurvePiOneFamilyActual
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S2038PaperOActual
open LeanFormal.IUT.XiFPaper.S1951KummerEvaluationSquareActual (PaperV)

structure S2047CurvePiOneFamily where
  piOne : (v : PaperV) → CurvePiOneData v
  geometric_nontrivial :
    ∀ v, Nontrivial (piOne v).proj.ker

def S2047CurvePiOneFamilyRequired : Prop :=
  Nonempty S2047CurvePiOneFamily

end LeanFormal.IUT.XiFPaper.S2047CurvePiOneFamilyActual
end