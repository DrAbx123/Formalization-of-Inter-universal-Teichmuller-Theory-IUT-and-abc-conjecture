import tmp.sheaf.xif.paper.S1687Torsion23RealizationActual
noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S1687Torsion23RealizationActual
namespace LeanFormal.IUT.XiFPaper.S1698ThreeTorsionExhaustionActual
def S1698FinrankSix : Prop := Module.finrank ℚ S1687Field = 6
def S1698ThreeTorsionOverFClassified : Prop := S1687ThreeTorsionOverFClassified
def S1698Torsion23Rational : Prop := S1687Torsion23Missing
theorem S1698Torsion23_of_missing (h : S1687ExactFirstMissing) :
    S1698Torsion23Rational := h.1
#check S1698FinrankSix
#check S1698ThreeTorsionOverFClassified
#check S1698Torsion23Rational
#check S1698Torsion23_of_missing
end LeanFormal.IUT.XiFPaper.S1698ThreeTorsionExhaustionActual
end
