import tmp.sheaf.xif.paper.S2736QPilotLineBundleHweightvol
import LeanFormal.IUT.ABCBridge.Arithmetic.RationalPrimeSupport

noncomputable section
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S2736QPilotLineBundleHweightvol
open LeanFormal.IUT.XiFPaper.S2735QPilotLineBundleActual
open LeanFormal.IUT.XiFPaperArithmeticLineBundle
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.XiFPaper.S2743ConditionalHweightvolActual

variable {l : PrimeGeFive}

theorem S2743ConditionalHweightvol
    (J : Nat -> Nat -> Nat -> Ideal (SourceOK (A := S2735Arithmetic l)))
    (habs : forall a b c : Nat, IsABCTriple a b c ->
      natRadical (a * b * c) <= FractionalIdeal.absNorm (qPilotLineBundleExtended (l := l) (J a b c))) :
    S2736QPilotLineBundleHweightvol (l := l) J 0 := by
  intro a n c habc
  rw [arithmeticWeight_abcRationalPoint habc]
  simp only [S2736QPilotLineBundleLogVolume, add_zero]
  apply Real.log_le_log
  · exact_mod_cast natRadical_pos (a * n * c)
  · exact_mod_cast habs a n c habc

end LeanFormal.IUT.XiFPaper.S2743ConditionalHweightvolActual
end
