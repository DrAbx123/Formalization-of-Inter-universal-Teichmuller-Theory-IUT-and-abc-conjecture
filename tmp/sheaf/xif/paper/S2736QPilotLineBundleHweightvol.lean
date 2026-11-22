import tmp.sheaf.xif.paper.S2735QPilotLineBundleActual
import tmp.sheaf.xif.paper.ArithmeticLineBundleActual
import LeanFormal.IUT.ABCBridge.Arithmetic.RationalPrimeSupport
import LeanFormal.IUT.ABCBridge.Arithmetic.RationalPointDictionary

noncomputable section
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaperArithmeticLineBundle
open LeanFormal.IUT.XiFPaper.S2735QPilotLineBundleActual
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.XiFPaper.S2736QPilotLineBundleHweightvol

variable {l : PrimeGeFive}

/-- The actual q-pilot extended line-bundle log-volume used as region volume. -/
noncomputable def S2736QPilotLineBundleLogVolume
    (J : Ideal (SourceOK (A := S2735Arithmetic l))) : Real :=
  Real.log ((FractionalIdeal.absNorm (qPilotLineBundleExtended (l := l) J) : Rat) : Real)

/-- hweightvol over the q-pilot line bundle extended by the ABC-support factor J. -/
def S2736QPilotLineBundleHweightvol
    (J : Nat -> Nat -> Nat -> Ideal (SourceOK (A := S2735Arithmetic l)))
    (unitVol : Real) : Prop :=
  ∀ a n c : Nat, IsABCTriple a n c →
    arithmeticWeight (abcRationalPoint a c)
      ≤ S2736QPilotLineBundleLogVolume (l := l) (J a n c) + unitVol

theorem S2736QPilotLineBundleLogVolume_eq
    (J : Ideal (SourceOK (A := S2735Arithmetic l))) :
    S2736QPilotLineBundleLogVolume (l := l) J =
      Real.log ((FractionalIdeal.absNorm (qPilotLineBundleExtended (l := l) J) : Rat) : Real) := rfl

end LeanFormal.IUT.XiFPaper.S2736QPilotLineBundleHweightvol
end
