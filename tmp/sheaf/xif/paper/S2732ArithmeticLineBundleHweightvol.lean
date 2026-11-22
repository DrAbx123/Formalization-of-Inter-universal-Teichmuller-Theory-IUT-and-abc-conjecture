import tmp.sheaf.xif.paper.ArithmeticLineBundleActual
import LeanFormal.IUT.ABCBridge.Arithmetic.RationalPrimeSupport
import LeanFormal.IUT.ABCBridge.Arithmetic.RationalPointDictionary

noncomputable section
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaperArithmeticLineBundle
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.XiFPaper.S2732ArithmeticLineBundleHweightvol

variable {l : PrimeGeFive}
variable {A : InitialThetaArithmeticData l}

/-- The arithmetic line-bundle global log-volume used as the region volume. -/
noncomputable def S2732LineBundleRegionVolume
    (P : PaperArithmeticLineBundleActual A) : Real :=
  P.detData.globalLogVolume

/-- It is the log of the absolute norm of the line bundle (actual formula). -/
theorem S2732LineBundleRegionVolume_eq
    (P : PaperArithmeticLineBundleActual A) :
    S2732LineBundleRegionVolume  P =
      Real.log ((FractionalIdeal.absNorm P.lineBundle : Rat) : Real) :=
  P.globalLogVolume_formula

/-- hweightvol with the actual arithmetic line-bundle log-volume as region volume
and an explicit unit-volume constant. -/
def S2732ArithmeticLineBundleHweightvol
    (P : PaperArithmeticLineBundleActual A) (unitVol : Real) : Prop :=
  ∀ a n c : Nat, IsABCTriple a n c →
    arithmeticWeight (abcRationalPoint a c)
      ≤ S2732LineBundleRegionVolume  P + unitVol

/-- Expanded form via the actual globalLogVolume_formula. -/
theorem S2732ArithmeticLineBundleHweightvol_iff
    (P : PaperArithmeticLineBundleActual A) (unitVol : Real) :
    S2732ArithmeticLineBundleHweightvol  P unitVol ↔
      ∀ a n c : Nat, IsABCTriple a n c →
        arithmeticWeight (abcRationalPoint a c)
          ≤ Real.log ((FractionalIdeal.absNorm P.lineBundle : Rat) : Real) + unitVol := by
  unfold S2732ArithmeticLineBundleHweightvol S2732LineBundleRegionVolume
  rw [show P.detData.globalLogVolume =
      Real.log ((FractionalIdeal.absNorm P.lineBundle : Rat) : Real) from
    P.globalLogVolume_formula]

end LeanFormal.IUT.XiFPaper.S2732ArithmeticLineBundleHweightvol
end
