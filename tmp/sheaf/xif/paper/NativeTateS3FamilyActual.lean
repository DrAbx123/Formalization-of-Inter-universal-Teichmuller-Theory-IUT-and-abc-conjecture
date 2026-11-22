import tmp.sheaf.xif.paper.NativeTateS3IntegralityActual
import tmp.sheaf.xif.paper.NativeTateQSquaresIntegralityActual
import tmp.sheaf.xif.paper.NativeTateLambertIntegralityActual
import tmp.sheaf.xif.paper.NativeTateA6IntegralityActual

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

/-! # s3 field of the q-series integrality family -/

noncomputable section

namespace LeanFormal.IUT.XiFPaper.NativeTateS3FamilyActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.XiFPaper.NativeTateS3IntegralityActual
open LeanFormal.IUT.XiFPaper.NativeTateQSquaresIntegralityActual

universe u

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable (b : Bad (LeanFormal.IUT.N8Closure.nativePlaceSelection T))

/-- The family with the actual s3 field supplied; the remaining s5/a4/a6 fields
are the exact inputs. -/
noncomputable def TateQSquaresIntegralityFamily.ofS3
    (hq : Valued.v (q (l := l) T b) < 1)
    (h5 : ∃ s : localRing (l := l) T b,
      ((s : localRing (l := l) T b) : localField (l := l) T b) =
        TateCurve.lambertSeries (localField (l := l) T b) 5 (q (l := l) T b))
    (ha4 : ∃ a : localRing (l := l) T b,
      ((a : localRing (l := l) T b) : localField (l := l) T b) =
        TateCurve.a4 (localField (l := l) T b) (q (l := l) T b))
    (ha6 : ∃ a : localRing (l := l) T b,
      ((a : localRing (l := l) T b) : localField (l := l) T b) =
        TateCurve.a6 (localField (l := l) T b) (q (l := l) T b)) :
    TateQSquaresIntegralityFamily (l := l) T b where
  s3Integral := s3Integral (l := l) T b hq
  s5Integral := h5
  a4Integral := ha4
  a6Integral := ha6

/-- The s3 field of the constructed family is the actual s3 integrality. -/
theorem TateQSquaresIntegralityFamily.ofS3_s3
    (hq : Valued.v (q (l := l) T b) < 1)
    (h5 : ∃ s : localRing (l := l) T b,
      ((s : localRing (l := l) T b) : localField (l := l) T b) =
        TateCurve.lambertSeries (localField (l := l) T b) 5 (q (l := l) T b))
    (ha4 : ∃ a : localRing (l := l) T b,
      ((a : localRing (l := l) T b) : localField (l := l) T b) =
        TateCurve.a4 (localField (l := l) T b) (q (l := l) T b))
    (ha6 : ∃ a : localRing (l := l) T b,
      ((a : localRing (l := l) T b) : localField (l := l) T b) =
        TateCurve.a6 (localField (l := l) T b) (q (l := l) T b)) :
    (TateQSquaresIntegralityFamily.ofS3 (l := l) T b hq h5 ha4 ha6).s3Integral =
      s3Integral (l := l) T b hq := rfl

/-- The family with actual s3 and s5 fields; a4/a6 remain exact inputs. -/
noncomputable def TateQSquaresIntegralityFamily.ofS3S5
    (hq : Valued.v (NativeTateS3IntegralityActual.q (l := l) T b) < 1)
    (ha4 : ∃ a : localRing (l := l) T b,
      ((a : localRing (l := l) T b) : localField (l := l) T b) =
        TateCurve.a4 (localField (l := l) T b)
          (NativeTateS3IntegralityActual.q (l := l) T b))
    (ha6 : ∃ a : localRing (l := l) T b,
      ((a : localRing (l := l) T b) : localField (l := l) T b) =
        TateCurve.a6 (localField (l := l) T b)
          (NativeTateS3IntegralityActual.q (l := l) T b)) :
    TateQSquaresIntegralityFamily (l := l) T b :=
  TateQSquaresIntegralityFamily.ofS3 (l := l) T b hq
    (NativeTateLambertIntegralityActual.s5Integral (l := l) T b hq)
    ha4 ha6

/-- The family with actual s3, s5, a4; a6 remains an exact input. -/
noncomputable def TateQSquaresIntegralityFamily.ofS3S5A4
    (hq : Valued.v (NativeTateS3IntegralityActual.q (l := l) T b) < 1)
    (ha6 : ∃ a : localRing (l := l) T b,
      ((a : localRing (l := l) T b) : localField (l := l) T b) =
        TateCurve.a6 (localField (l := l) T b)
          (NativeTateS3IntegralityActual.q (l := l) T b)) :
    TateQSquaresIntegralityFamily (l := l) T b where
  s3Integral := s3Integral (l := l) T b hq
  s5Integral := NativeTateLambertIntegralityActual.s5Integral (l := l) T b hq
  a4Integral := NativeTateLambertIntegralityActual.a4Integral (l := l) T b hq
  a6Integral := ha6

/-- The fully actual q-series integrality family: s3, s5, a4, a6. -/
noncomputable def TateQSquaresIntegralityFamily.actual
    (hq : Valued.v (NativeTateS3IntegralityActual.q (l := l) T b) < 1) :
    TateQSquaresIntegralityFamily (l := l) T b where
  s3Integral := s3Integral (l := l) T b hq
  s5Integral := NativeTateLambertIntegralityActual.s5Integral (l := l) T b hq
  a4Integral := NativeTateLambertIntegralityActual.a4Integral (l := l) T b hq
  a6Integral := NativeTateA6IntegralityActual.a6Integral (l := l) T b hq

end LeanFormal.IUT.XiFPaper.NativeTateS3FamilyActual

end
