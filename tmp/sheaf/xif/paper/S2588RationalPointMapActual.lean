import tmp.sheaf.xif.paper.S2587Cor312PointMapSkeletonActual
import LeanFormal.IUT.Foundations.LocalFields.FinitePadicTensorTopology
import LeanFormal.IUT.Foundations.NumberField.SourceQvClosed

noncomputable section
open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.LocalFieldPadicTensor
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.S2587Cor312PointMapSkeletonActual
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.XiFPaper.S2588RationalPointMapActual

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable (b : Bad (nativePlaceSelection T))

/-- The actual rational point `a/c` mapped into the one-factor tensor block. -/
noncomputable def S2588PointMap : Nat -> Nat -> Nat -> qVFamTensorBlock T b :=
  fun a _ c =>
    letI : Algebra T.arithmetic.F
        (CommonPrimeCompletion (qVFamTensorPlaces T b () ())) :=
      inferInstanceAs (Algebra T.arithmetic.F
        (LeanFormal.IUT.NumberFieldFinitePlace.Completion
          (qVFamTensorPlaces T b () ()).val))
    (finitePadicTensorTprod (p := qVFamTensorP T b)
      (fun _ : Unit => CommonPrimeCompletion (qVFamTensorPlaces T b () ())))
      (fun _ => algebraMap T.arithmetic.F
        (CommonPrimeCompletion (qVFamTensorPlaces T b () ()))
        (algebraMap Rat T.arithmetic.F (abcRationalPoint a c)))

#check S2588PointMap
#print axioms S2588PointMap

end LeanFormal.IUT.XiFPaper.S2588RationalPointMapActual
end