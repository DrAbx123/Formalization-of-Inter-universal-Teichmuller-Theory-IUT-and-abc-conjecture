import tmp.sheaf.xif.paper.Hull13TwoSidedBoundActual

/-!
  Mainline: H7/Ob9 two-sided sandwich projections (real re-exports of the
  conditional two-sided consumer; the deep both-sided transfer remains named).
-/

namespace LeanFormal.IUT.XiFPaper.Mzk1H7Ob9SandwichLawsActual

universe ua uv upi umon ui u

open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.S3136NativeHaarFamilyActual
open LeanFormal.IUT.XiFPaper.S3136ModelSourceClauseActual
open LeanFormal.IUT.XiFPaper.S3136ModelNativeDataWithHaarActual
open LeanFormal.IUT.XiFPaper.S3138SourceProcessionCoreActual
open LeanFormal.IUT.XiFPaper.S3139SourceMultiradialQuotientActual
open LeanFormal.IUT.XiFPaper.Indet05RouteMultiradialClassActual
open LeanFormal.IUT.XiFPaper.Indet06H7Ob9WiringActual
open LeanFormal.IUT.XiFPaper.Hull10H7Ob9ConsumerActual
open LeanFormal.IUT.XiFPaper.Hull12Ob9BoundTransferActual
open LeanFormal.IUT.XiFPaper.Hull13H7Ob9ComparisonConsumerActual
open LeanFormal.IUT.XiFPaper.S3182Cor312HullDetAssemblyActual
open LeanFormal.IUT.XiFPaper.Hull13TwoSidedBoundActual

variable {l : PrimeGeFive} {V : Type uv}
variable (M : LGPModelSourceClauseMissing l)
variable [Fintype (Bad (nativePlaceSelection (lgpModelNativeData M)))]

/-- Lower-bound projection of the conditional two-sided consumer. -/
theorem hull13_twoSided_lower_projection
    (I : OriginalInput.{ua, uv, upi, umon, ui} l V)
    (In : HullH7Ob9TwoSidedInputs (l := l) M I) :
    ∀ w, w ∈ sourceMultiradialPossibleImage I
      (sourceMultiradialMap I ((sourceStepXICore I).ind3 In.comparison.iterate
        In.comparison.consumer.base)) →
      In.lowerBound ≤ w :=
  fun w hw => (hull13_twoSided_bound (M := M) I In).2.2 w hw |>.1

/-- Sandwich projection: both bounds hold simultaneously on the iterate image. -/
theorem hull13_twoSided_sandwich
    (I : OriginalInput.{ua, uv, upi, umon, ui} l V)
    (In : HullH7Ob9TwoSidedInputs (l := l) M I) :
    ∀ w, w ∈ sourceMultiradialPossibleImage I
      (sourceMultiradialMap I ((sourceStepXICore I).ind3 In.comparison.iterate
        In.comparison.consumer.base)) →
      In.lowerBound ≤ w ∧ w ≤ In.comparison.bound :=
  fun w hw => (hull13_twoSided_bound (M := M) I In).2.2 w hw

/-- Consistency of the two bounds: on a nonempty iterate image the lower bound is
below the upper bound. -/
theorem hull13_twoSided_lower_le_upper
    (I : OriginalInput.{ua, uv, upi, umon, ui} l V)
    (In : HullH7Ob9TwoSidedInputs (l := l) M I)
    (hne : (sourceMultiradialPossibleImage I
      (sourceMultiradialMap I ((sourceStepXICore I).ind3 In.comparison.iterate
        In.comparison.consumer.base))).Nonempty) :
    In.lowerBound ≤ In.comparison.bound := by
  obtain ⟨w, hw⟩ := hne
  exact le_trans ((hull13_twoSided_bound (M := M) I In).2.2 w hw).1
    ((hull13_twoSided_bound (M := M) I In).2.2 w hw).2
end LeanFormal.IUT.XiFPaper.Mzk1H7Ob9SandwichLawsActual