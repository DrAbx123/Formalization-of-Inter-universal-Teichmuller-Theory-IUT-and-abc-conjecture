import tmp.sheaf.xif.paper.Mzk1Hull13BothSidedBaseActual

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 2000000

noncomputable section

/-! # Hull13 both-sided base green consumer; no closure. Registry frozen 14041. -/

namespace LeanFormal.IUT.XiFPaper.Mzk1Hull13GreenConsumerActual

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
open LeanFormal.IUT.XiFPaper.Hull13TwoSidedBoundActual
open LeanFormal.IUT.XiFPaper.Mzk1Hull13BothSidedBaseActual
open LeanFormal.IUT.XiFPaper.S3182Cor312HullDetAssemblyActual

variable {l : PrimeGeFive} {V : Type uv}
variable (M : LGPModelSourceClauseMissing l)
variable [Fintype (Bad (nativePlaceSelection (lgpModelNativeData M)))]

theorem hull13Green_upper (I : OriginalInput.{ua, uv, upi, umon, ui} l V)
    (In : HullH7Ob9BaseTwoSidedInputs (l := l) M I) :
    ∀ z, z ∈ sourceMultiradialPossibleImage I
      (sourceMultiradialMap I In.twoSided.comparison.consumer.base) →
      z ≤ In.twoSided.comparison.bound :=
  fun z hz => ((hull13_baseTwoSided (M := M) I In).2.1 z hz).2

theorem hull13Green_lower (I : OriginalInput.{ua, uv, upi, umon, ui} l V)
    (In : HullH7Ob9BaseTwoSidedInputs (l := l) M I) :
    ∀ z, z ∈ sourceMultiradialPossibleImage I
      (sourceMultiradialMap I In.twoSided.comparison.consumer.base) →
      In.baseLowerBound ≤ z :=
  fun z hz => ((hull13_baseTwoSided (M := M) I In).2.1 z hz).1

theorem hull13Green_bundle (I : OriginalInput.{ua, uv, upi, umon, ui} l V)
    (In : HullH7Ob9BaseTwoSidedInputs (l := l) M I) :
    (∀ z, z ∈ sourceMultiradialPossibleImage I
      (sourceMultiradialMap I In.twoSided.comparison.consumer.base) →
      In.baseLowerBound ≤ z ∧ z ≤ In.twoSided.comparison.bound) ∧
      Cor312HullDetConclusion M In.twoSided.comparison.consumer.hull.theta :=
  ⟨(hull13_baseTwoSided (M := M) I In).2.1, (hull13_baseTwoSided (M := M) I In).1⟩

def hull13GreenRows : List (String × String × String) :=
  [ ("base two-sided bound bundle", "PROVED (conditional)", "hull13Green_bundle"),
    ("base upper bound", "PROVED (conditional)", "hull13Green_upper"),
    ("base lower bound (explicit named hypothesis)", "PROVED (conditional)", "hull13Green_lower") ]

theorem hull13GreenRows_length : hull13GreenRows.length = 3 := rfl

#check hull13Green_bundle
#check hull13GreenRows_length

end LeanFormal.IUT.XiFPaper.Mzk1Hull13GreenConsumerActual
end