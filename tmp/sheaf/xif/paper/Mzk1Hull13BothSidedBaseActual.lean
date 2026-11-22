import tmp.sheaf.xif.paper.Hull13TwoSidedBoundActual

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 2000000

noncomputable section

/-!
# STEP 0 prior-art: e-deep:E3.twoSided / iutiii:HULL.H7.OB9.WRAPPER advance -> Hull13TwoSidedBoundActual (HullH7Ob9TwoSidedInputs + hull13_twoSided_bound) -> both-sided BASE variant: add an explicit lower-bound-at-base input and derive two-sided bound at the base representative, plus the iterate two-sided bound; the deep Ob9 both-sided transfer remains the named input (no new math beyond assembling the two bounds). Registry frozen 14041. No closure.

# Mzk1Hull13BothSidedBaseActual — two-sided bounds at base representative (conditional)

PROVED:
* `hull13_baseTwoSided`: Cor 3.12 conclusion + two-sided bound at the base representative
  (baseLowerBound <= z <= comparison.bound) + two-sided bound at the (Ind3) iterate;
* `hull13_baseTwoSided_upper`: one-sided base upper-bound projection;
* `hull13_baseTwoSided_lower`: one-sided base lower-bound projection.
NAMED: `base_lower_bound` is an explicit hypothesis (deep arbitrary-iterate Ob9
both-sided transfer); no free Prop fields.
-/

namespace LeanFormal.IUT.XiFPaper.Mzk1Hull13BothSidedBaseActual

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
open LeanFormal.IUT.XiFPaper.S3182Cor312HullDetAssemblyActual

variable {l : PrimeGeFive} {V : Type uv}
variable (M : LGPModelSourceClauseMissing l)
variable [Fintype (Bad (nativePlaceSelection (lgpModelNativeData M)))]

/-- Both-sided base inputs: the two-sided iterate inputs plus an explicit lower bound
at the base representative (the named deep Ob9 both-sided transfer). -/
structure HullH7Ob9BaseTwoSidedInputs
    (I : OriginalInput.{ua, uv, upi, umon, ui} l V) where
  twoSided : HullH7Ob9TwoSidedInputs (l := l) M I
  baseLowerBound : ℝ
  base_lower_bound : ∀ z,
    z ∈ sourceMultiradialPossibleImage I
      (sourceMultiradialMap I twoSided.comparison.consumer.base) →
    baseLowerBound ≤ z

/-- **PROVED (conditional):** Cor 3.12 conclusion + two-sided bounds at base and at the
(Ind3) iterate. -/
theorem hull13_baseTwoSided
    (I : OriginalInput.{ua, uv, upi, umon, ui} l V)
    (In : HullH7Ob9BaseTwoSidedInputs (l := l) M I) :
    Cor312HullDetConclusion M In.twoSided.comparison.consumer.hull.theta ∧
      (∀ z, z ∈ sourceMultiradialPossibleImage I
        (sourceMultiradialMap I In.twoSided.comparison.consumer.base) →
        In.baseLowerBound ≤ z ∧ z ≤ In.twoSided.comparison.bound) ∧
      (∀ w, w ∈ sourceMultiradialPossibleImage I
        (sourceMultiradialMap I ((sourceStepXICore I).ind3
          In.twoSided.comparison.iterate In.twoSided.comparison.consumer.base)) →
        In.twoSided.lowerBound ≤ w ∧ w ≤ In.twoSided.comparison.bound) := by
  obtain ⟨hcor, hbound, hiter⟩ := hull13_twoSided_bound (M := M) I In.twoSided
  exact ⟨hcor, fun z hz => ⟨In.base_lower_bound z hz, hbound z hz⟩, hiter⟩

/-- One-sided base upper bound (PROVED projection). -/
theorem hull13_baseTwoSided_upper
    (I : OriginalInput.{ua, uv, upi, umon, ui} l V)
    (In : HullH7Ob9BaseTwoSidedInputs (l := l) M I) :
    ∀ z, z ∈ sourceMultiradialPossibleImage I
      (sourceMultiradialMap I In.twoSided.comparison.consumer.base) →
      z ≤ In.twoSided.comparison.bound :=
  (hull13_baseTwoSided (M := M) I In).2.1 |> fun h => fun z hz => (h z hz).2

/-- One-sided base lower bound (PROVED projection). -/
theorem hull13_baseTwoSided_lower
    (I : OriginalInput.{ua, uv, upi, umon, ui} l V)
    (In : HullH7Ob9BaseTwoSidedInputs (l := l) M I) :
    ∀ z, z ∈ sourceMultiradialPossibleImage I
      (sourceMultiradialMap I In.twoSided.comparison.consumer.base) →
      In.baseLowerBound ≤ z :=
  (hull13_baseTwoSided (M := M) I In).2.1 |> fun h => fun z hz => (h z hz).1

/-- Rows: proved assembly vs named deep Ob9 input. -/
def bothSidedBaseRows : List (String × String × String) :=
  [ ("two-sided iterate input + base lower input", "DEFINED", "HullH7Ob9BaseTwoSidedInputs")
  , ("Cor 3.12 + two-sided base and iterate bounds", "PROVED (conditional)", "hull13_baseTwoSided")
  , ("base upper projection", "PROVED", "hull13_baseTwoSided_upper")
  , ("base lower projection", "PROVED", "hull13_baseTwoSided_lower")
  , ("deep Ob9 both-sided transfer to base", "NAMED (explicit field)", "base_lower_bound hypothesis; arbitrary-iterate independence not formalized") ]

theorem bothSidedBaseRows_length : bothSidedBaseRows.length = 5 := rfl

#check HullH7Ob9BaseTwoSidedInputs
#check hull13_baseTwoSided
#check hull13_baseTwoSided_upper
#check hull13_baseTwoSided_lower
#check bothSidedBaseRows_length

end LeanFormal.IUT.XiFPaper.Mzk1Hull13BothSidedBaseActual
end