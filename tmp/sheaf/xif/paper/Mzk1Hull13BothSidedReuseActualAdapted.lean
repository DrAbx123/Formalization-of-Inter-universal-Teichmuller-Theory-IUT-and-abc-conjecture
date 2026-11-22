import tmp.sheaf.xif.paper.Mzk1Hull13BothSidedBaseActual

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

/-! Mainline: reuse chain for Hull13 both-sided-base consumer (re-export projections). -/

namespace LeanFormal.IUT.XiFPaper.Mzk1Hull13BothSidedReuseActualAdapted

universe ua uv upi umon ui u

open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.XiFPaper.Hull13H7Ob9ComparisonConsumerActual
open LeanFormal.IUT.XiFPaper.Hull13TwoSidedBoundActual
open LeanFormal.IUT.XiFPaper.Mzk1Hull13BothSidedBaseActual

variable {l : PrimeGeFive} {V : Type uv}
variable (M : LGPModelSourceClauseMissing l)
variable [Fintype (Bad (nativePlaceSelection (lgpModelNativeData M)))]

theorem baseTwoSided_reuse
    (I : OriginalInput.{ua, uv, upi, umon, ui} l V)
    (In : HullH7Ob9BaseTwoSidedInputs (l := l) M I) :
    Cor312HullDetConclusion M In.twoSided.comparison.consumer.hull.theta ∧
      (∀ z, z ∈ sourceMultiradialPossibleImage I
        (sourceMultiradialMap I In.twoSided.comparison.consumer.base) →
        In.baseLowerBound ≤ z ∧ z ≤ In.twoSided.comparison.bound) := by
  obtain ⟨hcor, hbase, _⟩ := hull13_baseTwoSided (M := M) I In
  exact ⟨hcor, hbase⟩

theorem baseTwoSided_upper_reuse
    (I : OriginalInput.{ua, uv, upi, umon, ui} l V)
    (In : HullH7Ob9BaseTwoSidedInputs (l := l) M I) :
    ∀ z, z ∈ sourceMultiradialPossibleImage I
      (sourceMultiradialMap I In.twoSided.comparison.consumer.base) →
      z ≤ In.twoSided.comparison.bound :=
  hull13_baseTwoSided_upper (M := M) I In

theorem baseTwoSided_lower_reuse
    (I : OriginalInput.{ua, uv, upi, umon, ui} l V)
    (In : HullH7Ob9BaseTwoSidedInputs (l := l) M I) :
    ∀ z, z ∈ sourceMultiradialPossibleImage I
      (sourceMultiradialMap I In.twoSided.comparison.consumer.base) →
      In.baseLowerBound ≤ z :=
  hull13_baseTwoSided_lower (M := M) I In

end LeanFormal.IUT.XiFPaper.Mzk1Hull13BothSidedReuseActualAdapted