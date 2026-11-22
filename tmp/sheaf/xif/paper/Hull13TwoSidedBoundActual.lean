import tmp.sheaf.xif.paper.Hull13H7Ob9ComparisonConsumerActual

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 2000000

noncomputable section

/-!
# STEP 0 prior-art: Hull13 one-sided comparison|upper bound|two-sided -> hits Hull13H7Ob9ComparisonConsumerActual:55-76 (HullH7Ob9ComparisonInputs, hull13_h7ob9_comparison one-sided), Hull12Ob9BoundTransferActual:52 (upper-bound transfer) -> ADAPT (two-sided conditional version; lower-bound input explicit; both-sided transfer to base stays named).

# Hull13TwoSidedBoundActual — two-sided (conditional) version of the Hull13 comparison

Adds an explicit LOWER bound at the (Ind3) iterate to the Hull13 consumer, obtaining
the two-sided bound at the iterate together with the Cor 3.12 conclusion and the base
upper bound.  The both-sided transfer of the lower bound to the base representative
remains a DEEP Ob9 named input (not formalized).  No closure; registry frozen 14041.
-/

namespace LeanFormal.IUT.XiFPaper.Hull13TwoSidedBoundActual

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

variable {l : PrimeGeFive} {V : Type uv}
variable (M : LGPModelSourceClauseMissing l)
variable [Fintype (Bad (nativePlaceSelection (lgpModelNativeData M)))]

/-- Two-sided comparison inputs: the Hull13 one-sided inputs plus an explicit LOWER
bound at the chosen (Ind3) iterate.  (The lower bound is a hypothesis/data, not a
claimed theorem; transferring it to the base representative is the named deep Ob9
input.) -/
structure HullH7Ob9TwoSidedInputs
    (I : OriginalInput.{ua, uv, upi, umon, ui} l V) where
  comparison : HullH7Ob9ComparisonInputs (l := l) M I
  lowerBound : ℝ
  lower_bound_at_iterate : ∀ w,
    w ∈ sourceMultiradialPossibleImage I
      (sourceMultiradialMap I ((sourceStepXICore I).ind3 comparison.iterate
        comparison.consumer.base)) → lowerBound ≤ w

/-- **Two-sided comparison consumer (conditional):** from the Hull13 inputs and the
lower-bound input at the iterate, get the Cor 3.12 hull+det conclusion, the base
possible-image upper bound, AND the two-sided bound at the iterate. -/
theorem hull13_twoSided_bound
    (I : OriginalInput.{ua, uv, upi, umon, ui} l V)
    (In : HullH7Ob9TwoSidedInputs (l := l) M I) :
    Cor312HullDetConclusion M In.comparison.consumer.hull.theta ∧
      (∀ z, z ∈ sourceMultiradialPossibleImage I
        (sourceMultiradialMap I In.comparison.consumer.base) → z ≤ In.comparison.bound) ∧
      (∀ w, w ∈ sourceMultiradialPossibleImage I
        (sourceMultiradialMap I ((sourceStepXICore I).ind3 In.comparison.iterate
          In.comparison.consumer.base)) →
        In.lowerBound ≤ w ∧ w ≤ In.comparison.bound) := by
  obtain ⟨hcor, hbound⟩ := hull13_h7ob9_comparison (M := M) I In.comparison
  refine ⟨hcor, hbound, ?_⟩
  intro w hw
  exact ⟨In.lower_bound_at_iterate w hw, In.comparison.bound_at_iterate w hw⟩

/-- The one-sided (base) upper bound still holds (projection of the two-sided
consumer). -/
theorem hull13_twoSided_upper_projection
    (I : OriginalInput.{ua, uv, upi, umon, ui} l V)
    (In : HullH7Ob9TwoSidedInputs (l := l) M I) :
    ∀ z, z ∈ sourceMultiradialPossibleImage I
      (sourceMultiradialMap I In.comparison.consumer.base) → z ≤ In.comparison.bound :=
  (hull13_twoSided_bound (M := M) I In).2.1

/-- Row record: proved two-sided-at-iterate vs named deep both-sided transfer. -/
def hull13TwoSidedRows : List (String × String × String) :=
  [ ("one-sided base upper bound (Hull13)", "A", "REUSED-PROVED hull13_h7ob9_comparison")
  , ("lower bound at the (Ind3) iterate", "HYPOTHESIS", "explicit data field HullH7Ob9TwoSidedInputs.lower_bound_at_iterate (not derived)")
  , ("two-sided bound at the iterate", "A", "PROVED hull13_twoSided_bound (conditional on the lower-bound input)")
  , ("both-sided transfer of the lower bound to the base representative", "B-NAMED", "deep Ob9 named input (arbitrary-iterate independence/both-sidedness not formalized)") ]

theorem hull13TwoSidedRows_length : hull13TwoSidedRows.length = 4 := rfl

#check HullH7Ob9TwoSidedInputs
#check hull13_twoSided_bound
#check hull13_twoSided_upper_projection
#check hull13TwoSidedRows_length

end LeanFormal.IUT.XiFPaper.Hull13TwoSidedBoundActual
end