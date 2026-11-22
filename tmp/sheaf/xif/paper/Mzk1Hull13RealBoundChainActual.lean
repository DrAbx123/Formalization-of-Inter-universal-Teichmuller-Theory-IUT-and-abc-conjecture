import tmp.sheaf.xif.paper.Hull13TwoSidedBoundActual
import tmp.sheaf.xif.paper.Hull13H7Ob9ComparisonConsumerActual

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

noncomputable section

/-!
# Mzk1Hull13RealBoundChainActual — A480 real bound chain consumer (H7/Ob9)

New conclusions chaining the existing H7/Ob9 consumers:

1. `hull13_realLogBound_chain`: from the two-sided inputs, the real hull
   log-volume readout equality and its theta bound are extracted together with
   the base upper bound and the iterate two-sided bound;
2. `hull13_oneSided_of_twoSided`: the one-sided comparison consumer is
   recovered from the two-sided inputs.

No sorry/axioms; no closure claim.
-/

namespace LeanFormal.IUT.XiFPaper.Mzk1Hull13RealBoundChainActual

universe ua uv upi umon ui

open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.N8Closure
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

/-- **Four-component H7/Ob9 real-bound chain.** -/
theorem hull13_realLogBound_chain
    (I : OriginalInput.{ua, uv, upi, umon, ui} l V)
    (In : HullH7Ob9TwoSidedInputs (l := l) M I) :
    Real.log sourceHullRealLogVolume = modelThetaValue M ∧
      Real.log sourceHullRealLogVolume ≤ In.comparison.consumer.hull.theta ∧
      (∀ z, z ∈ sourceMultiradialPossibleImage I
        (sourceMultiradialMap I In.comparison.consumer.base) →
        z ≤ In.comparison.bound) ∧
      (∀ w, w ∈ sourceMultiradialPossibleImage I
        (sourceMultiradialMap I ((sourceStepXICore I).ind3 In.comparison.iterate
          In.comparison.consumer.base)) →
        In.lowerBound ≤ w ∧ w ≤ In.comparison.bound) := by
  obtain ⟨hcor, hbase, htwo⟩ := hull13_twoSided_bound (M := M) I In
  exact ⟨hcor.1, hcor.2, hbase, htwo⟩

/-- **One-sided comparison recovered from two-sided inputs.** -/
theorem hull13_oneSided_of_twoSided
    (I : OriginalInput.{ua, uv, upi, umon, ui} l V)
    (In : HullH7Ob9TwoSidedInputs (l := l) M I) :
    Cor312HullDetConclusion M In.comparison.consumer.hull.theta ∧
      (∀ z, z ∈ sourceMultiradialPossibleImage I
        (sourceMultiradialMap I In.comparison.consumer.base) →
        z ≤ In.comparison.bound) :=
  hull13_h7ob9_comparison (M := M) I In.comparison

#check hull13_realLogBound_chain
#check hull13_oneSided_of_twoSided

end LeanFormal.IUT.XiFPaper.Mzk1Hull13RealBoundChainActual
end