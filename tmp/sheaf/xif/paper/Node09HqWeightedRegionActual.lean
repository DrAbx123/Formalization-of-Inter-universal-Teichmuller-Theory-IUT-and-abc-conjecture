import tmp.sheaf.xif.paper.Node09HqMultConsumerActual
import tmp.sheaf.xif.paper.Node09RelativeNormConsumerActual

noncomputable section
open scoped BigOperators
open LeanFormal.IUT
open LeanFormal.IUT.N8Closure.NativeInput
open LeanFormal.IUT.N8Closure.NativeC3
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.ArithmeticQPilotBaseChange
open LeanFormal.IUT.XiFPaper.Node09HqMultConsumerActual

namespace LeanFormal.IUT.XiFPaper.Node09HqWeightedRegionActual

variable {l : PrimeGeFive}
variable {F : Type*} [Field F] [NumberField F] {p : Nat} [Fact p.Prime]

/-- Node09 weighted product-region exact interface. -/
structure Node09HqWeightedRegion (X : N8NativeInput l)
    (b : FinitePlaceAtPrime F p → Bad (nativePlaceSelection X.S))
    (Fdeg l : ℝ) (logIdx diff : FinitePlaceAtPrime F p → ℝ) : Prop where
  baseQCandidate : Nonempty (FinitePlaceQCandidate (nativeBadBasePlace X))
  A_bound : (1 / (2 * l)) * (∑ i : FinitePlaceAtPrime F p,
      fiberMult X b i / Fdeg *
        Real.log (((completionRationalPrime (i.val)).val : ℕ) : ℝ)) ≤
    ∑ i : FinitePlaceAtPrime F p, (logIdx i + diff i)

/-- Constructor from the two DONE node09 consumer conclusions. -/
theorem node09_hq_weighted_region_of_components (X : N8NativeInput l)
    (b : FinitePlaceAtPrime F p → Bad (nativePlaceSelection X.S))
    (Fdeg l : ℝ) (logIdx diff : FinitePlaceAtPrime F p → ℝ)
    (hbase : Nonempty (FinitePlaceQCandidate (nativeBadBasePlace X)))
    (hA : (1 / (2 * l)) * (∑ i : FinitePlaceAtPrime F p,
        fiberMult X b i / Fdeg *
          Real.log (((completionRationalPrime (i.val)).val : ℕ) : ℝ)) ≤
      ∑ i : FinitePlaceAtPrime F p, (logIdx i + diff i)) :
    Node09HqWeightedRegion X b Fdeg l logIdx diff :=
  ⟨hbase, hA⟩

end LeanFormal.IUT.XiFPaper.Node09HqWeightedRegionActual
