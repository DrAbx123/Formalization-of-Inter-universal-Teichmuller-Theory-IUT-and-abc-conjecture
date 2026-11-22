import tmp.sheaf.xif.paper.Mzk1StepVProcessionActual
import tmp.sheaf.xif.paper.Mzk1P6StepVAveragesActual

noncomputable section
open scoped BigOperators
namespace LeanFormal.IUT.XiFPaper.ULStepVWeightsActual
open LeanFormal.IUT
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.Mzk1StepVProcessionActual
open LeanFormal.IUT.XiFPaper.Mzk1P6StepVAveragesActual
open LeanFormal.IUT.XiFPaper.S3014StepVProcessionAverageActual
open LeanFormal.IUT.XiFPaper.S3029StepVAlignmentActual

universe u v w
variable {K : Type u} [Field K] [NumberField K] {p : Nat} [Fact p.Prime]
variable {ι : Type v} [Fintype ι] {V : ι -> Type w}
variable (places : (i : ι) -> V i -> FinitePlaceAtPrime K p)
variable (tuple : (i : ι) -> V i) (istar : ι)
variable (jValue : CommonPrimeCompletion (places istar (tuple istar)))
variable (exceptional : Finset ι) (l n : Nat)

/-- Actual U-L StepV weight package: the distinguished volume, the procession
average, the different/divisor term, and the per-label volume family, all taken
from the actual StepV donors (no chosen weights). -/
structure StepVWeightsData
    (places : (i : ι) -> V i -> FinitePlaceAtPrime K p)
    (tuple : (i : ι) -> V i) (istar : ι)
    (jValue : CommonPrimeCompletion (places istar (tuple istar)))
    (exceptional : Finset ι) (l n : Nat) where
  /-- The distinguished-slot volume at label 1. -/
  distinguished : ℝ
  /-- The procession average (1/n) * sum of per-label volumes. -/
  processionAverage : ℝ
  /-- The actual different term of the packet. -/
  divisor : ℝ
  /-- The per-label StepV volume family. -/
  volume : Nat → ℝ

/-- Actual construction from the StepV procession/volume donors. -/
noncomputable def stepVWeightsData
    (h : StepVExtraNonneg (p := p) places tuple exceptional) :
    StepVWeightsData places tuple istar jValue exceptional l n where
  distinguished := stepVVolume (p := p) places tuple istar jValue l 1
  processionAverage :=
    (1 / (n : ℝ)) *
      (∑ label ∈ Finset.Icc 1 n,
        stepVVolume (p := p) places tuple istar jValue l label)
  divisor := S3029DifferentTerm places tuple
  volume := stepVVolume (p := p) places tuple istar jValue l

/-- The actual weight package exists. -/
theorem stepVWeightsData_nonempty
    (h : StepVExtraNonneg (p := p) places tuple exceptional) :
    Nonempty (StepVWeightsData places tuple istar jValue exceptional l n) :=
  ⟨stepVWeightsData (p := p) places tuple istar jValue exceptional l n h⟩

/-- The distinguished volume is exactly the StepV volume donor at label 1. -/
theorem distinguished_eq_volume_one
    (h : StepVExtraNonneg (p := p) places tuple exceptional) :
    (stepVWeightsData (p := p) places tuple istar jValue exceptional l n h).distinguished =
      stepVVolume (p := p) places tuple istar jValue l 1 := rfl

/-- The procession average is exactly the normalized sum of the per-label
volumes. -/
theorem processionAverage_eq
    (h : StepVExtraNonneg (p := p) places tuple exceptional) :
    (stepVWeightsData (p := p) places tuple istar jValue exceptional l n h).processionAverage =
      (1 / (n : ℝ)) *
        (∑ label ∈ Finset.Icc 1 n,
          stepVVolume (p := p) places tuple istar jValue l label) := rfl

/-- The actual StepV weight package's procession average is bounded by the
accepted S3014 procession average bound. -/
theorem stepVWeightsData_average_le
    (h : StepVExtraNonneg (p := p) places tuple exceptional) :
    (stepVWeightsData (p := p) places tuple istar jValue exceptional l n h).processionAverage ≤
      S3014ProcessionAverageBound places tuple istar jValue exceptional l n := by
  unfold stepVWeightsData
  exact stepVProcessionAverage_bound (p := p) places tuple istar jValue exceptional l n h

#print axioms stepVWeightsData_nonempty
#print axioms stepVWeightsData_average_le
end LeanFormal.IUT.XiFPaper.ULStepVWeightsActual
end
