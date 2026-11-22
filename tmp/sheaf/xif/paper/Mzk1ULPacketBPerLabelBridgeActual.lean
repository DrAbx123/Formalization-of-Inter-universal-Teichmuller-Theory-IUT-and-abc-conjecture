/-
# C1 bridge: packetB = paper Step (v) per-label bound (conditional on the λ order)

The U-L C1 packet bound is
  packetB = (-localNormOrder varpi + sum_i localNormOrder different_i + 1) log p
            + sum_{i in exceptional} (3 + log e_i),
while the paper Step (v) per-label bound (S3014PerLabelBound) is the same formula
with -localNormOrder varpi replaced by the paper lambda
  stepVLambda p label jValue l = label^2 * (-localNormOrder jValue) / (2*l),
i.e. the root value-group order.  This file records the exact identity under the
order identification hlambda.  The representative with that fractional order does
not exist in the completion (no 2l-th root: S342QVFamilyRootImpossibleActual), so
hlambda is a genuine input here (interface only); the identity itself is a
definition unfolding, no extra mathematics.
-/
import tmp.sheaf.xif.paper.Mzk1ULPacketVActual
import tmp.sheaf.xif.paper.S3014StepVProcessionAverageActual
import Mathlib.Tactic

noncomputable section
open scoped BigOperators
namespace LeanFormal.IUT.XiFPaper.Mzk1ULPacketBPerLabelBridgeActual

open LeanFormal.IUT
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.LocalFieldLogarithm

universe u v w
variable {K : Type u} [Field K] [NumberField K] {p : Nat} [Fact p.Prime]
variable {ι : Type v} [Fintype ι] [DecidableEq ι]
variable {V : ι → Type w} [∀ i, Fintype (V i)] [∀ i, DecidableEq (V i)]
variable (places : (i : ι) → V i → FinitePlaceAtPrime K p)
variable (tuple : (i : ι) → V i) (istar : ι)
variable (jValue : CommonPrimeCompletion (places istar (tuple istar)))
variable (exceptional : Finset ι) (l label : Nat)

/-- C1 bridge (conditional on the distinguished representative order): packetB is
the paper Step (v) per-label bound. -/
theorem packetB_eq_perLabelBound
    (varpi : CommonPrimeCompletion (places istar (tuple istar)))
    (hlam : localNormOrder p varpi = stepVLambda p label jValue l) :
    LeanFormal.IUT.XiFPaper.Mzk1ULPacketVActual.packetB places tuple istar varpi exceptional =
      LeanFormal.IUT.XiFPaper.S3014StepVProcessionAverageActual.S3014PerLabelBound
        places tuple istar jValue exceptional l label := by
  unfold LeanFormal.IUT.XiFPaper.Mzk1ULPacketVActual.packetB
    LeanFormal.IUT.XiFPaper.S3014StepVProcessionAverageActual.S3014PerLabelBound
  rw [hlam]
  ring

/-- The same bridge applied label-wise to the procession average: the average of
the packet C1 bounds is the average of the paper Step (v) per-label bounds, given a
label family of representatives with the prescribed orders. -/
theorem avg_packetB_eq_processionAverage
    (n : Nat) (varpi : Nat → CommonPrimeCompletion (places istar (tuple istar)))
    (hlam : ∀ label, localNormOrder p (varpi label) = stepVLambda p label jValue l) :
    (1 / (n : ℝ)) * (∑ label ∈ Finset.Icc 1 n,
        LeanFormal.IUT.XiFPaper.Mzk1ULPacketVActual.packetB places tuple istar
          (varpi label) exceptional) =
      LeanFormal.IUT.XiFPaper.S3014StepVProcessionAverageActual.S3014ProcessionAverageBound
        places tuple istar jValue exceptional l n := by
  unfold LeanFormal.IUT.XiFPaper.S3014StepVProcessionAverageActual.S3014ProcessionAverageBound
  congr 1
  refine Finset.sum_congr rfl ?_
  intro label _
  exact packetB_eq_perLabelBound (p := p) places tuple istar jValue exceptional l label
    (varpi label) (hlam label)

#print axioms packetB_eq_perLabelBound
#print axioms avg_packetB_eq_processionAverage

end LeanFormal.IUT.XiFPaper.Mzk1ULPacketBPerLabelBridgeActual
end