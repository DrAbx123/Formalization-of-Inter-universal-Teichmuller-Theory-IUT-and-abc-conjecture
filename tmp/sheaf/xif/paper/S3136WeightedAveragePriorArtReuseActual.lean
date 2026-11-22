import LeanFormal.IUT.IUTIV.Estimates.StepVProcessionAverage

/-! # Stage-4 host: reuse of the IV Step V weighted-average estimates

PRIOR ART (§7.9, checked first): LeanFormal/IUT/IUTIV/Estimates/StepVProcessionAverage.lean:
:35 collectionBound l D Q S T j = (j+1)D - j^2/(2l) Q + S + 4(j+1)T (IV L1736-1741);
:39 sum_collectionBound; :54 processionAverage_eq; :68 processionAverage_le (IV L1757-1783);
:100 exceptionalSum_le_r4 ((R4)); :125 collectionChoiceBound; :162 weightedAverage_labelBeta;
:190 weightedAverage_le_collectionBound; :217 processionNormalized_le_of_collectionBounds.

CONSUMER: the weighted-average side of the (c) estimate (IUT IV Prop 1.7 / Step V).
This file reuses the prior-art formula and its procession-normalized bound; no new
estimate is proved.

LABEL: reuse adapters (class A weighted-average supply).  Registry frozen; new file only. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 1000000

namespace LeanFormal.IUT.XiFPaper.S3136WeightedAveragePriorArtReuseActual

open Finset
open scoped BigOperators
open LeanFormal.IUT.IUTIV.StepVProcessionAverage

/-- The prior-art per-label collection bound (IV L1736-1741). -/
theorem lgpCollectionBound_eq (l D Q S T : ℝ) (j : ℕ) :
    collectionBound l D Q S T j =
      ((j : ℝ) + 1) * D - (j : ℝ) ^ 2 / (2 * l) * Q + S +
        4 * ((j : ℝ) + 1) * T :=
  rfl

/-- The prior-art procession-normalized upper bound (IV L1757-1783). -/
theorem lgpProcessionAverage_le (n : ℕ) (hn : 2 ≤ n) (D Q S T : ℝ)
    (hD : 0 ≤ D) (hS : 0 ≤ S) (hT : 0 ≤ T) :
    (1 / (n : ℝ)) * ∑ j ∈ Icc 1 n, collectionBound (2 * n + 1) D Q S T j ≤
      ((2 * (n : ℝ) + 1) + 1) / 4 *
        ((1 + 4 / (2 * (n : ℝ) + 1)) * D - Q / 6 +
          4 / (2 * (n : ℝ) + 1) * S + 20 / 3 * T) :=
  LeanFormal.IUT.IUTIV.StepVProcessionAverage.processionAverage_le n hn D Q S T hD hS hT

/-- Mapping rows: our LGP theta label quantities <-> IV Step V collection terms. -/
def lgpWeightedAverageMapping : List (String × String) :=
  [ ("label weight (gaussExponent j)^2", "collection term j^2/(2l) Q (the theta label q-term)"),
    ("label log d_K term", "(j+1) D"),
    ("label p/log term", "4 (j+1) T"),
    ("label s_Q term", "S"),
    ("procession average over j = 1..n, l = 2n+1", "processionAverage_eq / processionAverage_le (IV L1744-1783)") ]

theorem lgpWeightedAverageMapping_length : lgpWeightedAverageMapping.length = 5 := rfl

#check lgpCollectionBound_eq
#check lgpProcessionAverage_le
#check lgpWeightedAverageMapping_length

end LeanFormal.IUT.XiFPaper.S3136WeightedAveragePriorArtReuseActual
end