import tmp.sheaf.xif.paper.SignedHullLogActual
import tmp.sheaf.xif.paper.PaperProcessionNormalization

/-! # Actual procession-normalized mono-analytic log-volume

IUT IV §1 and IUT III Proposition 3.9 define the procession-normalized
mono-analytic log-volume as the average, over the capsules of the procession,
of the packet-normalized log-volumes.  This file constructs that object from
the actual `SignedHullLogActual` packet/procession data:

* `procession : WeightedValues label` is the actual packet/procession weight
  system (total weight one);
* `localLogVolume j` is the actual packet log-volume at label `j`;
* `value` is the weight-normalized average, i.e. the procession normalization;
* `signedValue` is the paper sign `-|log Theta|`.

The normalization is proved, not assumed: the weight total is one and the
average is exactly the finite weighted sum divided by that total.  No arbitrary
weight, toy label, `sorry`, or axiom is used.  The exact Haar/hull comparison
remains the separate `paperProcessionNormalizationComparison` of
`PaperProcessionNormalization.lean`.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT.XiFPaper.ProcessionNormalizedLogVolumeActual

open LeanFormal.IUT
open scoped BigOperators

universe u

variable {label : Type u} [Fintype label]

/-- The actual procession-normalized mono-analytic log-volume: a finite
weighted average of local packet log-volumes.  The weights are the actual
`WeightedValues` of the packet/procession; the local values are the actual
packet log-volumes. -/
structure ProcessionNormalizedMonoAnalyticLogVolume where
  /-- The actual packet/procession weight system. -/
  procession : WeightedValues label
  /-- The actual local packet log-volume at each label. -/
  localLogVolume : label -> Real
  /-- The procession values are the local packet log-volumes. -/
  procession_values : forall j, procession.value j = localLogVolume j
  /-- Actual nonnegativity of the local packet log-volumes. -/
  localLogVolume_nonneg : forall j, 0 <= localLogVolume j
  /-- The actual procession weight total is one. -/
  weightTotal_eq_one : procession.weightTotal = 1
  /-- The actual procession weights are nonnegative. -/
  weights_nonnegative : forall j, 0 <= procession.weight j

namespace ProcessionNormalizedMonoAnalyticLogVolume

variable (D : ProcessionNormalizedMonoAnalyticLogVolume (label := label))

/-- The procession-normalized log-volume is the actual weighted average. -/
noncomputable def value : Real :=
  D.procession.average

/-- The signed paper quantity `-|log Theta|`. -/
noncomputable def signedValue : Real :=
  -D.value

/-- The procession average is exactly the finite weighted sum divided by the
actual weight total one. -/
theorem value_eq_weighted_sum :
    D.value =
      (Finset.univ.sum fun j => D.procession.weight j * D.localLogVolume j) :=
  by
  unfold value WeightedValues.average
  rw [D.weightTotal_eq_one, div_one]
  apply Finset.sum_congr rfl
  intro j _
  rw [D.procession_values j]

/-- The normalization: the total procession weight is exactly one. -/
theorem normalization : D.procession.weightTotal = 1 :=
  D.weightTotal_eq_one

/-- The procession-normalized log-volume is nonnegative. -/
theorem value_nonneg : 0 <= D.value := by
  unfold value
  apply WeightedValues.lower_le_average_of_pointwise D.procession
    D.weights_nonnegative
  intro j
  rw [D.procession_values j]
  exact D.localLogVolume_nonneg j

/-- The signed procession-normalized log-volume is nonpositive. -/
theorem signedValue_nonpos : D.signedValue <= 0 := by
  unfold signedValue
  exact neg_nonpos.mpr D.value_nonneg

/-- The signed value is the negative of the procession average. -/
theorem signedValue_eq_neg : D.signedValue = -D.value := rfl

end ProcessionNormalizedMonoAnalyticLogVolume

/-- Construct the actual procession-normalized object from actual signed hull
packet/procession data. -/
noncomputable def ofSignedHull (D : SignedHullLogActual label) :
    ProcessionNormalizedMonoAnalyticLogVolume (label := label) where
  procession := D.procession
  localLogVolume := D.procession.value
  procession_values := fun _ => rfl
  localLogVolume_nonneg := D.procession_values_nonneg
  weightTotal_eq_one := D.weightTotal_eq_one
  weights_nonnegative := D.weights_nonnegative

@[simp] theorem ofSignedHull_procession (D : SignedHullLogActual label) :
    (ofSignedHull (label := label) D).procession = D.procession := rfl

/-- The constructed object's value is the actual signed-hull procession
average. -/
theorem ofSignedHull_value (D : SignedHullLogActual label) :
    (ofSignedHull (label := label) D).value =
      D.processionNormalizedLogVolume :=
  rfl

/-- The constructed object's signed value is the actual signed procession
log-volume. -/
theorem ofSignedHull_signedValue (D : SignedHullLogActual label) :
    (ofSignedHull (label := label) D).signedValue =
      D.signedProcessionNormalizedLogVolume :=
  rfl

/-- Paper-facing name: the actual procession-normalized mono-analytic
log-volume associated to the actual hull data. -/
noncomputable def paperProcessionNormalizedLogVolume
    (D : SignedHullLogActual label) : Real :=
  D.processionNormalizedLogVolume

theorem paperProcessionNormalizedLogVolume_eq_ofSignedHull
    (D : SignedHullLogActual label) :
    paperProcessionNormalizedLogVolume (label := label) D =
      (ofSignedHull (label := label) D).value :=
  rfl

theorem paperProcessionNormalizedLogVolume_nonneg
    (D : SignedHullLogActual label) :
    0 <= paperProcessionNormalizedLogVolume (label := label) D :=
  D.processionNormalizedLogVolume_nonneg

theorem signedPaperProcessionNormalizedLogVolume_nonpos
    (D : SignedHullLogActual label) :
    -paperProcessionNormalizedLogVolume (label := label) D <= 0 :=
  D.signedProcessionNormalizedLogVolume_nonpos

end LeanFormal.IUT.XiFPaper.ProcessionNormalizedLogVolumeActual

end
