import LeanFormal.IUT.IUTIII.Corollary312.StepXI.HolomorphicHull.IQCarrierHaarData
import tmp.sheaf.xif.paper.S3132IQHullRealLogVolumeReadoutActual

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 2000000

noncomputable section

namespace LeanFormal.IUT.XiFPaper.S3132SourceHullReadoutCriterionActual

open MeasureTheory
open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput

universe ua uv upi umon ui

variable {l : PrimeGeFive} {V : Type uv}
variable (I : OriginalInput.{ua, uv, upi, umon, ui} l V)
variable (v : V) (R : I.SourceImageRealization v)
variable (n : ThetaPilotCarrier l)

/-!
# H_C readout criterion on the actual value carrier, and the concrete readout

The actual paper holomorphic hull of the theta-pilot image is the value-realized
`sourceHolomorphicHull` (Remark 3.9.5 least `lambda·O` hull).  This file pins
the H_C readout on that actual hull:

* finite hull log-volume is exactly the existence of an `IQHullLogVolumeInterface`
  realization whose log-volume is the actual source set log-volume and whose hull
  is the actual source holomorphic hull (no interface weakening);
* conversely, from finiteness the pinned realization is constructed from the
  actual hull alone (`sourceHullUnitScalingInterface`);
* under pointwise degree faithfulness the value-level hull log-volume is `⊤`
  and no such pinned realization exists, so H_C finiteness on the value carrier
  is not derivable from `OriginalInput` at this realization;
* on the concrete-completion carrier the actual H_C readout is finite
  (`S3129IQHullLogVolumeSourceActual` / `S3132IQHullRealLogVolumeReadoutActual`);
  the two carriers are NOT identified anywhere in the tree, and that
  identification is the remaining exact object obligation.

Source: IUT III, Corollary 3.12 proof; Remark 3.9.5, (i), (ii); IUT III
Theorem 3.11 (multiradial representation).  No new axiom, no sorry, no carrier
substitution.
-/

/-- **Pinned H_C realization from finiteness.**  From finiteness of the actual
hull log-volume, the actual hull itself realizes the paper-level interface with
the actual source set log-volume and the actual source holomorphic hull. -/
theorem sourceHullReadout_of_finite
    (hfin : I.sourceHullVolume v R n < ⊤) :
    ∃ W : IQHullLogVolumeInterface (I.ThetaPilotPoint v),
      W.logVolume = I.sourceSetVolume v ∧
        W.hull = (I.sourceHolomorphicHull v R n : Set (I.ThetaPilotPoint v)) ∧
        W.logVolume W.hull = I.sourceHullVolume v R n := by
  refine ⟨I.sourceHullUnitScalingInterface v R n hfin, rfl, rfl, ?_⟩
  rfl

/-- **H_C finiteness criterion, pinned form.**  The actual hull log-volume is
finite exactly when the pinned interface realization exists. -/
theorem sourceHullReadout_finite_iff_exists_pinnedInterface :
    I.sourceHullVolume v R n < ⊤ ↔
      ∃ W : IQHullLogVolumeInterface (I.ThetaPilotPoint v),
        W.logVolume = I.sourceSetVolume v ∧
          W.hull = (I.sourceHolomorphicHull v R n : Set (I.ThetaPilotPoint v)) := by
  constructor
  · intro hfin
    obtain ⟨W, hvol, hhull, _⟩ := sourceHullReadout_of_finite I v R n hfin
    exact ⟨W, hvol, hhull⟩
  · rintro ⟨W, hvol, hhull⟩
    have h := W.hull_logVolume_lt_top
    rw [hvol, hhull] at h
    exact h

/-- **Value-level obstruction.**  Under pointwise degree faithfulness there is no
pinned H_C realization on the value carrier with the actual source log-volume. -/
theorem sourceHullReadout_obstructed_of_degreeFaithful
    (hdeg : ∀ b : ℝ,
      I.logDegreeAt 0 0 v (R.posRealAction (Multiplicative.ofAdd b)) = b) :
    ¬ ∃ W : IQHullLogVolumeInterface (I.ThetaPilotPoint v),
        W.logVolume = I.sourceSetVolume v ∧
          W.hull = (I.sourceHolomorphicHull v R n : Set (I.ThetaPilotPoint v)) :=
  I.not_exists_iqHullLogVolumeInterface_hull_eq_of_degreeFaithful v R n hdeg

/-- **Cross-carrier reading, honestly stated.**  On the actual concrete
completion the H_C readout is finite with the actual normalized Haar measure,
while on the actual value carrier under pointwise degree faithfulness no pinned
H_C realization exists.  Both facts are theorems about their own actual
carriers; no identification between the carriers is asserted. -/
theorem concreteHullReadout_finite_and_valueHullReadout_obstructed
    (hdeg : ∀ b : ℝ,
      I.logDegreeAt 0 0 v (R.posRealAction (Multiplicative.ofAdd b)) = b) :
    LeanFormal.IUT.XiFPaper.S3129IQHullLogVolumeSourceActual.sourceIQHullLogVolume.logVolume
        LeanFormal.IUT.XiFPaper.S3129IQHullLogVolumeSourceActual.sourceIQHullLogVolume.hull
        < ⊤ ∧
      ¬ ∃ W : IQHullLogVolumeInterface (I.ThetaPilotPoint v),
          W.logVolume = I.sourceSetVolume v ∧
            W.hull = (I.sourceHolomorphicHull v R n : Set (I.ThetaPilotPoint v)) :=
  ⟨LeanFormal.IUT.XiFPaper.S3129IQHullLogVolumeSourceActual.sourceIQHull_hull_logVolume_lt_top,
    sourceHullReadout_obstructed_of_degreeFaithful I v R n hdeg⟩

/-- The concrete-carrier H_C real readout is the `toReal` of the finite actual
hull Haar volume, so the concrete carrier supplies the real-valued H_C
quantity whose value-carrier analogue is obstructed. -/
theorem concreteHullRealReadout_ofReal_eq :
    LeanFormal.IUT.XiFPaper.S3129IQHullLogVolumeSourceActual.sourceIQHullLogVolume.logVolume
        LeanFormal.IUT.XiFPaper.S3129IQHullLogVolumeSourceActual.sourceIQHullLogVolume.hull =
      ENNReal.ofReal
        LeanFormal.IUT.XiFPaper.S3132IQHullRealLogVolumeReadoutActual.sourceHullRealLogVolume :=
  LeanFormal.IUT.XiFPaper.S3132IQHullRealLogVolumeReadoutActual.sourceIQHull_logVolume_eq_ofReal

#check sourceHullReadout_of_finite
#check sourceHullReadout_finite_iff_exists_pinnedInterface
#check sourceHullReadout_obstructed_of_degreeFaithful
#check concreteHullReadout_finite_and_valueHullReadout_obstructed

end LeanFormal.IUT.XiFPaper.S3132SourceHullReadoutCriterionActual

end