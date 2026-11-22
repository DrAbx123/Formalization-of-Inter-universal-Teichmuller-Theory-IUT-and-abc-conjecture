import LeanFormal.IUT.IUTIII.Corollary312.StepXI.HolomorphicHull.SourceHullCompactnessReduction
import LeanFormal.IUT.IUTIII.Corollary312.StepXI.HolomorphicHull.Volume

/-!
# Paper-level signed 1,circ U hull log-volume

This file builds the paper-level signed hull carrier from the actual project
ingredients, without using the value-layer sourceThetaHullLogVolume sSup:

* IQHullLogVolumeInterface is the project's paper-level ambient
  compactness/Haar data interface for the carrier
  IQ(S±_{j+1}; n,circ D^vdash_{vQ}), with the hull, image union, unit region,
  lambda-scaling, normalized Haar log-volume and the compactness containment
  hull subset lambda * unitRegion (SourceHullCompactnessReduction.lean).
* FiniteHull and WeightedValues are the project's finite procession-average
  carriers (Volume.lean).
* PaperSignedHull ties them together: the procession average of the finite
  hull data is identified with the ambient hull log-volume, and the signed
  paper quantity -|log(Theta)| is defined as the negative of the ambient
  normalized hull log-volume.

The construction is conditional on exact source data:
(1) a realization of IQHullLogVolumeInterface for the actual paper carrier;
(2) the finite procession/hull data and their matching with the ambient hull;
(3) the normalized procession average equality;
(4) nonnegativity of that average.
None of these is postulated as a theorem or hidden axiom; they are fields of
the structure, and no inhabitant of PaperSignedHull is asserted. The actual
paper carrier and its compactness/Haar/procession normalization remain source
obligations. In particular this file does not use sourceThetaHullLogVolume or
the value-layer sSup, and it does not claim paper xi-f.

Corpus anchors: IUT III, Corollary 3.12, Step (xi), and Remark 3.9.5, (i),
(ii), (iii); corpus lines 7654-7750 (lambda * O hull and compactness),
10354-10410 (1,circ U compactness/finiteness), 10823-10899 (signed
-|log(Theta)| and the comparison). No fake proof, no axiom, no toy instance.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT

noncomputable section

universe u v

/-- Paper-level signed hull data. The ambient interface is the project's
paper-level compactness/Haar interface; the finite hull and weighted values
are the procession-average carrier. The equality fields are exact source
obligations, not consequences of the data interface. -/
structure PaperSignedHull (X : Type u) (label : Type v) [Fintype label] where
  /-- Paper-level ambient carrier data: hull, image union, unit region,
  lambda-scaling, normalized Haar log-volume, compactness containment. -/
  ambient : IQHullLogVolumeInterface X
  /-- Finite procession weights and values. -/
  procession : WeightedValues label
  /-- Finite hull carrier over the procession labels. -/
  hull : FiniteHull label
  /-- The weighted values are the hull volumes (procession construction). -/
  weighted_matches_hull : forall i, procession.value i = hull.volume i
  /-- Procession weights are nonnegative. -/
  weights_nonnegative : forall i, 0 <= procession.weight i
  /-- The normalized procession average is nonnegative (log-volume magnitude). -/
  average_nonneg : 0 <= procession.average
  /-- Exact source obligation: the ambient hull log-volume is the normalized
  procession average. This is the paper normalization/procession comparison,
  not a generic property of the interface. -/
  hull_logVolume_eq_average :
    ambient.logVolume ambient.hull = ENNReal.ofReal procession.average

namespace PaperSignedHull

variable {X : Type u} {label : Type v} [Fintype label]
variable (P : PaperSignedHull X label)

/-- The paper signed hull log-volume -|log(Theta)|: the negative of the actual
ambient normalized hull log-volume. It is not sourceThetaHullLogVolume. -/
def signedHullLogVolume : Real :=
  -(P.ambient.logVolume P.ambient.hull).toReal

/-- The ambient hull log-volume is finite, from the paper compactness/Haar
interface (hull inside the lambda-scaled unit region). -/
theorem ambient_hull_logVolume_lt_top :
    P.ambient.logVolume P.ambient.hull < ⊤ :=
  P.ambient.hull_logVolume_lt_top

/-- The ambient hull log-volume is bounded by the normalized unit-region
log-volume: the compactness/lambda-scaling half of Remark 3.9.5. -/
theorem ambient_hull_logVolume_le_unitRegion :
    P.ambient.logVolume P.ambient.hull <= P.ambient.logVolume P.ambient.unitRegion :=
  le_trans
    (P.ambient.logVolume_mono P.ambient.hull_subset_scaleShift)
    P.ambient.scaleShift_unitRegion_logVolume_le

/-- The signed hull log-volume is nonpositive. -/
theorem signedHullLogVolume_nonpos : P.signedHullLogVolume <= 0 :=
  neg_nonpos.mpr ENNReal.toReal_nonneg

/-- The signed hull log-volume is the negative of the normalized procession
average, under the exact procession-normalization obligation. -/
theorem signedHullLogVolume_eq_neg_average :
    P.signedHullLogVolume = -P.procession.average := by
  unfold signedHullLogVolume
  rw [P.hull_logVolume_eq_average, ENNReal.toReal_ofReal P.average_nonneg]

/-- The finite procession average is bounded by the finite hull volume
(FiniteHull.average_le). -/
theorem procession_average_le_hullVolume :
    P.procession.average <= P.hull.hullVolume :=
  FiniteHull.average_le P.hull P.procession P.weighted_matches_hull
    P.weights_nonnegative

/-- The ambient hull log-volume contains the image-union log-volume: the
paper hull contains the possible images. -/
theorem image_logVolume_le_hull_logVolume :
    P.ambient.logVolume P.ambient.imageSet <=
      P.ambient.logVolume P.ambient.hull :=
  P.ambient.imageSet_logVolume_le_hull

/-- The signed hull log-volume is at most the negative image-union
log-volume whenever the image log-volume is finite; sign conversion of the
hull-containment direction. -/
theorem signedHullLogVolume_le_neg_image_toReal
    (himg : P.ambient.logVolume P.ambient.imageSet < ⊤) :
    P.signedHullLogVolume <=
      -(P.ambient.logVolume P.ambient.imageSet).toReal := by
  unfold signedHullLogVolume
  rw [neg_le_neg_iff]
  exact ENNReal.toReal_mono (ne_top_of_lt P.ambient_hull_logVolume_lt_top)
    P.image_logVolume_le_hull_logVolume

/-- The signed hull log-volume is the negative of a finite nonnegative real
number (the procession average): the paper sign and finiteness content. -/
theorem signedHullLogVolume_eq_neg_of_nonneg_finite :
    exists h : Real, 0 <= h ∧ P.signedHullLogVolume = -h :=
  ⟨P.procession.average, P.average_nonneg, P.signedHullLogVolume_eq_neg_average⟩

end PaperSignedHull

end
end LeanFormal.IUT
