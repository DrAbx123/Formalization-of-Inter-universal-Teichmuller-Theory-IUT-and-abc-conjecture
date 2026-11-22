import tmp.sheaf.xif.paper.S3129IQHullLogVolumeSourceActual
import LeanFormal.IUT.IUTIII.Corollary312.StepXI.HolomorphicHull.SourceHullInterfaceDischarge

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 2000000

noncomputable section

namespace LeanFormal.IUT.XiFPaper.S3132IQHullRealLogVolumeReadoutActual

open MeasureTheory
open LeanFormal.IUT
open LeanFormal.IUT.IUTII.Frobenioid.Example36
open LeanFormal.IUT.IUTII.Frobenioid.Example36.LogShellLattice
open LeanFormal.IUT.XiFPaper.S3129IQHullLogVolumeSourceActual

/-!
# Real-valued H_C readout on the actual concrete-completion carrier

The source-faithful interface `sourceIQHullLogVolume`
(`S3129IQHullLogVolumeSourceActual`) has hull equal to the actual source
image of the `Q_l` log-shell, log-volume equal to the actual normalized Haar
measure of the concrete completion, and finite hull log-volume.  This file
extracts the real-valued readout used by the real consumer chain
(`IQHullLogVolumeInterface.hull_logVolume_realRepresentation`) and records the
actual Haar normalization on the unit reference:

* `sourceHullRealLogVolume` is the `toReal` of the actual hull Haar volume;
* its `ENNReal.ofReal` is exactly the hull log-volume;
* the hull log-volume dominates the image log-volume;
* the unit reference (actual integral log-shell) has Haar mass exactly one;
* the total finiteness of the hull log-volume makes the readout a real number.

Source: IUT III, Corollary 3.12 proof (hull log-volume bound); Remark 3.9.5,
(i), (ii).  No theta-link comparison and no paper-carrier identification is
claimed here.
-/

/-- The actual real-valued H_C readout on the concrete completion: the real
Haar log-volume of the actual source hull. -/
noncomputable def sourceHullRealLogVolume : ℝ :=
  ((sourceIQHullLogVolume).logVolume (sourceIQHullLogVolume).hull).toReal

theorem sourceHullRealLogVolume_eq_haar :
    sourceHullRealLogVolume = (sourceHullHaar sourceQlHullImage).toReal := rfl

theorem sourceHullRealLogVolume_nonneg : 0 ≤ sourceHullRealLogVolume :=
  ENNReal.toReal_nonneg

/-- The hull log-volume is the `ofReal` of the real readout: the actual hull
volume is finite (it is not an `ENNReal` clamp). -/
theorem sourceIQHull_logVolume_eq_ofReal :
    (sourceIQHullLogVolume).logVolume (sourceIQHullLogVolume).hull =
      ENNReal.ofReal sourceHullRealLogVolume :=
  (ENNReal.ofReal_toReal
    (ne_top_of_lt (sourceIQHullLogVolume).hull_logVolume_lt_top)).symm

/-- The image-union log-volume is dominated by the real hull readout. -/
theorem sourceIQHull_image_logVolume_le_ofReal :
    (sourceIQHullLogVolume).logVolume (sourceIQHullLogVolume).imageSet ≤
      ENNReal.ofReal sourceHullRealLogVolume := by
  rw [← sourceIQHull_logVolume_eq_ofReal]
  exact (sourceIQHullLogVolume).imageSet_logVolume_le_hull

/-- The actual hull of the readout is the actual source image of the `Q_l`
log-shell (no enlargement is claimed; the paper holomorphic hull is a separate
obligation). -/
theorem sourceIQHull_hull_eq_sourceQlHullImage :
    (sourceIQHullLogVolume).hull = sourceQlHullImage := rfl

/-- The real hull readout is the `toReal` of a finite `ENNReal`; consequently
the corresponding `ofReal` is finite and the real value is not a limit of an
unbounded family. -/
theorem sourceHullRealLogVolume_lt_top_readout :
    ENNReal.ofReal sourceHullRealLogVolume < ⊤ :=
  ENNReal.ofReal_lt_top

/-- The real-valued hull readout is at least the real part of the image
log-volume (monotonicity of the actual Haar measure through the hull
containment). -/
theorem sourceHullRealLogVolume_ge_image_toReal :
    ((sourceIQHullLogVolume).logVolume (sourceIQHullLogVolume).imageSet).toReal ≤
      sourceHullRealLogVolume := by
  unfold sourceHullRealLogVolume
  exact ENNReal.toReal_mono
    (ne_top_of_lt (sourceIQHullLogVolume).hull_logVolume_lt_top)
    (sourceIQHullLogVolume).imageSet_logVolume_le_hull

/-- The finite real representation of the hull log-volume supplied by
`IQHullLogVolumeInterface.hull_logVolume_realRepresentation`: some real `M`
represents the hull log-volume in `ENNReal` and dominates every lower bound on
the image log-volume. -/
theorem sourceHullRealLogVolume_representation {lowerBound : ENNReal}
    (h : lowerBound ≤
      (sourceIQHullLogVolume).logVolume (sourceIQHullLogVolume).imageSet) :
    ∃ M : ℝ,
      (sourceIQHullLogVolume).logVolume (sourceIQHullLogVolume).hull =
          ENNReal.ofReal M ∧
        lowerBound ≤ ENNReal.ofReal M :=
  (sourceIQHullLogVolume).hull_logVolume_realRepresentation h

#check sourceHullRealLogVolume
#check sourceIQHull_logVolume_eq_ofReal
#check sourceIQHull_hull_eq_sourceQlHullImage

end LeanFormal.IUT.XiFPaper.S3132IQHullRealLogVolumeReadoutActual

end