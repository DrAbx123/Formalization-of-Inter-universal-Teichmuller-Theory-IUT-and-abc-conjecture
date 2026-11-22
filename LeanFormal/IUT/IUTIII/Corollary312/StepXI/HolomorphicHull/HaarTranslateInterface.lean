import LeanFormal.IUT.IUTIII.Corollary312.StepXI.HolomorphicHull.SourceHullCompactnessReduction
import Mathlib.MeasureTheory.Measure.Haar.Basic
import Mathlib.MeasureTheory.Group.Action
import LeanFormal.IUT.Audit.Status

/-!
  # The Haar-translate model of the Corollary 3.12 hull interface

  The tree's F1 consistency model of `IQHullLogVolumeInterface`
  (`SourceHullInterfaceDischarge.haarContractionInterface`) uses a finite-dimensional
  real normed space, the closed unit ball, and a *contraction* `x |-> c . x` with
  `0 < c <= 1` for the scaling field.  In a normed space the multiplicative homothety
  is not a translation, so the Haar invariance of the paper's `lambda . O` regions
  (IUT III, Remark 3.9.5, (i), (ii)) can only be expressed there by monotonicity of
  the measure under a contracting image.

  This module provides the paper-faithful shape instead: on any locally compact group
  `G`, with a left-invariant Haar measure `mu`, a compact unit region `K` (the role of
  the log-shell `O_{vQ}`), a scaling element `lam : G` acting by left multiplication
  (the role of `lambda . O`, all components of `lambda` nonzero), and a hull region
  contained in the scaled unit region, the tree interface `IQHullLogVolumeInterface G`
  is realized with

  * `logVolume := mu`,
  * `scaleShift := fun x => lam * x`,
  * `unitRegion := K`,
  * `scaleShift_unitRegion_logVolume_le` obtained from *exact* left translation
    invariance of `mu` (`measure_image_mul_translate`), not from a contraction.

  Consequences proved here:

  * `HaarTranslateCarrier.scaledUnitRegion_measure_eq`: the scaled unit region carries
    exactly the log-volume of the unit region;
  * `HaarTranslateCarrier.toIQHullLogVolumeInterface_scaledUnitRegion_eq`: the same
    equality witnessed inside the interface instance itself;
  * `HaarTranslateCarrier.hull_measure_lt_top`: finiteness of the hull log-volume,
    routed through the tree's own `IQHullLogVolumeInterface.hull_logVolume_lt_top`.

  Reductions (do not overclaim): this is a model of the interface's analytic shape,
  not a realization of the literal carrier `IQ(S+-_{j+1}; n,circ D^vdash_{vQ})`;
  the compactness of the unit region and the containment `hull subseteq lambda . O`
  are data fields, not theorems about the source carrier; the value-level
  obstruction `not_exists_scaledRegionImage_unitDegreeBounded_of_degreeFaithful`
  (`SourceHullInterfaceDischarge.lean`) is untouched.

  Consumer interface: `LeanFormal.IUT.IQHullLogVolumeInterface`
  (`SourceHullCompactnessReduction.lean:52-87`); the canonical consumer entry is
  `IQHullLogVolumeInterface.hull_logVolume_lt_top` (:95).  Consumers are unchanged:
  the produced inhabitant has the same type as any other realization.

  Evidence: tmp probe `tmp/outsider-survey-iq-carrier-20261016/ProbeHaarTranslateLCG.lean`
  (exit 0, standard three principles); landing report
  `logs/coordination/iq-hull-haar-logshell-landing-20261016.md`.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT

universe u

namespace HaarTranslateModel

open MeasureTheory

/-- The paper-shaped data: a compact unit region `K` (role: the log-shell region
`O_{vQ}`), a scaling element `lam` acting on `K` by left multiplication (role: the
`lambda . O` regions of IUT III Remark 3.9.5, (i)), and a hull region contained in the
scaled unit region (role: `phi(n,circ U_{vQ}) subseteq lambda . O`). -/
structure HaarTranslateCarrier (G : Type u) [Group G] [TopologicalSpace G] where
  /-- The unit region (role: the log-shell region `O`). -/
  unitRegion : Set G
  /-- Compactness of the unit region (role: compactness of the `1,circ U` regions and
  of the log-shell). -/
  unitRegion_isCompact : IsCompact unitRegion
  /-- The scaling element (role: `lambda` with all components nonzero). -/
  lam : G
  /-- The hull region (role: `phi(n,circ U_{vQ})`). -/
  hull : Set G
  /-- The paper's containment `hull subseteq lambda . O`. -/
  hull_subset : hull ⊆ (fun x => lam * x) '' unitRegion

variable {G : Type u} [Group G] [TopologicalSpace G] [MeasurableSpace G] [MeasurableMul G]

/-- Left translation in image form preserves any left-invariant measure (no
measurability of the translated set is needed). -/
theorem measure_image_mul_translate (mu : Measure G)
    [MeasureTheory.Measure.IsMulLeftInvariant mu] (g : G) (s : Set G) :
    mu ((fun x => g * x) '' s) = mu s := by
  have h : (fun x => g * x) '' s = (fun x => g⁻¹ * x) ⁻¹' s := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      change g⁻¹ * (g * y) ∈ s
      rwa [inv_mul_cancel_left]
    · intro hx
      exact ⟨g⁻¹ * x, hx, by
        change g * (g⁻¹ * x) = x
        rw [mul_inv_cancel_left]⟩
  rw [h, measure_preimage_mul]

/-- Haar-translate realization of the tree's `IQHullLogVolumeInterface` on a locally
compact group: `logVolume` is Haar measure, the scaling is left translation by `lam`,
and the non-monotone field is exactly left invariance of Haar measure. -/
noncomputable def HaarTranslateCarrier.toIQHullLogVolumeInterface (mu : Measure G)
    [MeasureTheory.Measure.IsHaarMeasure mu] (gamma : HaarTranslateCarrier G) :
    IQHullLogVolumeInterface G where
  imageSet := gamma.hull
  hull := gamma.hull
  imageSet_subset_hull := subset_rfl
  logVolume := mu
  logVolume_mono := fun hST => measure_mono hST
  unitRegion := gamma.unitRegion
  scaleShift := fun x => gamma.lam * x
  hull_subset_scaleShift := gamma.hull_subset
  unitRegion_logVolume_lt_top := gamma.unitRegion_isCompact.measure_lt_top
  scaleShift_unitRegion_logVolume_le :=
    le_of_eq (measure_image_mul_translate mu gamma.lam gamma.unitRegion)

/-- In the Haar-translate model the scaled unit region carries *exactly* the
log-volume of the unit region (Haar translation invariance; no contraction). -/
theorem HaarTranslateCarrier.scaledUnitRegion_measure_eq (mu : Measure G)
    [MeasureTheory.Measure.IsHaarMeasure mu] (gamma : HaarTranslateCarrier G) :
    mu ((fun x => gamma.lam * x) '' gamma.unitRegion) = mu gamma.unitRegion :=
  measure_image_mul_translate mu gamma.lam gamma.unitRegion

/-- The strengthening of the scaling field witnessed inside the interface instance
itself: the instance's own `scaleShift`-image of its own `unitRegion` has exactly the
instance's `logVolume` of the unit region. -/
theorem HaarTranslateCarrier.toIQHullLogVolumeInterface_scaledUnitRegion_eq
    (mu : Measure G) [MeasureTheory.Measure.IsHaarMeasure mu]
    (gamma : HaarTranslateCarrier G) :
    (gamma.toIQHullLogVolumeInterface mu).logVolume
        ((gamma.toIQHullLogVolumeInterface mu).scaleShift ''
          (gamma.toIQHullLogVolumeInterface mu).unitRegion) =
      (gamma.toIQHullLogVolumeInterface mu).logVolume
        (gamma.toIQHullLogVolumeInterface mu).unitRegion := by
  change mu ((fun x => gamma.lam * x) '' gamma.unitRegion) = mu gamma.unitRegion
  exact measure_image_mul_translate mu gamma.lam gamma.unitRegion

/-- Finiteness of the hull log-volume in the Haar-translate model, through the
existing tree interface (reuse of `IQHullLogVolumeInterface.hull_logVolume_lt_top`). -/
theorem HaarTranslateCarrier.hull_measure_lt_top (mu : Measure G)
    [MeasureTheory.Measure.IsHaarMeasure mu] (gamma : HaarTranslateCarrier G) :
    mu gamma.hull < ⊤ :=
  (gamma.toIQHullLogVolumeInterface mu).hull_logVolume_lt_top

end HaarTranslateModel

end LeanFormal.IUT

namespace LeanFormal.IUT.Audit

/-- Audit record for the Haar-translate test-carrier model of the Corollary 3.12
hull/log-volume interface. -/
def haarTranslateModel : Obligation :=
  { id := "IUT-III.corollary-3.12-haar-translate-interface-model"
    source :=
      "IUT III, Corollary 3.12 proof (compactness of the 1,circ U_{j,vQ} and the " ++
        "definition of the log-volume); Remark 3.9.5, (i), (ii) -- model-level abstraction"
    status := VerificationStatus.testCarrier
    note :=
      "Concrete test-carrier model of IQHullLogVolumeInterface on a locally compact " ++
        "group: compact unit region, Haar measure as logVolume, scaling by left " ++
        "translation, hull contained in the scaled unit region. The scaling field " ++
        "holds as an equality by Haar left invariance (measure_image_mul_translate), " ++
        "with no contraction hypothesis; F1 (haarContractionInterface) remains the " ++
        "normed-space consistency model. NOT proved: realization for the actual " ++
        "IQ(S+-_{j+1}; n,circ D^vdash_{vQ}) carrier; the unit-region compactness and " ++
        "the hull containment are data fields."
    dependsOn :=
      [ "IUT-III.corollary-3.12-iq-hull-log-volume-interface" ] }

end LeanFormal.IUT.Audit
