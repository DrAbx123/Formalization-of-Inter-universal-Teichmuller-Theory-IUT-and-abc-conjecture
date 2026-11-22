import LeanFormal.IUT.IUTIII.Corollary312.StepXI.HolomorphicHull.HaarTranslateInterface
import LeanFormal.IUT.IUTIII.Corollary312.StepXI.HolomorphicHull.PadicLogShellModel
import Mathlib.MeasureTheory.Measure.Haar.OfBasis

/-!
  # The concrete Haar-translate test carrier on the real line (outsider-survey P1)

  The outsider survey's P1 recommendation supplies the Corollary 3.12 hull interface
  `IQHullLogVolumeInterface` from a locally compact group with Haar measure and a
  left-translate scaling instead of the normed-space contraction of the tree's F1
  model.  `HaarTranslateInterface.lean` (R1) realized the schema on an arbitrary
  locally compact group; `PadicLogShellModel.lean` (R2) realized a non-archimedean
  concrete instance on `Q_p`.  This module lands the minimal archimedean concrete
  instance, making the interface inhabited by a genuine measure-theoretic carrier:

  * carrier: the additive group `R` (real line); logVolume: Lebesgue measure
    `volume`, which Mathlib provides as an additive Haar measure
    (`MeasureTheory.Measure.IsAddHaarMeasure (volume : Measure R)`,
    `Mathlib.MeasureTheory.Measure.Haar.OfBasis`);
  * unit region: the compact interval `[-1, 1]`;
  * scaling: the left translation `x |-> 1 + x` (log-domain picture of the
    `lambda . O` regions of IUT III, Remark 3.9.5, (i));
  * hull: the translated unit region, i.e. the interval `[0, 2]`.

  Proved here:

  * `realLineHaarTranslateInterface : IQHullLogVolumeInterface R` -- all fields,
    with `unitRegion_logVolume_lt_top` from Haar finiteness on the compact interval
    (`IsCompact.measure_lt_top`) and `scaleShift_unitRegion_logVolume_le` as an
    equality from additive Haar translation invariance (reusing the generic
    additive lemma `PadicLogShellModel.measure_image_add_translate`);
  * `realLine_scaledUnitRegion_measure_eq`: the scaled unit region carries exactly
    the unit-region log-volume;
  * `realLine_translatedUnitInterval_eq`, `realLine_unitInterval_volume`: the
    concrete set and value data (`[0, 2]`, `volume [-1,1] = 2`);
  * `realLine_hull_measure_lt_top`: hull finiteness (Haar finiteness on the compact
    interval);
  * `nonempty_iqHullLogVolumeInterface_real`: the interface is inhabited on `R`.

  Route comparison (e2/d5), minimality.  d5 (`IQCarrierConcreteModel.lean`,
  `iqCarrierModelInterface`) already inhabits `IQHullLogVolumeInterface Real`, but
  with a synthetic set function `realLineLogVolume` (supremum of real values over
  the set), the identity scaling `x |-> 0 + x`, and the non-compact region
  `Set.Iic 0`; it carries no measure theory.  This instance is the genuine
  Haar-measure carrier (compact interval, nontrivial translation, equality field
  from Haar invariance); the two inhabitants have the same type and coexist without
  conflict -- consumers take their realization as an explicit argument, so no
  consumer is affected.  The e2 spec route (`Cor312CarrierRealizationSpec`) was
  refuted at its assumption layer by the arithmetic no-go recorded in
  `iq-carrier-alignment-20261016.md` and is not a route to this interface; nothing
  of it is touched.  Minimality: the additive real line is the smallest archimedean
  locally compact group here -- unlike `Q_p` (R2) it needs no local
  `MeasurableSpace`/`BorelSpace` installation, and unlike the multiplicative
  `HaarTranslateCarrier` (R1) it needs no transported group structure.

  Reductions (do not overclaim): raw Haar measure is not the normalized log-volume
  of [AbsTopIII] Proposition 5.7 / Corollary 5.10; the scaling is the log-domain
  translation, not the multiplicative field action; the literal carrier
  `IQ(S+-_{j+1}; n,circ D^vdash_{vQ})` is not realized; the value-level no-go at the
  source carrier is untouched.

  Consumer interface: `LeanFormal.IUT.IQHullLogVolumeInterface`
  (`SourceHullCompactnessReduction.lean:52-81`); the instance is a drop-in
  inhabitant of the same consumer type.

  Evidence: `tmp/outsider-survey-iq-carrier-20261016/` logs (`r4p-lean12.log`,
  `r4p-build5.log`, and the probe source `AxiomProbeRealLine.lean`; probe output in the
  landing report); landing report `logs/coordination/iq-hull-haar-logshell-landing-20261016.md`
  (section 13).
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT

noncomputable section

namespace HaarTranslateModel
namespace RealLine

open MeasureTheory

/-- The concrete unit region on the real line: the closed interval [-1, 1]. -/
def unitInterval : Set Real := Set.Icc (-1) 1

/-- The closed interval is compact (the unit-region compactness of the paper's
log-shell shape, realized concretely on the line). -/
theorem unitInterval_isCompact : IsCompact unitInterval := isCompact_Icc

/-- Left translation in image form preserves Lebesgue (additive Haar) measure on the
line; a thin restatement of the generic additive lemma at `volume`. -/
theorem realLine_image_add_translate_volume (a : Real) (s : Set Real) :
    volume ((fun x => a + x) '' s) = volume s :=
  PadicLogShellModel.measure_image_add_translate (volume : Measure Real) a s

/-- **The concrete real-line test carrier.**  An inhabitant of the tree's
`IQHullLogVolumeInterface` on the additive line: compact unit region `[-1, 1]`,
Lebesgue (= additive Haar) measure as log-volume, scaling by the left translation
`x |-> 1 + x`, hull the translated unit region.  The scaling field holds as an
equality (Haar translation invariance), with no contraction hypothesis; the unit
region has finite log-volume by Haar finiteness on compact sets. -/
def realLineHaarTranslateInterface : IQHullLogVolumeInterface Real where
  imageSet := (fun x => (1 : Real) + x) '' unitInterval
  hull := (fun x => (1 : Real) + x) '' unitInterval
  imageSet_subset_hull := subset_rfl
  logVolume := volume
  logVolume_mono := fun hST => measure_mono hST
  unitRegion := unitInterval
  scaleShift := fun x => (1 : Real) + x
  hull_subset_scaleShift := subset_rfl
  unitRegion_logVolume_lt_top := unitInterval_isCompact.measure_lt_top
  scaleShift_unitRegion_logVolume_le :=
    le_of_eq (realLine_image_add_translate_volume 1 unitInterval)

/-- In the real-line Haar-translate instance the scaled unit region carries exactly
the unit-region log-volume (Haar translation invariance; no contraction). -/
theorem realLine_scaledUnitRegion_measure_eq :
    volume ((fun x => (1 : Real) + x) '' unitInterval) = volume unitInterval :=
  realLine_image_add_translate_volume 1 unitInterval

/-- The translated unit region is the concrete interval `[0, 2]`. -/
theorem realLine_translatedUnitInterval_eq :
    (fun x => (1 : Real) + x) '' unitInterval = Set.Icc 0 2 := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨by linarith [hy.1], by linarith [hy.2]⟩
  · intro hx
    exact ⟨x - 1, ⟨by linarith [hx.1], by linarith [hx.2]⟩, by ring⟩

/-- The unit-region log-volume is the concrete value `2`. -/
theorem realLine_unitInterval_volume : volume unitInterval = ENNReal.ofReal 2 := by
  rw [unitInterval, Real.volume_Icc]
  norm_num

/-- Finiteness of the hull log-volume in the real-line instance: the hull carries the
unit-region log-volume by the translation equality, whose concrete value is `2`. -/
theorem realLine_hull_measure_lt_top :
    volume ((fun x => (1 : Real) + x) '' unitInterval) < ⊤ := by
  rw [realLine_scaledUnitRegion_measure_eq, realLine_unitInterval_volume]
  simp

/-- The interface `IQHullLogVolumeInterface` is inhabited on the real line by a
concrete measure-theoretic (Haar) test carrier. -/
theorem nonempty_iqHullLogVolumeInterface_real :
    Nonempty (IQHullLogVolumeInterface Real) :=
  ⟨realLineHaarTranslateInterface⟩

end RealLine
end HaarTranslateModel

end

end LeanFormal.IUT

namespace LeanFormal.IUT.Audit

/-- Audit record for the concrete Haar-translate test carrier on the real line
(outsider-survey P1, archimedean companion of the `Q_p` model). -/
def haarTranslateRealLineInstance : Obligation :=
  { id := "IUT-III.corollary-3.12-haar-translate-real-line-instance"
    source :=
      "IUT III, Corollary 3.12 proof (compactness of the 1,circ U_{j,vQ} and the " ++
        "definition of the log-volume); Remark 3.9.5, (i), (ii) -- concrete " ++
        "archimedean model-level abstraction"
    status := VerificationStatus.testCarrier
    note :=
      "Concrete real-line test carrier of IQHullLogVolumeInterface: unit region the " ++
        "compact interval [-1,1], logVolume the Lebesgue (additive Haar) measure, " ++
        "scaling the left translation x |-> 1 + x, hull the translated unit region " ++
        "[0,2]. The scaling field holds as an equality by additive Haar translation " ++
        "invariance (realLine_image_add_translate_volume, reused from " ++
        "PadicLogShellModel.measure_image_add_translate); unit-region finiteness is " ++
        "Haar finiteness on the compact interval; hull finiteness and nonemptiness of " ++
        "the interface are routed through the tree interface. Route comparison: d5 " ++
        "(iqCarrierModelInterface) inhabits the same type on Real with a synthetic " ++
        "sup-based log-volume and the identity scaling, so no field conflict arises " ++
        "and consumers (explicit realization arguments) are unaffected; the e2 spec " ++
        "route is arithmetically refuted at its assumption layer and untouched. " ++
        "Reductions: raw Haar is not the normalized log-volume of [AbsTopIII] " ++
        "Proposition 5.7 / Corollary 5.10; the literal IQ(S+-_{j+1}; n,circ " ++
        "D^vdash_{vQ}) carrier is not realized."
    dependsOn :=
      [ "IUT-III.corollary-3.12-iq-hull-log-volume-interface",
        "IUT-III.corollary-3.12-haar-translate-interface-model",
        "IUT-III.corollary-3.12-padic-log-shell-model" ] }

end LeanFormal.IUT.Audit
