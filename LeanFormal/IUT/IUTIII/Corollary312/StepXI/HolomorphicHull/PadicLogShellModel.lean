import LeanFormal.IUT.IUTIII.Corollary312.StepXI.HolomorphicHull.SourceHullCompactnessReduction
import Mathlib.NumberTheory.Padics.ProperSpace
import Mathlib.NumberTheory.Padics.PadicIntegers
import Mathlib.MeasureTheory.Constructions.BorelSpace.Metric
import Mathlib.MeasureTheory.Measure.Haar.Basic
import LeanFormal.IUT.Audit.Status

/-!
  # A p-adic log-shell model of the Corollary 3.12 hull interface

  Non-archimedean concrete test carrier for `IQHullLogVolumeInterface` (defined in
  `SourceHullCompactnessReduction.lean:52-87`): the additive group of `Q_p`, the
  compact open unit ball `Z_p = {x : norm x <= 1} = closedBall 0 1` as unit region
  (the role of the log-shell `O_{vQ}`), translation as the scaling action (the
  log-domain picture of the paper's `lambda . O` regions: scaling by `lambda` acts
  additively on log-shells), and the additive Haar measure of `Q_p`, normalized on
  `Z_p`, as `logVolume`.

  Proved here:

  * `measure_image_add_translate`: additive translation invariance in image form for
    any left-invariant measure (the log-domain normalization mechanism);
  * `padicLogShellInterface (lam : Q_p)`: an inhabitant of
    `IQHullLogVolumeInterface Q_[p]` with `unitRegion := Z_p`,
    `scaleShift := fun x => lam + x`, `hull := (fun x => lam + x) '' Z_p`;
    `unitRegion_logVolume_lt_top` is finiteness of Haar measure on the compact set
    `Z_p` (`IsCompact.measure_lt_top`), and `scaleShift_unitRegion_logVolume_le`
    holds as an equality by translation invariance;
  * `padicLogShell_scaledUnitRegion_measure_eq`: the scaled unit region carries
    exactly the unit-region log-volume;
  * `padicLogShell_hull_measure_lt_top`: finiteness of the hull log-volume, routed
    through the tree's own `IQHullLogVolumeInterface.hull_logVolume_lt_top`.

  Local instances: the imported Mathlib fragment provides no `MeasurableSpace` or
  `BorelSpace` instance for `Q_p`; this file installs the Borel structure of the
  norm topology and the measurability of addition (`instMeasurableSpacePadic`,
  `instBorelSpacePadic`).  If upstream Mathlib later provides such instances, these
  two declarations should be revised or removed.

  Reductions (do not overclaim): `logVolume` here is the raw additive Haar measure,
  not the normalized log-volume of [AbsTopIII] Proposition 5.7 / Corollary 5.10;
  the scaling is additive translation (log-domain picture), not the multiplicative
  action on the field; `Q_p` is the base local field (finite extensions and the
  V_bad/V_good generality of the paper are absent); the literal carrier
  `IQ(S+-_{j+1}; n,circ D^vdash_{vQ})` is not realized.

  Consumer interface: `LeanFormal.IUT.IQHullLogVolumeInterface`; consumers are
  unchanged.  Evidence: tmp probe
  `tmp/outsider-survey-iq-carrier-20261016/ProbePadicLogShell.lean` (exit 0,
  standard three principles); landing report
  `logs/coordination/iq-hull-haar-logshell-landing-20261016.md`.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT

universe u

namespace PadicLogShellModel

open MeasureTheory Metric

/-- Additive translation invariance in image form: any left-invariant measure of an
additive group is preserved by translating a set (the log-domain mechanism behind
the paper's `lambda . O` normalization; no measurability of the set is needed). -/
theorem measure_image_add_translate {A : Type u} [AddGroup A] [TopologicalSpace A]
    [MeasurableSpace A] [MeasurableAdd A] (mu : Measure A)
    [MeasureTheory.Measure.IsAddLeftInvariant mu] (g : A) (s : Set A) :
    mu ((fun x => g + x) '' s) = mu s := by
  have h : (fun x => g + x) '' s = (fun x => -g + x) ⁻¹' s := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      change -g + (g + y) ∈ s
      rwa [neg_add_cancel_left]
    · intro hx
      exact ⟨-g + x, hx, by
        change g + (-g + x) = x
        rw [add_neg_cancel_left]⟩
  rw [h, measure_preimage_add]

variable (p : ℕ) [Fact p.Prime]

/-- Borel measurable structure of the norm topology of `Q_p` (probe-local
installation; see the module docstring). -/
noncomputable instance instMeasurableSpacePadic : MeasurableSpace ℚ_[p] := borel ℚ_[p]

/-- `Q_p` carries the Borel structure of its norm topology. -/
instance instBorelSpacePadic : BorelSpace ℚ_[p] := ⟨rfl⟩

/-- The p-adic unit ball `Z_p = {x : norm x <= 1}`, a compact set with nonempty
interior: the compact open unit region (log-shell role). -/
noncomputable def padicUnitCompacts : TopologicalSpace.PositiveCompacts ℚ_[p] where
  carrier := closedBall (0 : ℚ_[p]) 1
  isCompact' := isCompact_closedBall (0 : ℚ_[p]) 1
  interior_nonempty' :=
    ⟨0, mem_interior_iff_mem_nhds.mpr (closedBall_mem_nhds (0 : ℚ_[p]) zero_lt_one)⟩

/-- The additive Haar measure of `Q_p`, normalized so that the unit ball `Z_p` has
mass one.  (`abbrev`, so that instance search unfolds the normalization.) -/
noncomputable abbrev padicLogVolume : Measure ℚ_[p] :=
  MeasureTheory.Measure.addHaarMeasure (padicUnitCompacts p)

/-- The p-adic log-shell model of the tree interface: unit region `Z_p`, scaling by
translation with `lam`, and the hull equal to the translated unit region. -/
noncomputable def padicLogShellInterface (lam : ℚ_[p]) :
    IQHullLogVolumeInterface ℚ_[p] where
  imageSet := (fun x => lam + x) '' closedBall (0 : ℚ_[p]) 1
  hull := (fun x => lam + x) '' closedBall (0 : ℚ_[p]) 1
  imageSet_subset_hull := subset_rfl
  logVolume := padicLogVolume p
  logVolume_mono := fun hST => measure_mono hST
  unitRegion := closedBall (0 : ℚ_[p]) 1
  scaleShift := fun x => lam + x
  hull_subset_scaleShift := subset_rfl
  unitRegion_logVolume_lt_top := (padicUnitCompacts p).isCompact.measure_lt_top
  scaleShift_unitRegion_logVolume_le :=
    le_of_eq (measure_image_add_translate (padicLogVolume p) lam (closedBall (0 : ℚ_[p]) 1))

/-- In the p-adic log-shell model the scaled unit region carries exactly the unit
region log-volume: Haar translation invariance, no contraction hypothesis. -/
theorem padicLogShell_scaledUnitRegion_measure_eq (lam : ℚ_[p]) :
    padicLogVolume p ((fun x => lam + x) '' closedBall (0 : ℚ_[p]) 1) =
      padicLogVolume p (closedBall (0 : ℚ_[p]) 1) :=
  measure_image_add_translate (padicLogVolume p) lam (closedBall (0 : ℚ_[p]) 1)

/-- Finiteness of the hull log-volume in the p-adic log-shell model, through the
existing tree interface (reuse of `IQHullLogVolumeInterface.hull_logVolume_lt_top`). -/
theorem padicLogShell_hull_measure_lt_top (lam : ℚ_[p]) :
    padicLogVolume p ((fun x => lam + x) '' closedBall (0 : ℚ_[p]) 1) < ⊤ :=
  (padicLogShellInterface p lam).hull_logVolume_lt_top

end PadicLogShellModel

end LeanFormal.IUT

namespace LeanFormal.IUT.Audit

/-- Audit record for the p-adic log-shell test-carrier model of the Corollary 3.12
hull/log-volume interface. -/
def padicLogShellModel : Obligation :=
  { id := "IUT-III.corollary-3.12-padic-log-shell-model"
    source :=
      "IUT III, Corollary 3.12 proof (compactness of the 1,circ U_{j,vQ} and the " ++
        "definition of the log-volume); Remark 3.9.5, (i), (ii) -- non-archimedean " ++
        "model-level abstraction"
    status := VerificationStatus.testCarrier
    note :=
      "Non-archimedean concrete test-carrier model of IQHullLogVolumeInterface on " ++
        "Q_p: unit region the compact open unit ball Z_p, logVolume the additive " ++
        "Haar measure normalized on Z_p, scaling by translation, hull the translated " ++
        "unit region. The scaling field holds as an equality by translation " ++
        "invariance (measure_image_add_translate); finiteness of the unit-region " ++
        "log-volume is Haar finiteness on the compact set Z_p. Reductions: raw Haar " ++
        "is not the normalized log-volume of [AbsTopIII] Proposition 5.7 / Corollary " ++
        "5.10; the scaling is the log-domain translation, not the multiplicative " ++
        "field action; finite extensions and general places are absent. NOT proved: " ++
        "realization for the literal IQ(S+-_{j+1}; n,circ D^vdash_{vQ}) carrier."
    dependsOn :=
      [ "IUT-III.corollary-3.12-iq-hull-log-volume-interface" ] }

end LeanFormal.IUT.Audit
