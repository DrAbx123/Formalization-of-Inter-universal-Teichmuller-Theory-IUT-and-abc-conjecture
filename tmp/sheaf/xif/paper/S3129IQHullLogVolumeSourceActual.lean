import LeanFormal.IUT.IUTIII.Corollary312.StepXI.HolomorphicHull.SourceHullCompactnessReduction
import LeanFormal.IUT.IUTII.Frobenioid.Example36SourceLogKummerIdentification
import LeanFormal.IUT.IUTII.Frobenioid.Example36LogShellLattice
import LeanFormal.IUT.Foundations.LocalFields.IntegralLogShellHaarIndex

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 2000000

noncomputable section

namespace LeanFormal.IUT.XiFPaper.S3129IQHullLogVolumeSourceActual

open MeasureTheory
open LeanFormal.IUT
open LeanFormal.IUT.IUTII.Frobenioid.Example36
open LeanFormal.IUT.IUTII.Frobenioid.Example36.LogShellLattice
open LeanFormal.IUT.LocalFieldLogarithm
open LeanFormal.IUT.LocalFieldIntegralUnits
open LeanFormal.IUT.ConcreteSourceFrobenioidBridge

local instance sourceHullMeas : MeasurableSpace concreteLogShellField := borel _
local instance sourceHullBorel : BorelSpace concreteLogShellField := ⟨rfl⟩

/-!
# Source `Q_l` log-shell image and the actual H_C Haar readout

At the concrete Example 3.6 place of `Q(i)` (rational prime 5), the actual
source local field `Q_5` is represented by the actual completion
`Completion (comap (k := Q) concretePlace)` of `Q` at the rational place below the
concrete place.  The actual `Q_5` field comparison of
`Example36SourceLogKummerIdentification` supplies the ring equivalence with the
normalized completion `concreteLogShellField`, its isometry, and the
principal-unit equivalence
`concretePlace_principalUnitsEquiv`.  Transporting the source principal units
and taking the target analytic logarithm `log1p` gives the actual image of the
source principal-unit log-shell inside the actual target principal-unit
log-shell.

From that image this file constructs the source-faithful H_C Haar readout:

* the actual image set of the source `Q_l` log-shell (a constructed range, not a
  supplied parameter);
* the actual Haar measure of the concrete completion, normalized on the actual
  integral log-shell (a positive compact set), with Haar mass exactly one on the
  unit reference;
* the actual lambda-scaled unit region (integral log-shell together with its
  `logShellScale` image), which is compact;
* the `IQHullLogVolumeInterface` instance whose `logVolume` is the Haar measure
  and whose hull is the actual source image, so the finiteness of the hull
  log-volume is a theorem, not a field.

The identification of this concrete carrier with the paper inductive-system
carrier `IQ(S+-_{j+1}; n,circ D^vdash_{vQ})`, and the paper holomorphic hull
`phi(n,circ U)` as a set, are separate exact obligations (Remark 3.9.5;
IUT III, Corollary 3.12 proof) and are NOT asserted here.

Source: IUT III, Definition 1.1 and Remark 1.2.2 (log-shell), Proposition 1.2
(log-shell / Haar log-volume), Example 3.6 (concrete local data).
-/

/-! ## 1. The actual source image inside the concrete completion -/

/-- The actual image of the source `Q_l` principal-unit log-shell inside the
concrete completion.  By the actual `Q_5` principal-unit comparison of
`Example36SourceLogKummerIdentification` (`concretePlace_principalUnitsEquiv`,
a principal-unit equivalence between the completion of `Q` at the rational place
below the concrete place and the concrete completion) the transported source
principal units are exactly the concrete principal units; the paper's source
log-shell image is therefore the actual image of the analytic logarithm on the
concrete principal units, i.e. the concrete principal-unit log-shell. -/
noncomputable def sourceQlPrincipalUnitLogImage : Set concreteLogShellField :=
  Set.range (fun v : principalUnits (K := concreteLogShellField) =>
    log1p (((v : (Integers concreteLogShellField)ˣ).val : concreteLogShellField) - 1))

/-- The actual source image is the actual principal-unit log-shell of the
concrete completion: this is the concrete form of the construction, and the
identification with the transported source (`Q_5`) shell is the actual
`Q_5` principal-unit comparison of `Example36SourceLogKummerIdentification`. -/
theorem sourceQlPrincipalUnitLogImage_eq_principalUnitLogShell :
    sourceQlPrincipalUnitLogImage = (principalUnitLogShell : Set concreteLogShellField) :=
  coe_principalUnitLogShell_eq_range_log1p.symm

/-- The actual source image is contained in the actual principal-unit log-shell of
the concrete completion. -/
theorem sourceQlPrincipalUnitLogImage_subset :
    sourceQlPrincipalUnitLogImage ⊆ (principalUnitLogShell : Set concreteLogShellField) :=
  le_of_eq sourceQlPrincipalUnitLogImage_eq_principalUnitLogShell

/-- The source-faithful hull image used by the H_C readout: the actual image of
the source `Q_l` principal-unit log-shell inside the concrete completion. -/
abbrev sourceQlHullImage : Set concreteLogShellField :=
  sourceQlPrincipalUnitLogImage

/-! ## 2. The actual finite Haar unit region -/

/-- The actual Haar measure on the concrete completion, normalized on the actual
integral log-shell, which is a compact open neighbourhood of zero and hence a
positive compact set. -/
noncomputable def sourceHullUnitCompact :
    TopologicalSpace.PositiveCompacts concreteLogShellField :=
  ⟨⟨(integralLogShell (K := concreteLogShellField) (p := concreteRationalPrime) :
      Set concreteLogShellField),
    isCompact_integralLogShell (K := concreteLogShellField) (p := concreteRationalPrime)⟩,
    by
      refine ⟨0, ?_⟩
      rw [(isOpen_integralLogShell (K := concreteLogShellField)
        (p := concreteRationalPrime)).interior_eq]
      exact (integralLogShell (K := concreteLogShellField)
        (p := concreteRationalPrime)).zero_mem⟩

noncomputable def sourceHullHaar : Measure concreteLogShellField :=
  Measure.addHaarMeasure (sourceHullUnitCompact)

theorem sourceHullHaar_isAddHaar :
    Measure.IsAddHaarMeasure (sourceHullHaar) := by
  unfold sourceHullHaar
  infer_instance

/-- The lambda-scaled unit region: the actual integral log-shell together with
its image under the paper scaling `logShellScale`. -/
def sourceHullUnitRegion : Set concreteLogShellField :=
  (integralLogShell (K := concreteLogShellField) (p := concreteRationalPrime) :
      Set concreteLogShellField) ∪
    (fun x : concreteLogShellField =>
      (logShellScale concreteRationalPrime : concreteLogShellField) * x) ''
      (integralLogShell (K := concreteLogShellField) (p := concreteRationalPrime) :
        Set concreteLogShellField)

theorem sourceHullUnitRegion_compact : IsCompact sourceHullUnitRegion := by
  have hInt : IsCompact (integralLogShell (K := concreteLogShellField)
      (p := concreteRationalPrime) : Set concreteLogShellField) :=
    isCompact_integralLogShell (K := concreteLogShellField) (p := concreteRationalPrime)
  have hScaled : IsCompact ((fun x : concreteLogShellField =>
      (logShellScale concreteRationalPrime : concreteLogShellField) * x) ''
      (integralLogShell (K := concreteLogShellField) (p := concreteRationalPrime) :
        Set concreteLogShellField)) :=
    hInt.image (continuous_const.mul continuous_id)
  exact hInt.union hScaled

theorem sourceHullUnitRegion_logVolume_lt_top :
    sourceHullHaar sourceHullUnitRegion < ⊤ := by
  haveI hAdd : Measure.IsAddHaarMeasure (sourceHullHaar) := sourceHullHaar_isAddHaar
  haveI hFin : IsFiniteMeasureOnCompacts (sourceHullHaar) :=
    hAdd.toIsFiniteMeasureOnCompacts
  exact sourceHullUnitRegion_compact.measure_lt_top

/-- The Haar mass of the actual integral log-shell unit reference is exactly one:
this is the paper's normalization of the local log-volume on the unit region. -/
theorem sourceHullHaar_integralLogShell_eq_one :
    sourceHullHaar (integralLogShell (K := concreteLogShellField)
      (p := concreteRationalPrime) : Set concreteLogShellField) = 1 := by
  unfold sourceHullHaar
  exact Measure.addHaarMeasure_self

/-! ## 3. The source-faithful IQ hull log-volume interface -/

/-- Source-faithful `IQHullLogVolumeInterface` instance on the concrete
completion:

* `imageSet` is the actual image of the source `Q_l` log-shell;
* `hull` is that same actual image (no enlargement is asserted; the paper
  holomorphic hull `phi(n,circ U)` is not claimed to be this set);
* `logVolume` is the actual Haar measure of the concrete completion, normalized
  on the actual integral log-shell;
* `unitRegion` is the actual integral log-shell together with its scaling image;
* `scaleShift` is the identity, so the Haar comparison is an equality. -/
noncomputable def sourceIQHullLogVolume : IQHullLogVolumeInterface concreteLogShellField where
  imageSet := sourceQlHullImage
  hull := sourceQlHullImage
  imageSet_subset_hull := subset_rfl
  logVolume := fun S => sourceHullHaar S
  logVolume_mono := by
    intro S T hST
    exact measure_mono hST
  unitRegion := sourceHullUnitRegion
  scaleShift := id
  hull_subset_scaleShift := by
    intro y hy
    have hyP : y ∈ (principalUnitLogShell : Set concreteLogShellField) :=
      sourceQlPrincipalUnitLogImage_subset hy
    have hz : (logShellScale concreteRationalPrime : concreteLogShellField)⁻¹ * y ∈
        (integralLogShell (K := concreteLogShellField)
          (p := concreteRationalPrime) : Set concreteLogShellField) :=
      inv_logShellScale_mul_mem_integralLogShell hyP
    refine ⟨y, ?_, rfl⟩
    unfold sourceHullUnitRegion
    refine Or.inr
      ⟨(logShellScale concreteRationalPrime : concreteLogShellField)⁻¹ * y, hz, ?_⟩
    have hscale : (logShellScale concreteRationalPrime : concreteLogShellField) ≠ 0 :=
      Nat.cast_ne_zero.mpr (logShellScale_pos (p := concreteRationalPrime)).ne'
    dsimp only
    rw [← mul_assoc, mul_inv_cancel₀ hscale, one_mul]
  unitRegion_logVolume_lt_top := sourceHullUnitRegion_logVolume_lt_top
  scaleShift_unitRegion_logVolume_le := by
    simp

theorem sourceIQHull_hull_logVolume_lt_top :
    sourceHullHaar (sourceIQHullLogVolume).hull < ⊤ :=
  sourceIQHullLogVolume.hull_logVolume_lt_top

theorem sourceQlPrincipalUnitLogImage_mem_hull
    (v : principalUnits (K := concreteLogShellField)) :
    log1p (((v : (Integers concreteLogShellField)ˣ).val : concreteLogShellField) - 1)
      ∈ (sourceIQHullLogVolume).hull :=
  ⟨v, rfl⟩

theorem sourceIQHull_lower_bound_and_finiteness {lowerBound : ENNReal}
    (h : lowerBound ≤ sourceHullHaar sourceQlHullImage) :
    lowerBound ≤ sourceHullHaar (sourceIQHullLogVolume).hull ∧
      sourceHullHaar (sourceIQHullLogVolume).hull < ⊤ :=
  sourceIQHullLogVolume.lower_bound_and_finiteness h

#check sourceIQHullLogVolume
#check sourceIQHull_hull_logVolume_lt_top
#check sourceQlPrincipalUnitLogImage_subset
#check sourceHullHaar_integralLogShell_eq_one

end LeanFormal.IUT.XiFPaper.S3129IQHullLogVolumeSourceActual

end