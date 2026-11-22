import tmp.sheaf.xif.paper.S3129IQHullLogVolumeSourceActual
import tmp.sheaf.xif.paper.S3132IQHullRealLogVolumeReadoutActual

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 2000000

noncomputable section

namespace LeanFormal.IUT.XiFPaper.S3132ConcreteSourceNormalizationClosureActual

open MeasureTheory
open LeanFormal.IUT
open LeanFormal.IUT.IUTII.Frobenioid.Example36
open LeanFormal.IUT.IUTII.Frobenioid.Example36.LogShellLattice
open LeanFormal.IUT.LocalFieldLogarithm
open LeanFormal.IUT.LocalFieldIntegralUnits
open LeanFormal.IUT.ConcreteSourceFrobenioidBridge
open LeanFormal.IUT.XiFPaper.S3129IQHullLogVolumeSourceActual
open LeanFormal.IUT.XiFPaper.S3132IQHullRealLogVolumeReadoutActual

local instance sourceNormMeas : MeasurableSpace concreteLogShellField := borel _
local instance sourceNormBorel : BorelSpace concreteLogShellField := ⟨rfl⟩

/-!
# Theta-half residual (2) CLOSED in the concrete Example 3.6 source model

**Component, not a paper object.**  Owner: hull.  Consumers: mainline
FINAL-STATUS/ledger; lattice index.

At the concrete Example 3.6 source place, the actual Haar measure
`sourceHullHaar` is normalized on the actual unit reference (the integral
log-shell) with mass exactly one (`sourceHullHaar_integralLogShell_eq_one`).
This closes the label-level (single-factor, d = 1) normalization residual:

* `sourceVFormLogVolume` is the label-level degree-normalized V-form
  `(1/1)(log mu(S) - log mu(O_hol))` of the actual source hull image;
* `sourceThetaNormalizationFactor := log mu(S) - sourceVFormLogVolume`
  `= log mu(O_hol)` (`sourceThetaNormalizationFactor_eq_log_unitReference`)
  `= log 1 = 0` (`sourceThetaNormalizationFactor_eq_zero`), because the
  unit-reference mass is one;
* hence the raw source reading equals the V-form on the actual image
  (`sourceRawLogVolume_eq_canonical_of_VForm`): the sharper canonical target
  reduces to the **V-form/canonical residual only** — exactly the analogue of
  `MissingVFormCanonicalIdentification` (task-41/61), which remains the single
  Theta-half residual on the concrete source side.

Pages: IUT III, Proposition 3.9, (i), p. 115; Remark 3.9.5, (i), (ii);
IUT III, Corollary 3.12 proof Step (xi-e), corpus:10324-10353; IUT IV,
Proposition 1.4, (i).  No scaling:=1 substitution: the hull is the least
lambda-O hull with lambda ranging over all nonzero scalings.
-/

/-- The label-level degree-normalized V-form of the actual source hull image
(single factor, d = 1): `log mu(S) - log mu(O_hol)`. -/
noncomputable def sourceVFormLogVolume : ℝ :=
  Real.log ((sourceHullHaar sourceQlHullImage).toReal) -
    Real.log ((sourceHullHaar
      (integralLogShell (K := concreteLogShellField) (p := concreteRationalPrime)
        : Set concreteLogShellField)).toReal)

/-- The exact label-level normalization factor of the actual source readout. -/
noncomputable def sourceThetaNormalizationFactor : ℝ :=
  Real.log ((sourceHullHaar sourceQlHullImage).toReal) - sourceVFormLogVolume

/-- The unit-reference Haar mass is one (from the actual normalization of
`sourceHullHaar`). -/
theorem sourceHullHaar_integralLogShell_toReal_eq_one :
    (sourceHullHaar
      (integralLogShell (K := concreteLogShellField) (p := concreteRationalPrime)
        : Set concreteLogShellField)).toReal = 1 := by
  rw [sourceHullHaar_integralLogShell_eq_one]
  simp

/-- **Factor value:** the exact normalization factor is the unit-reference
log-mass. -/
theorem sourceThetaNormalizationFactor_eq_log_unitReference :
    sourceThetaNormalizationFactor =
      Real.log ((sourceHullHaar
        (integralLogShell (K := concreteLogShellField) (p := concreteRationalPrime)
          : Set concreteLogShellField)).toReal) := by
  unfold sourceThetaNormalizationFactor sourceVFormLogVolume
  ring

/-- **Residual (2) CLOSED:** the exact normalization factor vanishes in the
concrete model. -/
theorem sourceThetaNormalizationFactor_eq_zero :
    sourceThetaNormalizationFactor = 0 := by
  rw [sourceThetaNormalizationFactor_eq_log_unitReference,
    sourceHullHaar_integralLogShell_toReal_eq_one]
  simp

/-- The raw source reading in terms of the V-form and the (vanishing) factor. -/
theorem sourceRawLogVolume_eq_VForm_add_factor :
    Real.log ((sourceHullHaar sourceQlHullImage).toReal) =
      sourceVFormLogVolume + sourceThetaNormalizationFactor := by
  unfold sourceThetaNormalizationFactor
  ring

/-- **Reduction to the V-form/canonical residual only:** if the label-level
V-form equals a canonical value, the actual raw source reading equals it. -/
theorem sourceRawLogVolume_eq_canonical_of_VForm (C : ℝ)
    (hV : sourceVFormLogVolume = C) :
    Real.log ((sourceHullHaar sourceQlHullImage).toReal) = C := by
  have hfac := sourceThetaNormalizationFactor_eq_zero
  have hraw := sourceRawLogVolume_eq_VForm_add_factor
  rw [hfac, add_zero] at hraw
  rw [hraw, hV]

/-- Bridge to the packaged real readout `sourceHullRealLogVolume`. -/
theorem sourceRawLogVolume_eq_log_sourceHullRealLogVolume :
    Real.log ((sourceHullHaar sourceQlHullImage).toReal) =
      Real.log sourceHullRealLogVolume := by
  rw [sourceHullRealLogVolume_eq_haar]

/-- **Canonical target from the V-form residual only** (residual (2) closed):
given the label-level V-form equals a canonical value, the packaged source
readout's logarithm equals it. -/
theorem sourceCanonicalReadout_of_VFormResidual (C : ℝ)
    (hV : sourceVFormLogVolume = C) :
    Real.log sourceHullRealLogVolume = C := by
  rw [← sourceRawLogVolume_eq_log_sourceHullRealLogVolume]
  exact sourceRawLogVolume_eq_canonical_of_VForm C hV

/-- **The concrete-model residual-(2) closure record.** -/
structure ConcreteSourceExactFactorClosure : Prop where
  unitReference_mass_one :
    sourceHullHaar
      (integralLogShell (K := concreteLogShellField) (p := concreteRationalPrime)
        : Set concreteLogShellField) = 1
  factor_zero : sourceThetaNormalizationFactor = 0

/-- The concrete-model residual-(2) closure holds. -/
theorem concreteSourceExactFactorClosure_holds : ConcreteSourceExactFactorClosure :=
  { unitReference_mass_one := sourceHullHaar_integralLogShell_eq_one
    factor_zero := sourceThetaNormalizationFactor_eq_zero }

#check sourceVFormLogVolume
#check sourceThetaNormalizationFactor_eq_log_unitReference
#check sourceThetaNormalizationFactor_eq_zero
#check sourceRawLogVolume_eq_canonical_of_VForm
#check sourceCanonicalReadout_of_VFormResidual
#check concreteSourceExactFactorClosure_holds

end LeanFormal.IUT.XiFPaper.S3132ConcreteSourceNormalizationClosureActual

end
