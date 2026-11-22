import LeanFormal.IUT.IUTIII.Corollary312.StepXI.HolomorphicHull.HaarTranslateRealLineInstance
import LeanFormal.IUT.IUTIII.Corollary312.StepXI.HolomorphicHull.IQHullValueCarrierWiring

/-!
  # Drop-in consumption of the real-line Haar-translate carrier (outsider survey P1, continued)

  The P1 instance `realLineHaarTranslateInterface : IQHullLogVolumeInterface Real`
  (`HaarTranslateRealLineInstance.lean`) is consumed here in the exact consumption
  form of the Corollary 3.12 pipeline landed by Card-HULLREAL:

  * the generic N14 slot adapter
    `IQHullValueCarrierWiring.iqHullPointWiringCertificate` is instantiated at the
    real-line instance with the carrier point `1 = 1 + 0` of the image union; all
    four certificate slots are discharged by proved lemmas (`q = -1`,
    `theta = iqHullRealVolume`, `q < 0`, image and hull bounds);
  * the upper slot computes to the concrete value `2`
    (`realLineHullRealVolume_eq_two`);
  * the link evidence and the composed `Cor312Conclusion` wrapper are instantiated
    (`realLinePointWiringCor312Conclusion`);
  * the consumer-side finiteness theorem fires on the instance
    (`realLine_hull_logVolume_lt_top_via_interface`).

  The [AbsTopIII] normalization step is realized on the same carrier
  (`normalizedRealLineVolume`): rescaling the additive Haar measure by
  `(volume [-1, 1])^{-1}` gives an additive Haar measure whose unit region carries
  mass exactly `1` -- the test-carrier form of the normalization `mu_k(O_k) = 1` of
  Proposition 5.7, (i), (a), (3) -- and the normalized measure inhabits the consumer
  interface as well (`realLineNormalizedHaarTranslateInterface`).

  Reductions (do not overclaim): raw Haar measure is not the normalized log-volume
  of [AbsTopIII] Proposition 5.7 / Corollary 5.10; their carrier is a local field
  with multiplicative log-shell structure, whereas this is the additive line with
  the log-domain translation.  The multiplicative scaling law (Proposition 5.7,
  (i), (b)) is represented only by additive translation invariance; the literal
  carrier `IQ(S+-_{j+1}; n,circ D^vdash_{vQ})` is not realized; the value-level
  boundary at `I.ThetaPilotPoint` is untouched.

  Evidence: `tmp/outsider-survey-iq-carrier-20261016/` logs and the landing report
  `logs/coordination/iq-hull-haar-logshell-landing-20261016.md`, section 14.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT.HaarTranslateModel.RealLine

noncomputable section

open MeasureTheory

/-! ## 1. Concrete slot values of the real-line instance -/

/-- The hull of the real-line instance (the translated unit region `[0, 2]`) carries
exactly the concrete unit-interval log-volume. -/
theorem realLine_hull_volume_eq_ofReal_two :
    volume ((fun x => (1 : Real) + x) '' unitInterval) = ENNReal.ofReal 2 := by
  rw [realLine_scaledUnitRegion_measure_eq, realLine_unitInterval_volume]

/-- The upper-bound slot at `theta = 2`, in interface form. -/
theorem realLine_hull_volume_le_ofReal_two :
    volume ((fun x => (1 : Real) + x) '' unitInterval) ≤ ENNReal.ofReal 2 :=
  le_of_eq realLine_hull_volume_eq_ofReal_two

/-- The real hull log-volume consumed by the certificate is the concrete value `2`. -/
theorem realLineHullRealVolume_eq_two :
    iqHullRealVolume realLineHaarTranslateInterface = 2 := by
  change (volume ((fun x => (1 : Real) + x) '' unitInterval)).toReal = 2
  rw [realLine_hull_volume_eq_ofReal_two,
    ENNReal.toReal_ofReal (by norm_num : (0 : Real) ≤ 2)]

/-- Interface-level finiteness of the hull log-volume fires on the real-line
instance: the consumer-side theorem, not only the measure computation. -/
theorem realLine_hull_logVolume_lt_top_via_interface :
    realLineHaarTranslateInterface.logVolume realLineHaarTranslateInterface.hull < ⊤ :=
  realLineHaarTranslateInterface.hull_logVolume_lt_top

/-! ## 2. Drop-in consumption in the N14 certificate pipeline -/

/-- The carrier point `1 = 1 + 0` of the image union of the real-line instance. -/
theorem realLine_one_mem_imageSet :
    (1 : Real) ∈ realLineHaarTranslateInterface.imageSet :=
  ⟨0, ⟨by norm_num, by norm_num⟩, by norm_num⟩

/-- **Drop-in certificate.**  The P1 inhabitant, consumed by the N14 pipeline as any
other realization: certificate with `q = -1` and `theta = iqHullRealVolume`, all
four slots discharged by proof. -/
def realLinePointWiringCertificate : StepXIFiniteCertificate Unit :=
  IQHullValueCarrierWiring.iqHullPointWiringCertificate realLineHaarTranslateInterface
    (1 : Real) realLine_one_mem_imageSet

/-- The certificate lower slot carries `q = -1`. -/
theorem realLinePointWiringCertificate_qSigned :
    realLinePointWiringCertificate.qSigned = -1 :=
  IQHullValueCarrierWiring.iqHullPointWiringCertificate_qSigned
    realLineHaarTranslateInterface (1 : Real) realLine_one_mem_imageSet

/-- The certificate upper slot computes to the concrete value `2`. -/
theorem realLinePointWiringCertificate_thetaSigned :
    realLinePointWiringCertificate.thetaSigned = 2 :=
  (IQHullValueCarrierWiring.iqHullPointWiringCertificate_thetaSigned
    realLineHaarTranslateInterface (1 : Real) realLine_one_mem_imageSet).trans
    realLineHullRealVolume_eq_two

/-- The link evidence of the real-line certificate; the IPL/SHE/APT propositions
and their evidence remain supplied inputs, exactly as in the existing bridge. -/
def realLinePointWiringLinkEvidence (ipl she apt : Prop) (hipl : ipl) (hshe : she)
    (hapt : apt) :
    FiniteStepXILinkEvidence realLinePointWiringCertificate :=
  IQHullValueCarrierWiring.iqHullPointWiringLinkEvidence realLineHaarTranslateInterface
    (1 : Real) realLine_one_mem_imageSet ipl she apt hipl hshe hapt

/-- **Drop-in consumer conclusion.**  The composed Corollary 3.12 conclusion at the
real-line instance. -/
theorem realLinePointWiringCor312Conclusion (ipl she apt : Prop) (hipl : ipl)
    (hshe : she) (hapt : apt) :
    Cor312Conclusion
      (realLinePointWiringCertificate.toContract
        (realLinePointWiringLinkEvidence ipl she apt hipl hshe hapt)) :=
  IQHullValueCarrierWiring.iqHullPointWiringCor312Conclusion
    realLineHaarTranslateInterface (1 : Real) realLine_one_mem_imageSet
    ipl she apt hipl hshe hapt

/-! ## 3. The [AbsTopIII] normalization step on the same carrier -/

/-- The normalized real-line log-volume: the additive Haar measure rescaled so that
the unit region `[-1, 1]` carries mass exactly `1` -- the test-carrier form of the
normalization `mu_k(O_k) = 1` of [AbsTopIII] Proposition 5.7, (i), (a), (3). -/
def normalizedRealLineVolume : Measure Real :=
  (ENNReal.ofReal 2)⁻¹ • volume

/-- The normalized log-volume gives the unit region mass exactly `1`. -/
theorem normalizedRealLineVolume_unitInterval :
    normalizedRealLineVolume unitInterval = 1 := by
  rw [normalizedRealLineVolume, Measure.smul_apply, realLine_unitInterval_volume]
  simpa using ENNReal.inv_mul_cancel
    (ne_of_gt (ENNReal.ofReal_pos.mpr (by norm_num : (0 : Real) < 2)))
    ENNReal.ofReal_ne_top

/-- The normalized log-volume gives the translated unit region mass exactly `1`:
the scaling invariance stays an exact equality after normalization (test-carrier
form of the scaling law of [AbsTopIII] Proposition 5.7, (i), (b)). -/
theorem normalizedRealLineVolume_scaledUnitRegion :
    normalizedRealLineVolume ((fun x => (1 : Real) + x) '' unitInterval) = 1 := by
  rw [normalizedRealLineVolume, Measure.smul_apply, realLine_scaledUnitRegion_measure_eq,
    realLine_unitInterval_volume]
  simpa using ENNReal.inv_mul_cancel
    (ne_of_gt (ENNReal.ofReal_pos.mpr (by norm_num : (0 : Real) < 2)))
    ENNReal.ofReal_ne_top

/-- The normalization step preserves translation invariance: the normalized measure
is again an additive Haar measure. -/
theorem normalizedRealLineVolume_isAddHaarMeasure :
    MeasureTheory.Measure.IsAddHaarMeasure normalizedRealLineVolume :=
  MeasureTheory.Measure.IsAddHaarMeasure.smul (volume : Measure Real)
    (ENNReal.inv_ne_zero.mpr ENNReal.ofReal_ne_top)
    (ENNReal.inv_ne_top.mpr
      (ne_of_gt (ENNReal.ofReal_pos.mpr (by norm_num : (0 : Real) < 2))))

/-- The normalized carrier: the same test carrier with the unit-normalized measure.
Both the raw and the normalized inhabitant fit the consumer type; the normalization
step is invisible to consumers. -/
def realLineNormalizedHaarTranslateInterface : IQHullLogVolumeInterface Real where
  imageSet := (fun x => (1 : Real) + x) '' unitInterval
  hull := (fun x => (1 : Real) + x) '' unitInterval
  imageSet_subset_hull := subset_rfl
  logVolume := normalizedRealLineVolume
  logVolume_mono := fun hST => measure_mono hST
  unitRegion := unitInterval
  scaleShift := fun x => (1 : Real) + x
  hull_subset_scaleShift := subset_rfl
  unitRegion_logVolume_lt_top := by
    rw [normalizedRealLineVolume_unitInterval]
    exact ENNReal.one_lt_top
  scaleShift_unitRegion_logVolume_le := by
    rw [normalizedRealLineVolume]
    simp only [Measure.smul_apply]
    rw [realLine_image_add_translate_volume 1 unitInterval]

end

end LeanFormal.IUT.HaarTranslateModel.RealLine

namespace LeanFormal.IUT.Audit

/-- Audit record for the drop-in consumption of the P1 real-line Haar-translate
carrier in the N14 certificate pipeline, with the [AbsTopIII] normalization step
realized on the test carrier (outsider survey P1, continued). -/
def haarTranslateRealLineConsumerWiring : Obligation :=
  { id := "IUT-III.corollary-3.12-haar-translate-real-line-consumer-wiring"
    source :=
      "IUT III, Corollary 3.12, Step (xi) (N14 certificate slots); [AbsTopIII] " ++
        "Proposition 5.7, (i), (a), (3) (normalization mu_k(O_k) = 1) and (i), (b) " ++
        "(scaling law); Corollary 5.10, (i) (finite log-volume of log-shells) -- " ++
        "test-carrier form"
    status := VerificationStatus.testCarrier
    note :=
      "Drop-in consumption of realLineHaarTranslateInterface: the generic N14 " ++
        "adapter is instantiated at the real-line instance with the carrier point " ++
        "1 = 1 + 0 (realLinePointWiringCertificate, realLinePointWiringLinkEvidence, " ++
        "realLinePointWiringCor312Conclusion); the upper slot computes to the " ++
        "concrete value 2. The [AbsTopIII] normalization step is realized on the " ++
        "same carrier: (volume [-1, 1])^{-1} scalar volume is again an additive " ++
        "Haar measure with unit-region mass exactly 1 (normalizedRealLineVolume_" ++
        "unitInterval, normalizedRealLineVolume_isAddHaarMeasure), and the " ++
        "normalized measure inhabits the interface as a second test-carrier " ++
        "inhabitant (realLineNormalizedHaarTranslateInterface). Reductions: raw " ++
        "Haar is not the normalized log-volume of Proposition 5.7 / Corollary " ++
        "5.10; the multiplicative scaling law is represented only by additive " ++
        "translation; the literal IQ(S+-_{j+1}; n,circ D^vdash_{vQ}) carrier is " ++
        "not realized; the value-level boundary at I.ThetaPilotPoint is untouched."
    dependsOn :=
      [ "IUT-III.corollary-3.12-haar-translate-real-line-instance",
        "IUT-III.corollary-3.12-iq-hull-value-carrier-wiring" ] }

end LeanFormal.IUT.Audit
