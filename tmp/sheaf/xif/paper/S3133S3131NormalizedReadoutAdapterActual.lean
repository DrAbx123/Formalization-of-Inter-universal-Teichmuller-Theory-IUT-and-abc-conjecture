import tmp.sheaf.xif.paper.S3131PaperNormalizedComparisonActual
import tmp.sheaf.xif.paper.S3133S3131WeightNormalizationActual
import tmp.sheaf.xif.paper.S3137QThetaPilotLogVolumeReadingsActual
import tmp.sheaf.xif.paper.S3137NativeToC3SameCReadoutActual
import tmp.sheaf.xif.paper.QPilotObjectActual
import tmp.sheaf.xif.paper.S3137QThetaComparisonBridgeActual
import tmp.sheaf.xif.paper.VbadPlaceIndexingActual

/-!
# Normalized-weight adapters for mainline M5a'/M5b' and lattice R1

COMPONENT, not a paper object.  Named consumers: mainline task-20 model map
M5a'/M5b' (S3131Stage2ModelMapActual) and lattice S3137NativeToC3SameCReadoutActual.
Source: IUT III Remark 3.1.1(ii)-(iv) p.95-97; Prop 3.9(i) p.115; Cor 3.12
corpus 10324-10353; IUT IV Prop 1.4(i).  Given mainline's regional readouts
S3131PaperRegionalQ/Hull (weighted by nativeBadLocalWeight) and the actual
normalized weights S3131NormalizedWeight with proved total one, this file gives:

* the exact algebra: raw regional readout = weightSum * normalized regional
  readout; weightSum * normalizedWeight = raw weight;
* per-b match collapse: from per-b readout equalities, the NORMALIZED regional
  readout equals the common value (unconditional total-one weights);
* the raw regional equalities from the normalized model map plus the single
  residual S3131WeightSumOneHypothesis (raw total one);
* the normalized same-C bridge structures and the theorem deriving lattice's
  raw NativeToC3SameCReadoutIdentification from them plus the residual.

No weight total-one is assumed where not stated.  No sorry/axiom/toy.  WRITE-ONLY.
-/

noncomputable section
open scoped BigOperators
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 1000000

namespace LeanFormal.IUT.XiFPaper.S3133S3131NormalizedReadoutAdapterActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.N8Closure.SourcePilotRegion
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.QPilotZeroLocusDivisorActual
open LeanFormal.IUT.XiFPaper.S3131PaperNormalizedComparisonActual
open LeanFormal.IUT.XiFPaper.S3133S3131WeightNormalizationActual
open LeanFormal.IUT.XiFPaper.S3137QThetaPilotLogVolumeReadingsActual
open LeanFormal.IUT.XiFPaper.S3137NativeToC3SameCReadoutActual
open LeanFormal.IUT.N8Closure.PaperQPilotObjectActual
open LeanFormal.IUT.XiFPaper.S3137QThetaComparisonBridgeActual
open LeanFormal.IUT.XiFPaper.VbadPlaceIndexingActual
open MeasureTheory

universe u

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]
variable [∀ b : Bad (nativePlaceSelection T),
  MeasurableSpace (qVFamTensorBlock T b)]
variable [∀ b : Bad (nativePlaceSelection T),
  BorelSpace (qVFamTensorBlock T b)]
variable (mu : ∀ b : Bad (nativePlaceSelection T),
  Measure (qVFamTensorBlock T b))
variable [∀ b : Bad (nativePlaceSelection T), Measure.IsAddHaarMeasure (mu b)]
variable {V : Type} {I : OriginalInput l V}
variable (C3 : SourcePilotRegionData (l := l) (V := V) I)
variable (P : PaperQPilotObjectActual (l := l) (I := I))

/-! ## 1. Normalized regional readouts -/

/-- Paper-normalized global q readout with the total-one normalized weights. -/
noncomputable def S3131PaperRegionalQNormalized : Real :=
  ∑ b : Bad (nativePlaceSelection T),
    S3131NormalizedWeight T b * S3131PaperQReadout (l := l) T mu b

/-- Paper-normalized global hull readout with the total-one normalized weights. -/
noncomputable def S3131PaperRegionalHullNormalized : Real :=
  ∑ b : Bad (nativePlaceSelection T),
    S3131NormalizedWeight T b * S3131PaperHullReadout (l := l) T mu b

/-- raw weight = weightSum * normalized weight. -/
theorem S3131WeightSum_mul_normalizedWeight [Nonempty (Bad (nativePlaceSelection T))]
    (b : Bad (nativePlaceSelection T)) :
    S3131WeightSum T * S3131NormalizedWeight T b = nativeBadLocalWeight T b := by
  unfold S3131NormalizedWeight
  field_simp [ne_of_gt (S3131WeightSum_pos T)]

/-- raw q regional = weightSum * normalized q regional. -/
theorem S3131PaperRegionalQ_eq_weightSum_mul_normalized
    [Nonempty (Bad (nativePlaceSelection T))] :
    S3131PaperRegionalQ (l := l) T mu =
      S3131WeightSum T * S3131PaperRegionalQNormalized T mu := by
  unfold S3131PaperRegionalQ S3131PaperRegionalQNormalized S3131NormalizedWeight
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro b _
  field_simp [ne_of_gt (S3131WeightSum_pos T)]

/-- raw hull regional = weightSum * normalized hull regional. -/
theorem S3131PaperRegionalHull_eq_weightSum_mul_normalized
    [Nonempty (Bad (nativePlaceSelection T))] :
    S3131PaperRegionalHull (l := l) T mu =
      S3131WeightSum T * S3131PaperRegionalHullNormalized T mu := by
  unfold S3131PaperRegionalHull S3131PaperRegionalHullNormalized S3131NormalizedWeight
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro b _
  field_simp [ne_of_gt (S3131WeightSum_pos T)]

/-! ## 3. Per-b match collapse -/

/-- Per-b q matches collapse to the normalized q regional readout. -/
theorem S3131PaperRegionalQNormalized_eq_of_perB
    [Nonempty (Bad (nativePlaceSelection T))]
    {x : Real}
    (h : ∀ b : Bad (nativePlaceSelection T),
      S3131PaperQReadout (l := l) T mu b = x) :
    S3131PaperRegionalQNormalized (l := l) T mu = x := by
  unfold S3131PaperRegionalQNormalized
  rw [Finset.sum_congr rfl (fun b _ => by rw [h b])]
  rw [← Finset.sum_mul, S3131NormalizedWeightTotal, one_mul]

/-- Per-b hull matches collapse to the normalized hull regional readout. -/
theorem S3131PaperRegionalHullNormalized_eq_of_perB
    [Nonempty (Bad (nativePlaceSelection T))]
    {x : Real}
    (h : ∀ b : Bad (nativePlaceSelection T),
      S3131PaperHullReadout (l := l) T mu b = x) :
    S3131PaperRegionalHullNormalized (l := l) T mu = x := by
  unfold S3131PaperRegionalHullNormalized
  rw [Finset.sum_congr rfl (fun b _ => by rw [h b])]
  rw [← Finset.sum_mul, S3131NormalizedWeightTotal, one_mul]

/-- Exact normalized same-C model map (variant A). -/
structure S3133Stage2ModelMapGlobalNormalized : Type where
  arithmeticModelMatch : Prop
  badTensorIndexMatch : Prop
  qParameterMatch : Prop
  thetaValueMatch : Prop
  qReadout_eq_normalized :
    qPilotLogVolumeReading P = S3131PaperRegionalQNormalized (l := l) T mu
  hullReadout_eq_normalized :
    thetaPilotHullLogVolumeReal C3 =
      S3131PaperRegionalHullNormalized (l := l) T mu

/-- From the normalized model map plus the single residual raw-weight-total-one
hypothesis, the raw paper-normalized readout equalities of mainline variant A
hold. -/
theorem rawReadoutEqualities_of_normalizedModelMap
    [Nonempty (Bad (nativePlaceSelection T))]
    (M : S3133Stage2ModelMapGlobalNormalized T mu C3 P)
    (hw : S3131WeightSumOneHypothesis T) :
    qPilotLogVolumeReading P = S3131PaperRegionalQ (l := l) T mu ∧
      thetaPilotHullLogVolumeReal C3 =
        S3131PaperRegionalHull (l := l) T mu := by
  constructor
  · rw [M.qReadout_eq_normalized,
      S3131PaperRegionalQ_eq_weightSum_mul_normalized, hw, one_mul]
  · rw [M.hullReadout_eq_normalized,
      S3131PaperRegionalHull_eq_weightSum_mul_normalized, hw, one_mul]

/-- Normalized same-C bridge: scaled form of lattice's SameCQThetaReadoutBridge. -/
structure S3133SameCQThetaReadoutBridgeNormalized : Prop where
  qReadout_eq_normalized :
    qPilotLogVolumeReading P = S3131PaperRegionalQNormalized (l := l) T mu
  hullReadout_eq_normalized :
    thetaPilotHullLogVolumeReal C3 =
      S3131PaperRegionalHullNormalized (l := l) T mu

/-- The normalized bridge from the normalized model map. -/
theorem sameCBridgeNormalized_of_normalizedModelMap
    (M : S3133Stage2ModelMapGlobalNormalized T mu C3 P) :
    S3133SameCQThetaReadoutBridgeNormalized T mu C3 P :=
  ⟨M.qReadout_eq_normalized, M.hullReadout_eq_normalized⟩

/-- The exact same-C readout bridge of lattice is definitionally the raw readout
conjunction proved above (SameCQThetaReadoutBridge is a def of that conjunction);
consumers transport it with rfl. -/
theorem rawReadoutEqualities_sameC
    [Nonempty (Bad (nativePlaceSelection T))]
    (M : S3133Stage2ModelMapGlobalNormalized T mu C3 P)
    (hw : S3131WeightSumOneHypothesis T) :
    (qPilotLogVolumeReading P = S3131PaperRegionalQ (l := l) T mu) ∧
      (thetaPilotHullLogVolumeReal C3 =
        S3131PaperRegionalHull (l := l) T mu) :=
  rawReadoutEqualities_of_normalizedModelMap T mu C3 P M hw

end LeanFormal.IUT.XiFPaper.S3133S3131NormalizedReadoutAdapterActual
