import tmp.sheaf.xif.paper.S3133S3131GaussianModelMapMinimalActual
import tmp.sheaf.xif.paper.S3137QThetaComparisonBridgeActual
import LeanFormal.IUT.Audit.Status

/-!
# S3137: reduced R1 residual from qpilot's minimal Gaussian model map

Lead request: instantiate the R1 same-C residual from qpilot's
S3133GaussianModelMapResidualMinimal so that R1 reduces to exactly the genuine
missing fields M1 + shrunk M2 (plus the readout-side obligations).

qpilot proves M0 (S3133GaussianModelMapResidualMinimal_m0) and M3
(S3133GaussianModelMapResidualMinimal_m3); its residual record carries
* m1_indexInjection : Prop (bad <-> all-place index injection; genuine source
  placeToMod provenance missing, IUT I Def 3.1(b),(e); III Prop 3.4(ii));
* m2_baseQMatch : Prop (= S3133GaussianQParameterMatchAtBase T; clause-B base-q
  descent with Gaussian norm 1/5 above 5; IUT I Ex 3.2(iv); III Def 3.8(i)).

This file defines the reduced residual record bringing M0/M3 in as PROVED
fields (filled from qpilot theorems) and M1/M2 as residual propositions, plus
the readout-side residual (M4 raw weight total-one and M5a/M5b readout
equalities, owned by mainline/qpilot/shehdd task-40/task-28).  The signed Cor
3.12 comparison and magnitude form are derived from the readout side via the
S3137 bridge and mainline's unconditional paper-normalized comparison.
No assertion of residual fields, no carrier substitution, no sorry, no axiom.
WRITE-ONLY.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 2000000

noncomputable section

namespace LeanFormal.IUT.XiFPaper.S3137QpilotGaussianResidualReducedActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.N8Closure.SourcePilotRegion
open LeanFormal.IUT.N8Closure.PaperQPilotObjectActual
open LeanFormal.IUT.N8Closure.C3Actual
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.S3131QCLeHCComparisonActual
open LeanFormal.IUT.XiFPaper.S3131PaperNormalizedComparisonActual
open LeanFormal.IUT.XiFPaper.S3131SameCSourceInputActual
open LeanFormal.IUT.XiFPaper.VbadPlaceIndexingActual
open LeanFormal.IUT.XiFPaper.C3GaussianThetaPacketActual
open LeanFormal.IUT.XiFPaper.S3133S3131GaussianModelComponentsActual
open LeanFormal.IUT.XiFPaper.S3133S3131GaussianModelMapMinimalActual
open LeanFormal.IUT.XiFPaper.S3137QThetaPilotLogVolumeReadingsActual
open LeanFormal.IUT.XiFPaper.S3137QThetaComparisonBridgeActual
open MeasureTheory
open scoped BigOperators

variable {l : PrimeGeFive} {V : Type} {I : OriginalInput l V}
variable (D : SourcePilotRegionDonors (I := I))
variable (R : S3133GaussianModelMapResidualMinimal (l := l) (I := I) D)

abbrev gaussianT : SourceNativeInitialThetaData.{0} l :=
  R.C.toSourceNativeInitialThetaData

abbrev gaussianC3 : SourcePilotRegionData (l := l) (V := V) I :=
  actualGaussianC3 (l := l) (V := V) (I := I) D

variable [Fintype (Bad (nativePlaceSelection gaussianT))]
variable [forall b : Bad (nativePlaceSelection gaussianT),
  MeasurableSpace (qVFamTensorBlock gaussianT b)]
variable [forall b : Bad (nativePlaceSelection gaussianT),
  BorelSpace (qVFamTensorBlock gaussianT b)]
variable (mu : forall b : Bad (nativePlaceSelection gaussianT),
  Measure (qVFamTensorBlock gaussianT b))
variable [forall b : Bad (nativePlaceSelection gaussianT), Measure.IsAddHaarMeasure (mu b)]
variable (P : PaperQPilotObjectActual (l := l) (I := I))

/-- **Reduced R1 residual.**  M0 and M3 are PROVED (fields filled from qpilot's
theorems below); M1 and shrunk M2 are the genuine missing residual propositions;
M4/M5a/M5b are the readout-side obligations. -/
structure SameCModelMapResidualReduced : Prop where
  /-- M0 PROVED: actual SourceCompletion with the concrete Gaussian arithmetic -/
  m0 : S3133GaussianModelArithmeticMatch (l := l) gaussianT
  /-- M1 residual: bad <-> all-place index injection (source placeToMod missing) -/
  m1 : R.m1_indexInjection
  /-- M2 residual: clause-B base-q descent + Gaussian norm 1/5 above 5 -/
  m2 : R.m2_baseQMatch
  /-- M3 PROVED: actual Gaussian Stage-2 theta values match the source theater -/
  m3 : S3133GaussianThetaValueMatch (l := l) (V := V) (I := I) gaussianC3
  /-- M4 readout residual: raw Remark 3.1.1(ii) weight sum is one -/
  m4 : (∑ b : Bad (nativePlaceSelection gaussianT),
    nativeBadLocalWeight gaussianT b) = 1
  /-- M5a readout residual: per-b q readout equality -/
  m5a : forall b : Bad (nativePlaceSelection gaussianT),
    S3131PaperQReadout (l := l) gaussianT mu b = qPilotLogVolumeReading P
  /-- M5b readout residual: per-b Theta-hull readout equality -/
  m5b : forall b : Bad (nativePlaceSelection gaussianT),
    S3131PaperHullReadout (l := l) gaussianT mu b = thetaPilotHullLogVolumeReal gaussianC3

/-- **Construct the reduced residual**: M0 and M3 are supplied by qpilot's
proved theorems; only M1, M2 and the readout-side hypotheses are assumed. -/
theorem sameCModelMapResidualReduced_of_qpilot
    (hM1 : R.m1_indexInjection) (hM2 : R.m2_baseQMatch)
    (hM4 : (∑ b : Bad (nativePlaceSelection gaussianT),
      nativeBadLocalWeight gaussianT b) = 1)
    (hM5a : forall b : Bad (nativePlaceSelection gaussianT),
      S3131PaperQReadout (l := l) gaussianT mu b = qPilotLogVolumeReading P)
    (hM5b : forall b : Bad (nativePlaceSelection gaussianT),
      S3131PaperHullReadout (l := l) gaussianT mu b = thetaPilotHullLogVolumeReal gaussianC3) :
    SameCModelMapResidualReduced (l := l) (V := V) (I := I) D R mu P where
  m0 := S3133GaussianModelMapResidualMinimal_m0 (l := l) (V := V) (I := I) D R
  m1 := hM1
  m2 := hM2
  m3 := S3133GaussianModelMapResidualMinimal_m3 (l := l) (V := V) (I := I) D
  m4 := hM4
  m5a := hM5a
  m5b := hM5b

/-- Weighted q-side collapse from M4+M5a. -/
theorem reduced_regionalQ_eq (M : SameCModelMapResidualReduced (l := l) (V := V) (I := I) D R mu P) :
    S3131PaperRegionalQ (l := l) gaussianT mu = qPilotLogVolumeReading P := by
  unfold S3131PaperRegionalQ
  rw [Finset.sum_congr rfl (fun b _ => by rw [M.m5a b])]
  rw [← Finset.sum_mul, M.m4, one_mul]

/-- Weighted Theta-hull collapse from M4+M5b. -/
theorem reduced_regionalHull_eq
    (M : SameCModelMapResidualReduced (l := l) (V := V) (I := I) D R mu P) :
    S3131PaperRegionalHull (l := l) gaussianT mu = thetaPilotHullLogVolumeReal gaussianC3 := by
  unfold S3131PaperRegionalHull
  rw [Finset.sum_congr rfl (fun b _ => by rw [M.m5b b])]
  rw [← Finset.sum_mul, M.m4, one_mul]

/-- Same-C bridge from the reduced residual. -/
theorem reduced_bridge
    (M : SameCModelMapResidualReduced (l := l) (V := V) (I := I) D R mu P) :
    SameCQThetaReadoutBridge (l := l) gaussianT mu gaussianC3 P := by
  refine ⟨?_, ?_⟩
  · exact (reduced_regionalQ_eq (l := l) (V := V) (I := I) D R mu P M).symm
  · exact (reduced_regionalHull_eq (l := l) (V := V) (I := I) D R mu P M).symm

/-- **Cor 3.12 signed comparison from the reduced R1 residual.** -/
theorem qThetaPilotLogVolumeComparison_of_reduced
    (M : SameCModelMapResidualReduced (l := l) (V := V) (I := I) D R mu P) :
    qThetaPilotLogVolumeComparison gaussianC3 P :=
  qThetaPilotLogVolumeComparison_of_sameC (l := l) gaussianT mu gaussianC3 P
    (reduced_bridge (l := l) (V := V) (I := I) D R mu P M)

/-- **Cor 3.12 magnitude form from the reduced R1 residual.** -/
theorem qThetaMagnitudeComparison_of_reduced
    (M : SameCModelMapResidualReduced (l := l) (V := V) (I := I) D R mu P) :
    -thetaPilotHullLogVolumeReal gaussianC3 <= -qPilotLogVolumeReading P :=
  qThetaMagnitudeComparison_of_sameC (l := l) gaussianT mu gaussianC3 P
    (reduced_bridge (l := l) (V := V) (I := I) D R mu P M)

end LeanFormal.IUT.XiFPaper.S3137QpilotGaussianResidualReducedActual

namespace LeanFormal.IUT.Audit

/-- **Reduced R1 residual (qpilot minimal Gaussian model map).**  M0 PROVED
(actual SourceCompletion above the model arithmetic) and M3 PROVED (actual
Gaussian Stage-2 theta values match the source theater).  Residual is exactly
{M1: source placeToMod provenance (bad<->all-place injection, contract-separated
genuine missing), M2: clause-B base-q descent + Gaussian norm 1/5 at places
above 5, M4: raw weight total-one (normalized alternative exists), M5a/M5b:
canonical readout equalities (task-40/task-28)}.  Signed comparison and
magnitude form derived from the readout side via mainline's unconditional
paper-normalized comparison. -/
def s3137R1ReducedResidual : Obligation :=
  { id := "S3137.residual.R1-reduced-final"
    source := "IUT I, Def 3.1, Ex. 3.2(iv); IUT II, Remark 2.5.1, (i); IUT III, Prop. 3.4, (ii), pp. 102-103; Def. 3.8, (i), p. 112; Remark 3.1.1, (ii); IUT IV, Prop. 1.4, (i); Cor. 3.12"
    status := VerificationStatus.pending
    note := "M0/M3 proved via qpilot; residual M1 (source placeToMod provenance, contract-separated) + M2 (clause-B base-q descent/Gaussian norm) + M4 raw weight total-one + M5a/M5b readout equalities.  Comparison derived from readout side.  No residual field proof assumed."
    dependsOn := ["S3133S3131GaussianModelMapMinimalActual", "S3137QThetaComparisonBridgeActual", "S3137QpilotGaussianResidualReducedActual"] }

end LeanFormal.IUT.Audit
