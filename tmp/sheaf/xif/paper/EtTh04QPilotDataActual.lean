import tmp.sheaf.xif.paper.S3132ThetaSideComparisonRegionBundleV2Actual

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 1500000

noncomputable section
open MeasureTheory
open LeanFormal.IUT
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.S3131CanonicalRootedQCActual
open LeanFormal.IUT.XiFPaper.S3136NativeHaarFamilyActual
open LeanFormal.IUT.XiFPaper.S3136ModelSourceClauseActual
open LeanFormal.IUT.XiFPaper.S3136ModelNativeDataWithHaarActual
open LeanFormal.IUT.XiFPaper.S3132RootedScalingDataTrivialActual
open LeanFormal.IUT.XiFPaper.S3132ThetaSideModelClauseResidualActual
open LeanFormal.IUT.XiFPaper.S3132ThetaSideSharpResidualReducedActual
open LeanFormal.IUT.XiFPaper.S3132ThetaSideModelComparisonDataActual
open LeanFormal.IUT.XiFPaper.S3132ThetaSideComparisonRegionBundleActual
open LeanFormal.IUT.XiFPaper.S3132ThetaSideHullSlotWiringActual
open LeanFormal.IUT.XiFPaper.S3132ThetaSideQSideSlotWiringActual
open LeanFormal.IUT.XiFPaper.S3132ThetaSideComparisonRegionBundleV2Actual
open LeanFormal.IUT.XiFPaper.S3132SourceAdaptedPilotComparisonActual
open LeanFormal.IUT.XiFPaper.S3132SourceAdaptedCorollary312DataActual
open LeanFormal.IUT.XiFPaper.S3129IQHullLogVolumeSourceActual
open LeanFormal.IUT.XiFPaper.S3132IQHullRealLogVolumeReadoutActual

namespace LeanFormal.IUT.XiFPaper.EtTh04QPilotDataActual

/-!
# STEP 0 prior-art: q-pilot|Theta-pilot|thetaPilot -> hits our Theta-side files (modelThetaValue, WeightedRootedIdentity, H4/H5 slots) + IUTIII/Corollary312/ArithmeticQPilotGlobalNormalization (fibers/degrees; identification NOT established) + LeanFormal/IUTDispute.lean:27-31 (qPilot/thetaPilot interface) -> ADAPT (interface + class A projections only; no closure).

# [EtTh] 04: theta q-pilot / Theta-pilot data interface (aligned to Theta-side H2/H4)

Corpus: papers/motizuki_corpus/text/The Etale Theta Function and its Frobenioid-theoretic
Manifestations.txt.  The tree does NOT establish the identification of its
arithmetic q-pilot normalization with the paper's actual q-pilot (frozen obstacle).
Hence: define the interface with explicit magnitudes; prove only the CLASS A
projection theta magnitude = canonical rooted readout; q magnitude and H4 hull bound
stay explicit hypotheses.  No closure claim.
-/

variable {l : PrimeGeFive}
variable (M : LGPModelSourceClauseMissing l)
variable [Fintype (Bad (nativePlaceSelection (lgpModelNativeData M)))]

/-- [EtTh] q-pilot/Theta-pilot magnitude interface (data record). -/
structure EtThQPilotData where
  thetaMagnitude : ℝ
  qMagnitude : ℝ
  theta_eq : thetaMagnitude = modelThetaValue M
  q_negative : qMagnitude < 0

/-- The canonical rooted Theta value as an [EtTh] Theta-pilot magnitude. -/
def etThQPilotDataOfModel : EtThQPilotData M :=
  { thetaMagnitude := modelThetaValue M
    qMagnitude := -1
    theta_eq := rfl
    q_negative := by norm_num }

/-- The [EtTh] Theta magnitude equals the canonical rooted readout. -/
theorem etThQPilotDataOfModel_theta :
    (etThQPilotDataOfModel M).thetaMagnitude = modelThetaValue M :=
  rfl

/-- The canonical packaged source readout (class A projection, canonical form). -/
theorem etThQPilotData_canonicalReadout
    (h : ModelWeightedRootedIdentity M) :
    Real.log sourceHullRealLogVolume =
      S3131CanonicalRootedHC (lgpModelNativeData M)
        (fun b => lgpNativeHaarFamily (lgpModelNativeData M) b) :=
  weightedIdentity_canonicalReadout M h

/-- The same projection in [EtTh] Theta-pilot magnitude form. -/
theorem etThQPilotData_canonicalReadout_theta
    (h : ModelWeightedRootedIdentity M) :
    Real.log sourceHullRealLogVolume = (etThQPilotDataOfModel M).thetaMagnitude := by
  simpa [etThQPilotDataOfModel, modelThetaValue, modelNativeData] using
    weightedIdentity_canonicalReadout M h
#check etThQPilotData_canonicalReadout
#check etThQPilotData_canonicalReadout_theta

end LeanFormal.IUT.XiFPaper.EtTh04QPilotDataActual
end