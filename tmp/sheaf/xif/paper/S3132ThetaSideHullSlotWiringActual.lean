import tmp.sheaf.xif.paper.S3132ThetaSideSharpResidualReducedActual
import tmp.sheaf.xif.paper.S3132ThetaSideComparisonRegionBundleActual
import tmp.sheaf.xif.paper.S3132ThetaSideModelComparisonDataActual
import tmp.sheaf.xif.paper.S3132SourceAdaptedPilotComparisonActual
import tmp.sheaf.xif.paper.S3132SourceAdaptedCorollary312DataActual
import tmp.sheaf.xif.paper.S3136ModelSourceClauseActual
import tmp.sheaf.xif.paper.S3136ModelNativeDataWithHaarActual
import tmp.sheaf.xif.paper.S3132RootedScalingDataFormulaActual

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
open LeanFormal.IUT.XiFPaper.S3132SourceAdaptedPilotComparisonActual
open LeanFormal.IUT.XiFPaper.S3132SourceAdaptedCorollary312DataActual

namespace LeanFormal.IUT.XiFPaper.S3132ThetaSideHullSlotWiringActual

/-!
# Theta-side H4: hull-volume <= theta slot (adapted from certificate/hull route)

PRIOR ART (one line): LeanFormal/IUT/IUTIII/Corollary312/StepXI/CertificateHullWiring.lean
iqHullRealVolume_le_theta_iff:106, iqHullCertificate:155, sourceRealHullVolume_le_theta:272
(interface shape: logVolume hull <= ofReal theta and 0 <= theta and q < 0);
CardAMPLThetaBoundSupply.lean structure:78, realVolume_le:94, of_realVolume_le:116, nonempty_iff:125
-> ADAPT as an explicit H4 hypothesis on our canonical readout; the certificate-hull/AMPL source
discharge is a registered boundary (CardQCMPComparison.lean:50-68) and is NOT re-proved or claimed.
-/

variable {l : PrimeGeFive}
variable (M : LGPModelSourceClauseMissing l)
variable [Fintype (Bad (nativePlaceSelection (lgpModelNativeData M)))]

/-- **H4 slot:** an explicit Theta bound for the canonical rooted readout value.
The bound is DATA/hypothesis (certificate-hull/AMPL boundary), not proved. -/
structure ThetaSideHullBoundSlot where
  theta : ℝ
  theta_nonneg : 0 ≤ theta
  hull_le_theta : modelThetaValue M ≤ theta

/-- The slot in the certificate/hull route shape: the real hull volume is at most theta. -/
theorem thetaSideHullBoundSlot_realVolume_le (S : ThetaSideHullBoundSlot M) :
    modelThetaValue M ≤ S.theta :=
  S.hull_le_theta

/-- The slot also gives the ENNReal-level bound shape used by the certificate route. -/
theorem thetaSideHullBoundSlot_ofReal_le (S : ThetaSideHullBoundSlot M) :
    ENNReal.ofReal (modelThetaValue M) ≤ ENNReal.ofReal S.theta :=
  ENNReal.ofReal_le_ofReal S.hull_le_theta

#check ThetaSideHullBoundSlot
#check thetaSideHullBoundSlot_realVolume_le
#check thetaSideHullBoundSlot_ofReal_le

end LeanFormal.IUT.XiFPaper.S3132ThetaSideHullSlotWiringActual
end
