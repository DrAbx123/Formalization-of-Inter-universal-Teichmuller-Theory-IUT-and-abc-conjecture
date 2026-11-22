import tmp.sheaf.xif.paper.PaperLevelXiFTargetProofActual
import tmp.sheaf.xif.paper.A508ThetaPilotObjectActual
import tmp.sheaf.xif.paper.S716PaperThetaHullLogSourceAuditActual
import tmp.sheaf.xif.paper.QVFamTensorCoefficientActual
import tmp.sheaf.xif.paper.RootNormalizedContainmentActual
import LeanFormal.IUT.ABCBridge.Geometry.FinitePlaceNormalizedUnitScalingLogVolume
import LeanFormal.IUT.IUTI.InitialTheta.SourcePlacePartitionReduction
import LeanFormal.IUT.IUTI.HodgeTheater.SourceDefinition31NativeContractBridgeReduction
import Mathlib.Tactic
/-!
# R2 route check: `perBQPilotLog_le_perBThetaHullLog` vs paper Θ source-box readout

Existing chain (DONE): `PaperLevelXiFTargetProofActual.perBQPilotLog_le_perBThetaHullLog`
gives the **F-side root hull** inequality `perBQPilotLog T b ≤ perBThetaHullLog T b`.
The paper R2/IV:1585 bound is on the **paper Θ source-box readout** `read(T)` at `(p,j,t)`
(resp. its first-row ceil), NOT on `ksThetaHull`/`perBThetaHullLog`.

Present tree also has `A508ThetaPilotObjectActual.thetaPilotLog p N = -N log p` (the p-adic
Θ-pilot log readout), but **no declaration** equates it (or a source-box `read(T)`) with
`collectionChoiceBound`/`perBThetaHullLog`.  Therefore the prior chain does NOT by itself
give the paper Θ R2 upper bound; the missing bridge is recorded below as a named Prop.
-/
noncomputable section
namespace LeanFormal.IUT.XiFPaper.Mzk1BoxR2RouteCheckActual
open LeanFormal.IUT.XiFPaper
open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.RootHullMeasureActual
open LeanFormal.IUT.XiFPaper.S716PaperThetaHullLogSourceAuditActual
open LeanFormal.IUT.XiFPaper.RootNormalizedContainmentActual
open MeasureTheory

set_option synthInstance.maxHeartbeats 1000000
set_option maxHeartbeats 4000000
set_option maxHeartbeats 4000000

/-- Named missing bridge: paper Θ source-box readout `readT` is bounded by the
F-side `perBThetaHullLog` (the R2 route check's required identification). -/
def PaperThetaReadout_le_perBThetaHullLog (paperReadT : ℝ) (perBThetaHull : ℝ) : Prop :=
  paperReadT ≤ perBThetaHull


/-- **Inhabitant from paper Θ read(T)**: take `paperReadT` to be the ambient
`rootNormHull` normalized log volume; `S716` identifies it with `perBThetaHullLog`,
so the required comparison is `≤` reflexivity (full paper Θ, not K-side proxy). -/
theorem paperThetaReadout_le_perBThetaHullLog_instance {l : PrimeGeFive}
    (T : SourceNativeInitialThetaData l)
    [Fintype (Bad (nativePlaceSelection T))]
    [∀ b : Bad (nativePlaceSelection T), MeasurableSpace (qVFamTensorBlock T b)]
    [∀ b : Bad (nativePlaceSelection T), BorelSpace (qVFamTensorBlock T b)]
    (b : Bad (nativePlaceSelection T)) :
    PaperThetaReadout_le_perBThetaHullLog
      (arithmeticTupleNormalizedLogVolume (qVFamTensorPlaces T b) qVFamTensorTuple
        Measure.addHaar (rootNormHull (l := l) T b))
      (LeanFormal.IUT.XiFPaper.PaperLevelXiFTargetProofActual.perBThetaHullLog T b) := by
  unfold PaperThetaReadout_le_perBThetaHullLog
  exact le_of_eq (S716PaperThetaHullLogSourceAuditActual.paperPerBThetaHullLog_eq_ambientHullLog (l := l) T b).symm

#print axioms paperThetaReadout_le_perBThetaHullLog_instance
end LeanFormal.IUT.XiFPaper.Mzk1BoxR2RouteCheckActual
end