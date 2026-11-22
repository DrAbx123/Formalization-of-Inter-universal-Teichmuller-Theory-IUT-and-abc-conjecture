import tmp.sheaf.xif.paper.Mzk1P2MultiIndexLandingActual
import tmp.sheaf.xif.paper.PaperRootExtensionHaarActual
import tmp.sheaf.xif.paper.PaperRootExtensionProductHaarActual
import tmp.sheaf.xif.paper.PaperRootExtensionNormBoundActual
import tmp.sheaf.xif.paper.S1902ActualThetaHullActual
import tmp.sheaf.xif.paper.S1929LiteralIQCarrierActual
import tmp.sheaf.xif.paper.PaperC3ThetaRootActual
import Mathlib.Tactic

noncomputable section
namespace LeanFormal.IUT.XiFPaper.Mzk1P7MultiradialP2DataActual
open LeanFormal.IUT LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.XiFPaper.PaperRootExtensionHaarActual
open LeanFormal.IUT.XiFPaper.PaperRootExtensionProductHaarActual
open LeanFormal.IUT.XiFPaper.PaperRootExtensionNormBoundActual
open LeanFormal.IUT.XiFPaper.PaperRootCompletionTensorActual
open LeanFormal.IUT.XiFPaper.S1902ActualThetaHullActual
open LeanFormal.IUT.XiFPaper.S1929LiteralIQCarrierActual
open LeanFormal.IUT.XiFPaper.PaperC3ThetaRootActual
open LeanFormal.IUT.XiFPaper.Mzk1P2LabelBlockSumActual
open LeanFormal.IUT.XiFPaper.S664RootQUnitNormLeOneActual
open MeasureTheory

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]

theorem thetaGen_mem_unitBall (j : ThetaLabel (l := l)) :
    (fun b => rootNormedThetaValueInL T b (thetaLabelToSigned j)) ∈
      rootExtensionProductUnitBall T := by
  intro b _
  change (fun b => rootNormedThetaValueInL T b (thetaLabelToSigned j)) b ∈
    Metric.closedBall (0 : rootNormedExtension T b) 1
  rw [Metric.mem_closedBall, dist_eq_norm, sub_zero]
  simpa using rootNormedThetaValueInL_norm_le_one (T := T) (b := b)
    (rootQUnitNormLeOne (T := T)) (thetaLabelToSigned j)

noncomputable def actualP2LabelBlockData :
    P2LabelBlockSumData T (ThetaLabel (l := l)) where
  thetaGen j := fun b => rootNormedThetaValueInL T b (thetaLabelToSigned j)
  theta_mem j := thetaGen_mem_unitBall T j
  coeff j := fun b => rootNormedThetaValueInL T b (thetaLabelToSigned j)
  coeff_mem j := thetaGen_mem_unitBall T j

theorem actualP2Landing_mem :
    p2MultiIndexLanding T (actualP2LabelBlockData T) ∈
      rootExtensionProductUnitBall T :=
  p2MultiIndexLanding_mem T (actualP2LabelBlockData T)

#print axioms thetaGen_mem_unitBall
#print axioms actualP2Landing_mem
end LeanFormal.IUT.XiFPaper.Mzk1P7MultiradialP2DataActual
end
