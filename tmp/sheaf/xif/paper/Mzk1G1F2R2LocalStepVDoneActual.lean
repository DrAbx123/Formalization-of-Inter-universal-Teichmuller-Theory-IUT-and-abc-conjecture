/- LocalStepV: root ball / log-volume on the actual root extension, from urRootAlpha_mass.

localRootBall is the integer unit ball O_L inside rootNormedExtension; localRootLogVolume is
the normalized log-volume increment of urRootAlpha * O_L.  urRootAlpha_mass identifies it
with (1/(2l)) log||q_b|| (and its order form), which is the scalar used by paperThetaReadout.
-/
import tmp.sheaf.xif.paper.Mzk1URRootExtInstancesActual
import tmp.sheaf.xif.paper.Mzk1BoxR2PaperThetaLeHActual
import tmp.sheaf.xif.paper.PaperRootCompletionTensorActual
import tmp.sheaf.xif.paper.PaperRootExtensionHaarActual
import LeanFormal.IUT.Foundations.LocalFields.IntegralUnits
import Mathlib.Tactic
noncomputable section
open MeasureTheory
namespace LeanFormal.IUT.XiFPaper.Mzk1G1F2R2LocalStepVDoneActual
open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.Mzk1URRootExtensionActual
open LeanFormal.IUT.XiFPaper.Mzk1URRootExtInstancesActual
open LeanFormal.IUT.XiFPaper.PaperRootCompletionTensorActual
open LeanFormal.IUT.XiFPaper.PaperRootExtensionHaarActual
open LeanFormal.IUT.LocalFieldIntegralUnits
open LeanFormal.IUT.XiFPaper.Mzk1BoxR2PaperThetaLeHActual
open LeanFormal.IUT.XiFPaper.PaperThetaRootObstructionActual
open LeanFormal.IUT.LocalFieldLogarithm
variable {l : PrimeGeFive} (T : SourceNativeInitialThetaData.{0} l)
variable (b : Bad (nativePlaceSelection T))

/-- The local root unit ball O_L in the actual root extension. -/
noncomputable def localRootBall : Set (rootNormedExtension T b) :=
  (Integers (rootNormedExtension T b) : Set (rootNormedExtension T b))

/-- Normalized log-volume increment of urRootAlpha * O_L. -/
noncomputable def localRootLogVolume : Real :=
  (1 / (Module.finrank ℚ_[qVFamTensorP T b] (rootNormedExtension T b) : Real)) *
    (Real.log (rootExtensionHaar T b
        ((urRootAlpha T b : rootNormedExtension T b) • localRootBall (T := T) (b := b))).toReal -
      Real.log (rootExtensionHaar T b (localRootBall (T := T) (b := b))).toReal)

/-- LocalStepV identification: localRootLogVolume = (1/(2l)) log||q_b||. -/
theorem localRootLogVolume_eq :
    localRootLogVolume (T := T) (b := b) =
      (1 / (2 * (l.value : Real))) * Real.log ‖((sourceRootQUnit T b : rootBase T b))‖ := by
  unfold localRootLogVolume localRootBall
  exact urRootAlpha_mass (T := T) (b := b)

end LeanFormal.IUT.XiFPaper.Mzk1G1F2R2LocalStepVDoneActual
