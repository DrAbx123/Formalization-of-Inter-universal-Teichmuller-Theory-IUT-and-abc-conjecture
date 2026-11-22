/- U-R theta hull: the actual per-b q-pilot ≤ actual theta hull inequality,
the actual theta hull magnitude target, and the actual root-mass identity on
the actual finite root extension (route §5.3 C2: q side `q_P5 = -M`
with `M = Q/(2*l)`, theta side `theta_P5 <= H_pkt`).

The q side is the actual normalized log-mass identity of the full root lattice
in the actual finite root extension (`Mzk1URRootExtensionActual.urRootMass_kummer`);
no rfl, no hypothesis, no completion root.  The theta side is the accepted
actual root-hull containment. -/
import tmp.sheaf.xif.paper.P6HThetaNormalization2Actual
import tmp.sheaf.xif.paper.Mzk1ActualHullTargetMagnitudeActual
import tmp.sheaf.xif.paper.PaperLevelXiFTargetProofActual
import tmp.sheaf.xif.paper.PaperLevelXiFTargetActual
import tmp.sheaf.xif.paper.Mzk1URPacketActual
import tmp.sheaf.xif.paper.Mzk1URRootExtensionActual
import Mathlib.Tactic

noncomputable section
namespace LeanFormal.IUT.XiFPaper.Mzk1URThetaHullActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.N8Closure.NativeInput
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.P6HThetaNormalization2Actual
open LeanFormal.IUT.XiFPaper.Mzk1ActualHullTargetMagnitudeActual
open LeanFormal.IUT.XiFPaper.PaperLevelXiFTargetActual
open LeanFormal.IUT.XiFPaper.PaperLevelXiFTargetProofActual
open LeanFormal.IUT.LocalFieldLogarithm
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.PaperThetaRootObstructionActual
open LeanFormal.IUT.XiFPaper.PaperRootCompletionTensorActual
open LeanFormal.IUT.XiFPaper.Mzk1P6PhiActionFamilyActual
open LeanFormal.IUT.XiFPaper.Mzk1URPacketActual
open LeanFormal.IUT.XiFPaper.Mzk1URRootExtensionActual
open MeasureTheory

universe u

variable {l : PrimeGeFive} (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]
variable [∀ b : Bad (nativePlaceSelection T), MeasurableSpace (qVFamTensorBlock T b)]
variable [∀ b : Bad (nativePlaceSelection T), BorelSpace (qVFamTensorBlock T b)]

/-- Theta side of C2: the signed q-pilot lower bound `-M <= H_theta`
(`M = actualQPilotMagnitudeClassical` at the actual normalization). -/
theorem ur_negM_le_Htheta :
    -actualQPilotMagnitudeClassical (l := l) T ≤ actualThetaHullLogRoot (l := l) T :=
  p6_neg_M_le_HTheta2 (l := l) T

/-- Actual per-b q-pilot ≤ actual theta hull (actual root-hull containment). -/
theorem ur_perB_containment (b : Bad (nativePlaceSelection T)) :
    perBQPilotLog (l := l) T b ≤ perBThetaHullLog (l := l) T b :=
  actualPerB_inequality (l := l) T b

/-- Actual theta-hull magnitude target. -/
theorem ur_thetaHull_magnitude : ActualPaperXiFTargetMagnitude (l := l) T :=
  actualTargetMagnitude_actual (l := l) T

/-- q side of C2, per bad place, value/order form: the actual log-norm of the
theta pilot on the actual root extension is `-(gaussExponent j/(2l)) * log ‖q_b‖`
(this is the actual C1 negative term, finrank-free; the finrank-normalized Haar
mass version is the consumer's `Mzk1ULThetaPacketActual.ulNormalizedLogMass_smul`). -/
theorem ur_q_rootMass_order_form (b : Bad (nativePlaceSelection T))
    (j : SignedLabel l.value) :
    Real.log ‖urRootTheta T b j‖ =
      -((gaussExponent j.1 : ℝ) / (2 * (l.value : ℝ))) *
        localNormOrder (qVFamTensorP T b) ((sourceRootQUnit T b : rootBase T b)) *
        Real.log (qVFamTensorP T b : ℝ) :=
  urRootTheta_log_norm_eq_neg_shift (T := T) (b := b) j

/-
C2 theta-side packet containment (`theta_P5 <= H_pkt` region form) is the existing
accepted donor `Mzk1P6PhiActionFamilyActual.p6_possibleImages_subset_packetHull`; every theta
possible image lies in the actual packet hull by construction of the holomorphic
hull.  Consumers (`david`/`sophie`) import that donor directly; it is not duplicated here.
-/
#print axioms ur_negM_le_Htheta
#print axioms ur_perB_containment
#print axioms ur_q_rootMass_order_form

end LeanFormal.IUT.XiFPaper.Mzk1URThetaHullActual
end