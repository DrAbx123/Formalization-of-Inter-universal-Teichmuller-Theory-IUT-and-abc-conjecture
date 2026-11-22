/- R2 F-side hperB: actual L_w/root datum (no completion root).

`ActualLwRootDatum` records the actual root-extension hull/root equality
`actualLocalHullLog b = log||urRootAlpha b||`; it uses urRootAlpha/rootExtensionHaar,
not BadPlaceHalfRootSupply's completion root.  From the datum plus the actual root
packet bound `log||urRootAlpha b|| <= packetV b`, we derive hperB and htheta via the DONE
ur_htheta_of_scaling.
-/
import tmp.sheaf.xif.paper.Mzk1URThetaTransportActual
import tmp.sheaf.xif.paper.Mzk1URThetaHthetaActual
import tmp.sheaf.xif.paper.PaperLevelXiFTargetActual
import Mathlib.Tactic
noncomputable section
open scoped BigOperators
namespace LeanFormal.IUT.XiFPaper.R2FsideHperBActual
open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.Mzk1URRootExtensionActual
open LeanFormal.IUT.XiFPaper.Mzk1URRootExtInstancesActual
open LeanFormal.IUT.XiFPaper.Mzk1URThetaTransportActual
open LeanFormal.IUT.XiFPaper.Mzk1URThetaHthetaActual
open LeanFormal.IUT.XiFPaper.PaperLevelXiFTargetActual
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.VbadPlaceIndexingActual
open LeanFormal.IUT.XiFPaper.BadPlaceThetaHullCorrectionFormulaActual
open LeanFormal.IUT.XiFPaper.Mzk1UCC3ProducerActual
variable {l : PrimeGeFive} (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]
variable [∀ b : Bad (nativePlaceSelection T), MeasurableSpace (qVFamTensorBlock T b)]
variable [∀ b : Bad (nativePlaceSelection T), BorelSpace (qVFamTensorBlock T b)]

/-- Actual L_w/root datum: the actual local hull log equals the root log-norm. -/
structure ActualLwRootDatum (l : PrimeGeFive) (T : SourceNativeInitialThetaData l)
    [∀ b : Bad (nativePlaceSelection T), MeasurableSpace (qVFamTensorBlock T b)]
    [∀ b : Bad (nativePlaceSelection T), BorelSpace (qVFamTensorBlock T b)] : Prop where
  hull_eq_root : ∀ b : Bad (nativePlaceSelection T),
    actualLocalHullLog T b =
      Real.log ‖(urRootAlpha T b : urRootCarrier T b)‖

/-- The actual root packet bound for one b: root log-norm <= packet value. -/
def RootDatumPacketBound (l : PrimeGeFive) (T : SourceNativeInitialThetaData l)
    (packetV : Bad (nativePlaceSelection T) → Real) : Prop :=
  ∀ b, Real.log ‖(urRootAlpha T b : urRootCarrier T b)‖ ≤ packetV b

/-- F-side hperB from the actual L_w/root datum and the root packet bound. -/
theorem actualLwRootDatum_hperB
    (D : ActualLwRootDatum l T)
    (packetV : Bad (nativePlaceSelection T) → Real)
    (hroot : RootDatumPacketBound l T packetV) :
    actualThetaHullLogRoot T ≤
      ucWeightedHpkt (nativeBadLocalWeight T) packetV := by
  have halign : ∀ b, RootTensorVolumeAlignmentAt T b := by
    intro b
    unfold RootTensorVolumeAlignmentAt
    exact D.hull_eq_root b
  have hpacket : ∀ b, -thetaCoefficientContribution T b ≤ packetV b := by
    intro b
    rw [thetaCoeff_eq_neg_alpha_log]
    exact hroot b
  exact ur_htheta_of_alignment T halign packetV hpacket

#print axioms actualLwRootDatum_hperB
end LeanFormal.IUT.XiFPaper.R2FsideHperBActual