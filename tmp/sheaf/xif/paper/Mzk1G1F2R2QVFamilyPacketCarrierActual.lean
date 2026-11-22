/- R2: PacketHullData instantiation on the one-factor qVFam tensor carrier.

The qVFam tensor carrier is definitionally the ArithmeticTensorTupleBlock with
ι := qVFamTensorV = Unit, V i = Unit, tuple i = (); hence the generic
PacketHullData applies and its carrier is qVFamTensorBlock T b by rfl.
No new data; no sorry. -/
import tmp.sheaf.xif.paper.Mzk1BoxReadoutLocalActual
import tmp.sheaf.xif.paper.QVFamTensorCoefficientActual
import tmp.sheaf.xif.paper.VbadPlaceIndexingActual
import Mathlib.Tactic
noncomputable section
set_option maxHeartbeats 4000000
namespace LeanFormal.IUT.XiFPaper.Mzk1G1F2R2QVFamilyPacketCarrierActual
open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.Mzk1BoxReadoutLocalActual
open MeasureTheory

variable {l : PrimeGeFive} (T : SourceNativeInitialThetaData.{0} l)
variable (b : Bad (nativePlaceSelection T))
variable [MeasurableSpace (qVFamTensorBlock (T := T) (b := b))]
variable [BorelSpace (qVFamTensorBlock (T := T) (b := b))]

/-- The actual one-factor qVFam PacketHullData (ι = qVFamTensorV = Unit, V i = Unit). -/
abbrev qVFamPacketHullData :=
  PacketHullData (K := T.arithmetic.F) (p := qVFamTensorP T b)
    (ι := qVFamTensorV) (V := fun _ => Unit)
    (qVFamTensorPlaces T b) (qVFamTensorTuple)
    (J := Unit)
    (E := fun _ => CommonPrimeCompletion (qVFamTensorPlaces T b ()))

/-- The generic PacketHullData carrier is exactly qVFamTensorBlock. -/
theorem qVFamPacketHullData_carrier_eq :
    ArithmeticTensorTupleBlock (qVFamTensorPlaces T b) qVFamTensorTuple =
      qVFamTensorBlock (T := T) (b := b) := rfl

end LeanFormal.IUT.XiFPaper.Mzk1G1F2R2QVFamilyPacketCarrierActual
end