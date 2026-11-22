/- K-side norm-order bridges for the actual packet (hperB), kurt lane.

Purpose: relate the KSide letters (ksCeilC, ksDifferentOrder) used inside urPacketV_K to the
local norm-order forms required by arithmeticTupleStepVPossibleImages_subset_endpoint:
  (1) localNormOrder p ((urCeilData T b).localGenerator ()) = urCeilC = ksCeilC;
  (2) localNormOrder p (arithmeticTupleLocalDifferent (ksPlaces T b) ksTuple i) = ksDifferentOrder.
No new hypotheses; all by unfolding the definitions.

Default heartbeats (parent packet file raises them).
-/
import tmp.sheaf.xif.paper.Mzk1URThetaKLowerCoreActual
import tmp.sheaf.xif.paper.Mzk1URThetaKSideActual
import tmp.sheaf.xif.paper.Mzk1URThetaKPacketActual
import LeanFormal.IUT.ABCBridge.Geometry.FinitePlaceStepVAssembly
import Mathlib.Tactic

noncomputable section
open scoped BigOperators

namespace LeanFormal.IUT.XiFPaper.Mzk1URPacketNormOrderBridgeActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.ABCBridge.Geometry
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.VbadPlaceIndexingActual
open LeanFormal.IUT.XiFPaper.Mzk1URThetaKLowerCoreActual
open LeanFormal.IUT.XiFPaper.Mzk1URThetaKSideActual

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]
variable [∀ b : Bad (nativePlaceSelection T), MeasurableSpace (ksBlock T b)]
variable [∀ b : Bad (nativePlaceSelection T), BorelSpace (ksBlock T b)]

/-- (1) localNormOrder of the ceiling generator equals urCeilC. -/
theorem localNormOrder_localGenerator (b : Bad (nativePlaceSelection T)) :
    LocalFieldLogarithm.localNormOrder
      (p := (completionRationalPrime (nativeBadToKPlace T b)).val)
      (urCeilGenerator (l := l) T b) = urCeilC (l := l) T b := by
  letI : Fact (Nat.Prime ((completionRationalPrime (nativeBadToKPlace T b)).val)) :=
    completionRationalPrime_fact (nativeBadToKPlace T b)
  exact localNormOrder_eq_of_norm_eq_rpow (urCeilGenerator_norm (l := l) T b)

/-- (1') urCeilC coincides with the KSide ceiling letter ksCeilC. -/
theorem urCeilC_eq_ksCeilC (b : Bad (nativePlaceSelection T)) :
    urCeilC (l := l) T b = ksCeilC (l := l) T b := rfl


/-- (2) localNormOrder of the tuple local different equals the KSide different letter. -/
theorem localNormOrder_arithTupleLocalDifferent (b : Bad (nativePlaceSelection T))
    (i : LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual.qVFamTensorV) :
    LocalFieldLogarithm.localNormOrder
      (p := (completionRationalPrime (nativeBadToKPlace T b)).val)
      (arithmeticTupleLocalDifferent (ksPlaces T b) ksTuple i) =
      ksDifferentOrder (l := l) T b := rfl

#print axioms localNormOrder_localGenerator
#print axioms urCeilC_eq_ksCeilC
#print axioms localNormOrder_arithTupleLocalDifferent

end LeanFormal.IUT.XiFPaper.Mzk1URPacketNormOrderBridgeActual
end