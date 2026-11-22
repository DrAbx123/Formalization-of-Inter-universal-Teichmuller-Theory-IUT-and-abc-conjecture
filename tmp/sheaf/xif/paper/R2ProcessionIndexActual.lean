/- R2 real procession index (kurt, owner R2ProcessionIndexActual).

Per handoff §4: fix p; E_p = the bad places at p; lambda_v the local weights; n = (l-1)/2;
labels j = 1..n; a slot map t : Fin (j+1) -> E_p with product weight W(t) = prod_i lambda_{t i};
the distinguished slot is Fin.last j.  Row region H_bj and row volume V_bj = nu(H_bj) are actual.
-/
import tmp.sheaf.xif.paper.Mzk1URThetaKSideActual
import LeanFormal.IUT.ABCBridge.Geometry.FinitePlaceNormalizedUnitScalingLogVolume
import Mathlib.Tactic

set_option maxHeartbeats 8000000
noncomputable section
open scoped BigOperators
open MeasureTheory

namespace LeanFormal.IUT.XiFPaper.R2ProcessionIndexActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.Mzk1URThetaKSideActual

variable {l : PrimeGeFive} (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))] [Nonempty (Bad (nativePlaceSelection T))]
variable [Fintype (SignedLabel l.value)]
variable [∀ b : Bad (nativePlaceSelection T), MeasurableSpace (ksBlock T b)]
variable [∀ b : Bad (nativePlaceSelection T), BorelSpace (ksBlock T b)]

/-- The procession place set E_p at fixed p (from the bad places). -/
abbrev EPlace := Bad (nativePlaceSelection T)

/-- The local weight lambda_v at v in E_p. -/
noncomputable def lamE (v : EPlace (T := T)) : ℝ := lamWeight (l := l) T v

/-- n = (l-1)/2, the Gaussian label bound. -/
def processN : ℕ := (l.value - 1) / 2

/-- The real row region H_bj at bad place b and label j (the actual K-side theta row). -/
noncomputable def rowRegion (b : EPlace (T := T)) (j : SignedLabel l.value) :
    Set (ksBlock T b) :=
  ksThetaRegion (l := l) T b j

/-- The real row volume V_bj = nu(H_bj). -/
noncomputable def rowV (b : EPlace (T := T)) (j : SignedLabel l.value) : ℝ :=
  arithmeticTupleNormalizedLogVolume (ksPlaces T b) ksTuple
    MeasureTheory.Measure.addHaar (rowRegion (l := l) T b j)

/-- The slot weight W(t) = prod_i lambda_{t i}. -/
noncomputable def slotW {j : ℕ} (t : Fin (j + 1) → EPlace (T := T)) : ℝ :=
  ∑ _i : Fin (j + 1), (0 : ℝ) + (∏ i, lamE (T := T) (t i)) - (∑ _i : Fin (j + 1), (0 : ℝ))

/-- Clean form of the slot weight. -/
theorem slotW_eq {j : ℕ} (t : Fin (j + 1) → EPlace (T := T)) :
    slotW (T := T) t = ∏ i, lamE (T := T) (t i) := by
  unfold slotW
  ring

/-- The distinguished slot Fin.last j. -/
def distinguishedSlot (j : ℕ) : Fin (j + 1) := Fin.last j

/-- Real row volume at the distinguished slot of a tuple t, at label jlab. -/
noncomputable def distRowV {j : ℕ} (t : Fin (j + 1) → EPlace (T := T))
    (jlab : SignedLabel l.value) : ℝ :=
  rowV (T := T) (b := t (distinguishedSlot j)) jlab


/-- The real procession readout H = Sum_b thetaLamWeight_b * (1/card) Sum_j V_bj. -/
noncomputable def HProcession : ℝ :=
  ∑ b : EPlace (T := T), thetaLamWeight (l := l) T b *
    ((∑ j : SignedLabel l.value, rowV (l := l) T b j) /
      (Fintype.card (SignedLabel l.value) : ℝ))

/-- H identity: H is the weighted average of the real row volumes. -/
theorem H_eq_weighted_average :
    HProcession (l := l) T =
      ∑ b : EPlace (T := T), thetaLamWeight (l := l) T b *
        ((∑ j : SignedLabel l.value, rowV (l := l) T b j) /
          (Fintype.card (SignedLabel l.value) : ℝ)) := rfl

/-- Row volume identity V_bj = nu(ksThetaRegion T b j). -/
theorem rowV_eq (b : EPlace (T := T)) (j : SignedLabel l.value) :
    rowV (l := l) T b j =
      arithmeticTupleNormalizedLogVolume (ksPlaces T b) ksTuple
        MeasureTheory.Measure.addHaar (ksThetaRegion (l := l) T b j) := rfl

/-- Distinguished-slot row volume is the row volume at the tuple's last place. -/
theorem distRowV_eq {j : ℕ} (t : Fin (j + 1) → EPlace (T := T))
    (jlab : SignedLabel l.value) :
    distRowV (l := l) T t jlab =
      rowV (l := l) T (t (distinguishedSlot j)) jlab := rfl


end LeanFormal.IUT.XiFPaper.R2ProcessionIndexActual
end