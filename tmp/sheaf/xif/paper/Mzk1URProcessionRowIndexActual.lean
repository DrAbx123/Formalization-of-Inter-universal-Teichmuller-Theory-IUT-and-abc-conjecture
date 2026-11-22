/- R2 real procession index and row identity (kurt).

Real index: (b, j) with b a bad place and j a signed procession label; slot data are carried by
`ksThetaRegion T b j` (the actual per-label row region H_bj).  Row volume and average:
  V_bj := nu(H_bj),   avg_j V_bj := (1/card) * Sum_j V_bj,
  H := Sum_b thetaLamWeight_b * avg_j V_bj.
`H_eq_weighted_average` is the requested H identity (definitional, no equality assumption).
-/
import tmp.sheaf.xif.paper.Mzk1URThetaKSideActual
import LeanFormal.IUT.ABCBridge.Geometry.FinitePlaceNormalizedUnitScalingLogVolume
import Mathlib.Tactic

set_option maxHeartbeats 8000000
noncomputable section
open scoped BigOperators
open MeasureTheory

namespace LeanFormal.IUT.XiFPaper.Mzk1URProcessionRowIndexActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.Mzk1URThetaKSideActual

variable {l : PrimeGeFive} (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]
variable [Fintype (SignedLabel l.value)]
variable [∀ b : Bad (nativePlaceSelection T), MeasurableSpace (ksBlock T b)]
variable [∀ b : Bad (nativePlaceSelection T), BorelSpace (ksBlock T b)]

/-- The actual row region H_bj at the real procession index (b,j). -/
noncomputable def rowRegion (b : Bad (nativePlaceSelection T)) (j : SignedLabel l.value) :
    Set (ksBlock T b) :=
  ksThetaRegion (l := l) T b j

/-- The actual row volume V_bj = nu(H_bj). -/
noncomputable def rowV (b : Bad (nativePlaceSelection T)) (j : SignedLabel l.value) : ℝ :=
  arithmeticTupleNormalizedLogVolume (ksPlaces T b) ksTuple
    MeasureTheory.Measure.addHaar (rowRegion (l := l) T b j)

/-- The real procession average over the labels at b: avg_j V_bj. -/
noncomputable def rowAvg (b : Bad (nativePlaceSelection T)) : ℝ :=
  (∑ j : SignedLabel l.value, rowV (l := l) T b j) /
    (Fintype.card (SignedLabel l.value) : ℝ)

/-- The actual procession readout H = Sum_b thetaLamWeight_b * avg_j V_bj. -/
noncomputable def HProcession : ℝ :=
  ∑ b : Bad (nativePlaceSelection T), thetaLamWeight (l := l) T b * rowAvg (l := l) T b

/-- H identity: H is exactly the weighted average of the actual row volumes. -/
theorem H_eq_weighted_average :
    HProcession (l := l) T =
      ∑ b : Bad (nativePlaceSelection T),
        thetaLamWeight (l := l) T b * rowAvg (l := l) T b := rfl

/-- Row-average identity: avg_j V_bj = (1/card) * Sum_j V_bj. -/
theorem rowAvg_eq :
    ∀ b : Bad (nativePlaceSelection T),
      rowAvg (l := l) T b =
        (∑ j : SignedLabel l.value, rowV (l := l) T b j) /
          (Fintype.card (SignedLabel l.value) : ℝ) := fun _ => rfl

end LeanFormal.IUT.XiFPaper.Mzk1URProcessionRowIndexActual
end