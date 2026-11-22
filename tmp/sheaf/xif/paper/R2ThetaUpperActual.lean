/- R2 Θ-upper (`R2ThetaUpperActual`): ν(Θ) <= H with the real per-label row average,
  per route §4.1/4.2.  NO union-hull average shortcut: the comparison is done per bad place
  `b` between the paper Θ readout `Θ_b` and the real procession row average
  `avg_j V_bj = (1/card) sum_j ν(H_bj)`, then summed with the actual weights
  `thetaLamWeight_b`.  The per-b input `hperB : Θ_b <= avg_j V_bj` is exactly route §4.2
  step 3/5 (real P5 source map / transport); it is kept as an explicit hypothesis here and
  is NOT derived from a union-average shortcut.

  H_bj is the actual per-label row region `ksThetaRegion T b j` (K-side carrier);
  Θ_b is the actual paper Θ readout `paperThetaReadoutB` (F-side rootNormHull volume).
  The two carriers are NOT identified (no transport map exists in the tree); hence the
  per-b comparison is the named missing input, not faked.
  No equality, no stub, no sorry/axiom. -/
import tmp.sheaf.xif.paper.Mzk1BoxR2PaperThetaLeHActual
import tmp.sheaf.xif.paper.Mzk1URThetaKSideActual
import LeanFormal.IUT.ABCBridge.Geometry.FinitePlaceNormalizedUnitScalingLogVolume
import Mathlib.Tactic

noncomputable section
set_option maxHeartbeats 2000000
open scoped BigOperators
open MeasureTheory
namespace LeanFormal.IUT.XiFPaper.R2ThetaUpperActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.VbadPlaceIndexingActual
open LeanFormal.IUT.XiFPaper.Mzk1URThetaKSideActual
open LeanFormal.IUT.XiFPaper.Mzk1BoxR2PaperThetaLeHActual

variable {l : PrimeGeFive} (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]
variable [Fintype (SignedLabel l.value)]
variable [∀ b : Bad (nativePlaceSelection T), MeasurableSpace (ksBlock T b)]
variable [∀ b : Bad (nativePlaceSelection T), BorelSpace (ksBlock T b)]

/-- The actual per-label row region H_bj (real procession index (b,j)). -/
noncomputable def rowRegionH (b : Bad (nativePlaceSelection T))
    (j : SignedLabel l.value) : Set (ksBlock T b) :=
  ksThetaRegion (l := l) T b j

/-- The actual row volume V_bj = nu(H_bj). -/
noncomputable def rowVH (b : Bad (nativePlaceSelection T))
    (j : SignedLabel l.value) : ℝ :=
  arithmeticTupleNormalizedLogVolume (ksPlaces T b) ksTuple
    Measure.addHaar (rowRegionH (l := l) T b j)

/-- The real procession row average `avg_j V_bj`. -/
noncomputable def rowAvgH (b : Bad (nativePlaceSelection T)) : ℝ :=
  (∑ j : SignedLabel l.value, rowVH (l := l) T b j) /
    (Fintype.card (SignedLabel l.value) : ℝ)

/-- The real procession readout `H = sum_b thetaLamWeight_b * avg_j V_bj`. -/
noncomputable def HProcessionTheta : ℝ :=
  ∑ b : Bad (nativePlaceSelection T), thetaLamWeight (l := l) T b * rowAvgH (l := l) T b

theorem HProcessionTheta_eq :
    HProcessionTheta (l := l) T =
      ∑ b : Bad (nativePlaceSelection T),
        thetaLamWeight (l := l) T b * rowAvgH (l := l) T b := rfl

/-- **Per-b Θ <= row average** (route §4.2 steps 3+5: real source map/transport).
    This is the named missing input; it is NOT a union-average shortcut. -/
theorem theta_le_rowAvg_of_transport
    (hperB : ∀ b : Bad (nativePlaceSelection T),
      paperThetaReadoutB (l := l) T b ≤ rowAvgH (l := l) T b) :
    ∀ b : Bad (nativePlaceSelection T),
      paperThetaReadoutB (l := l) T b ≤ rowAvgH (l := l) T b := hperB

/-- **ν(Θ) <= H**: weighted sum of the per-b comparisons (no union-average shortcut; the
    summation is over bad places with the actual paper weights). -/
theorem paperTheta_le_HProcession
    (hperB : ∀ b : Bad (nativePlaceSelection T),
      paperThetaReadoutB (l := l) T b ≤ rowAvgH (l := l) T b) :
    (∑ b : Bad (nativePlaceSelection T),
        thetaLamWeight (l := l) T b * paperThetaReadoutB (l := l) T b) ≤ HProcessionTheta (l := l) T := by
  unfold HProcessionTheta
  apply Finset.sum_le_sum
  intro b _
  exact mul_le_mul_of_nonneg_left (hperB b) (thetaLamWeight_nonneg (l := l) T b)

#print axioms HProcessionTheta_eq
#print axioms paperTheta_le_HProcession

end LeanFormal.IUT.XiFPaper.R2ThetaUpperActual
