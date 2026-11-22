import tmp.sheaf.xif.paper.S721ActualHullToPaperSignedHullActual
import tmp.sheaf.xif.paper.S662NormalizedHaarArbitraryAverageActual
import tmp.sheaf.xif.paper.BadPlacePaperRootThetaHullActual
import tmp.sheaf.xif.paper.S716PaperThetaHullLogSourceAuditActual

-- S743: paper-order PaperSignedHull.  L := paperRootThetaHullLog (paper
-- order/(2l)) and the actual A has hull log = ofReal(-L).
-- Signed log = L = - paperOrderThetaHullMagnitude.

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.XiFPaper.S743PaperSignedHullPaperOrderActualAdapted

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.S721ActualHullToPaperSignedHullActual
open LeanFormal.IUT.XiFPaper.S662NormalizedHaarArbitraryAverageActual
open LeanFormal.IUT.XiFPaper.BadPlacePaperRootThetaHullActual
open LeanFormal.IUT.XiFPaper.S716PaperThetaHullLogSourceAuditActual
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open MeasureTheory
open scoped BigOperators

universe u

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]
variable [∀ b : Bad (nativePlaceSelection T), MeasurableSpace (qVFamTensorBlock T b)]
variable [∀ b : Bad (nativePlaceSelection T), BorelSpace (qVFamTensorBlock T b)]
variable (b : Bad (nativePlaceSelection T))

/-- Paper-order Θ hull log at b: paper coefficient order(q_v)/(2l). -/
noncomputable def paperOrderThetaHullLog : Real :=
  paperRootThetaHullLog (l := l) T b Measure.addHaar

/-- The positive paper-order Θ hull magnitude. -/
noncomputable def paperOrderThetaHullMagnitude : Real :=
  -paperOrderThetaHullLog (l := l) T b

/-- Constant paper-order procession at magnitude A. -/
noncomputable def paperOrderProcession (A : Real) :
    WeightedValues (SignedLabel l.value) where
  value _ := A
  weight _ := (Fintype.card (SignedLabel l.value) : Real)⁻¹
  weightTotal := 1
  weightTotal_pos := by norm_num
  weightTotal_eq_sum := by
    letI : Nonempty (SignedLabel l.value) :=
      ⟨SignedLabel.representative l (0 : Fl l.value)⟩
    rw [Finset.sum_const, nsmul_eq_mul, Finset.card_univ]
    have hcard : (Fintype.card (SignedLabel l.value) : Real) ≠ 0 := by
      exact_mod_cast (Fintype.card_pos_iff.mpr inferInstance).ne'
    exact (mul_inv_cancel₀ hcard).symm

theorem paperOrderProcession_average (A : Real) :
    (paperOrderProcession (l := l) A).average = A := by
  unfold WeightedValues.average
  simp only [paperOrderProcession]
  rw [div_one]
  letI : Nonempty (SignedLabel l.value) :=
    ⟨SignedLabel.representative l (0 : Fl l.value)⟩
  rw [Finset.sum_const, nsmul_eq_mul, Finset.card_univ]
  have hcard : (Fintype.card (SignedLabel l.value) : Real) ≠ 0 := by
    exact_mod_cast (Fintype.card_pos_iff.mpr inferInstance).ne'
  rw [← mul_assoc, mul_inv_cancel₀ hcard, one_mul]

noncomputable def paperOrderFiniteHull (A : Real) :
    FiniteHull (SignedLabel l.value) where
  volume _ := A
  hullVolume := ∑ _ : SignedLabel l.value, |A|
  contains j := by
    calc A ≤ |A| := le_abs_self A
      _ ≤ ∑ _ : SignedLabel l.value, |A| := by
        exact Finset.single_le_sum (fun i _ => abs_nonneg A) (Finset.mem_univ j)

noncomputable def paperOrderHullInterface
    (hM : 0 ≤ paperOrderThetaHullMagnitude (l := l) T b) :
    IQHullLogVolumeInterface (qVFamTensorBlock T b) :=
  arithmeticTupleIQHullLogVolumeInterface (qVFamTensorPlaces T b) qVFamTensorTuple
    (normalizedHaarMeasureFor (qVFamTensorPlaces T b) qVFamTensorTuple
      Measure.addHaar (paperOrderThetaHullMagnitude (l := l) T b))

theorem paperOrderHullInterface_hnormal
    (hM : 0 ≤ paperOrderThetaHullMagnitude (l := l) T b) :
    (paperOrderHullInterface (l := l) T b hM).logVolume
        (paperOrderHullInterface (l := l) T b hM).hull =
      ENNReal.ofReal (paperOrderThetaHullMagnitude (l := l) T b) :=
  normalizedHaarMeasureFor_interface_hnormal
    (qVFamTensorPlaces T b) qVFamTensorTuple Measure.addHaar
    (paperOrderThetaHullMagnitude (l := l) T b) hM

noncomputable def paperSignedHullOfLog
    (A : IQHullLogVolumeInterface (qVFamTensorBlock T b)) (L : Real)
    (procession : WeightedValues (SignedLabel l.value))
    (finiteHull : FiniteHull (SignedLabel l.value))
    (hmatches : ∀ i, procession.value i = finiteHull.volume i)
    (hweights : ∀ i, 0 <= procession.weight i)
    (havg : 0 <= procession.average)
    (havg_eq : procession.average = -L)
    (hnormal : A.logVolume A.hull = ENNReal.ofReal (-L)) :
    PaperSignedHull (qVFamTensorBlock T b) (SignedLabel l.value) where
  ambient := A
  procession := procession
  hull := finiteHull
  weighted_matches_hull := hmatches
  weights_nonnegative := hweights
  average_nonneg := havg
  hull_logVolume_eq_average := by
    rw [havg_eq]
    exact hnormal

theorem paperSignedHullOfLog_signed
    (A : IQHullLogVolumeInterface (qVFamTensorBlock T b)) (L : Real)
    (procession : WeightedValues (SignedLabel l.value))
    (finiteHull : FiniteHull (SignedLabel l.value))
    (hmatches : ∀ i, procession.value i = finiteHull.volume i)
    (hweights : ∀ i, 0 <= procession.weight i)
    (havg : 0 <= procession.average)
    (havg_eq : procession.average = -L)
    (hnormal : A.logVolume A.hull = ENNReal.ofReal (-L)) :
    (paperSignedHullOfLog (l := l) T b A L procession finiteHull hmatches
      hweights havg havg_eq hnormal).signedHullLogVolume = L := by
  unfold PaperSignedHull.signedHullLogVolume paperSignedHullOfLog
  change -((A.logVolume A.hull).toReal) = L
  rw [hnormal]
  have hnon : 0 <= -L := by
    rw [← havg_eq]
    exact havg
  rw [ENNReal.toReal_ofReal hnon]
  ring

noncomputable def paperSignedHullPaperOrder
    (hM : 0 ≤ paperOrderThetaHullMagnitude (l := l) T b) :
    PaperSignedHull (qVFamTensorBlock T b) (SignedLabel l.value) :=
  paperSignedHullOfLog (l := l) T b
    (paperOrderHullInterface (l := l) T b hM)
    (paperOrderThetaHullLog (l := l) T b)
    (paperOrderProcession (l := l) (paperOrderThetaHullMagnitude (l := l) T b))
    (paperOrderFiniteHull (l := l) (paperOrderThetaHullMagnitude (l := l) T b))
    (fun _ => rfl)
    (fun _ => inv_nonneg.mpr (Nat.cast_nonneg _))
    hM
    (paperOrderProcession_average (l := l)
      (paperOrderThetaHullMagnitude (l := l) T b))
    (paperOrderHullInterface_hnormal (l := l) T b hM)

theorem paperSignedHullPaperOrder_signed
    (hM : 0 ≤ paperOrderThetaHullMagnitude (l := l) T b) :
    (paperSignedHullPaperOrder (l := l) T b hM).signedHullLogVolume =
      paperOrderThetaHullLog (l := l) T b :=
  paperSignedHullOfLog_signed (l := l) T b
    (paperOrderHullInterface (l := l) T b hM)
    (paperOrderThetaHullLog (l := l) T b)
    (paperOrderProcession (l := l) (paperOrderThetaHullMagnitude (l := l) T b))
    (paperOrderFiniteHull (l := l) (paperOrderThetaHullMagnitude (l := l) T b))
    (fun _ => rfl)
    (fun _ => inv_nonneg.mpr (Nat.cast_nonneg _))
    hM
    (paperOrderProcession_average (l := l)
      (paperOrderThetaHullMagnitude (l := l) T b))
    (paperOrderHullInterface_hnormal (l := l) T b hM)

theorem paperSignedHullPaperOrder_signed_magnitude
    (hM : 0 ≤ paperOrderThetaHullMagnitude (l := l) T b) :
    (paperSignedHullPaperOrder (l := l) T b hM).signedHullLogVolume =
      -paperOrderThetaHullMagnitude (l := l) T b := by
  rw [paperSignedHullPaperOrder_signed]
  rfl

def PaperOrderMagnitudeNonneg : Prop :=
  0 ≤ paperOrderThetaHullMagnitude (l := l) T b

#check paperSignedHullPaperOrder
#check paperSignedHullPaperOrder_signed
#check PaperOrderMagnitudeNonneg

end LeanFormal.IUT.XiFPaper.S743PaperSignedHullPaperOrderActualAdapted

end