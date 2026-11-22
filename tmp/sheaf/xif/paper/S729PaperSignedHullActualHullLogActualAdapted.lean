import tmp.sheaf.xif.paper.S721ActualHullToPaperSignedHullActual
import tmp.sheaf.xif.paper.S662NormalizedHaarArbitraryAverageActual
import tmp.sheaf.xif.paper.S716PaperThetaHullLogSourceAuditActual
import tmp.sheaf.xif.paper.PaperLevelXiFTargetProofActual

-- S729: actual PaperSignedHull with signed log = perBThetaHullLog.
-- A is the actual arbitrary-average IQ interface; procession/hull are
-- constant magnitude -perBThetaHullLog.

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.XiFPaper.S729PaperSignedHullActualHullLogActualAdapted

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.S721ActualHullToPaperSignedHullActual
open LeanFormal.IUT.XiFPaper.S662NormalizedHaarArbitraryAverageActual
open LeanFormal.IUT.XiFPaper.S716PaperThetaHullLogSourceAuditActual
open LeanFormal.IUT.XiFPaper.PaperLevelXiFTargetProofActual
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open MeasureTheory
open scoped BigOperators

universe u

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable (b : Bad (nativePlaceSelection T))
variable [Fintype (Bad (nativePlaceSelection T))]
variable [∀ b : Bad (nativePlaceSelection T), MeasurableSpace (qVFamTensorBlock T b)]
variable [∀ b : Bad (nativePlaceSelection T), BorelSpace (qVFamTensorBlock T b)]

noncomputable def paperThetaProcession (A : Real) :
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

theorem paperThetaProcession_average (A : Real) :
    (paperThetaProcession (l := l) A).average = A := by
  unfold WeightedValues.average
  simp only [paperThetaProcession]
  rw [div_one]
  letI : Nonempty (SignedLabel l.value) :=
    ⟨SignedLabel.representative l (0 : Fl l.value)⟩
  rw [Finset.sum_const, nsmul_eq_mul, Finset.card_univ]
  have hcard : (Fintype.card (SignedLabel l.value) : Real) ≠ 0 := by
    exact_mod_cast (Fintype.card_pos_iff.mpr inferInstance).ne'
  rw [← mul_assoc, mul_inv_cancel₀ hcard, one_mul]

noncomputable def paperThetaFiniteHull (A : Real) :
    FiniteHull (SignedLabel l.value) where
  volume _ := A
  hullVolume := ∑ _ : SignedLabel l.value, |A|
  contains j := by
    calc A ≤ |A| := le_abs_self A
      _ ≤ ∑ _ : SignedLabel l.value, |A| := by
        exact Finset.single_le_sum (fun i _ => abs_nonneg A) (Finset.mem_univ j)

noncomputable def paperHullInterface (hA : 0 ≤ -paperPerBThetaHullLog (l := l) T b) :
    IQHullLogVolumeInterface (qVFamTensorBlock T b) :=
  arithmeticTupleIQHullLogVolumeInterface (qVFamTensorPlaces T b)
    qVFamTensorTuple
    (normalizedHaarMeasureFor (qVFamTensorPlaces T b) qVFamTensorTuple
      Measure.addHaar (-paperPerBThetaHullLog (l := l) T b))

theorem paperHullInterface_hnormal
    (hA : 0 ≤ -paperPerBThetaHullLog (l := l) T b) :
    (paperHullInterface (l := l) T b hA).logVolume
        (paperHullInterface (l := l) T b hA).hull =
      ENNReal.ofReal (-paperPerBThetaHullLog (l := l) T b) :=
  normalizedHaarMeasureFor_interface_hnormal
    (qVFamTensorPlaces T b) qVFamTensorTuple Measure.addHaar
    (-paperPerBThetaHullLog (l := l) T b) hA

noncomputable def paperSignedHullActual
    (hA : 0 ≤ -paperPerBThetaHullLog (l := l) T b) :
    PaperSignedHull (qVFamTensorBlock T b) (SignedLabel l.value) :=
  paperSignedHullOfActualHullLog (l := l) T b
    (paperHullInterface (l := l) T b hA)
    (paperThetaProcession (l := l) (-paperPerBThetaHullLog (l := l) T b))
    (paperThetaFiniteHull (l := l) (-paperPerBThetaHullLog (l := l) T b))
    (fun _ => rfl)
    (fun _ => inv_nonneg.mpr (Nat.cast_nonneg _))
    (by rw [paperThetaProcession_average]; exact hA)
    (paperThetaProcession_average (l := l) (-paperPerBThetaHullLog (l := l) T b))
    (paperHullInterface_hnormal (l := l) T b hA)

theorem paperSignedHullActual_signed
    (hA : 0 ≤ -paperPerBThetaHullLog (l := l) T b) :
    (paperSignedHullActual (l := l) T b hA).signedHullLogVolume =
      perBThetaHullLog (l := l) T b :=
  paperSignedHullOfActualHullLog_signed_eq (l := l) T b
    (paperHullInterface (l := l) T b hA)
    (paperThetaProcession (l := l) (-paperPerBThetaHullLog (l := l) T b))
    (paperThetaFiniteHull (l := l) (-paperPerBThetaHullLog (l := l) T b))
    (fun _ => rfl)
    (fun _ => inv_nonneg.mpr (Nat.cast_nonneg _))
    (by rw [paperThetaProcession_average]; exact hA)
    (paperThetaProcession_average (l := l) (-paperPerBThetaHullLog (l := l) T b))
    (paperHullInterface_hnormal (l := l) T b hA)

#check paperSignedHullActual
#check paperSignedHullActual_signed

end LeanFormal.IUT.XiFPaper.S729PaperSignedHullActualHullLogActualAdapted

end