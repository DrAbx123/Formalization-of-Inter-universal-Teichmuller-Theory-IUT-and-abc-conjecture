import tmp.sheaf.xif.paper.S716PaperThetaHullLogSourceAuditActual
import tmp.sheaf.xif.paper.RootHullMeasureActual
import tmp.sheaf.xif.paper.SignedLabelOneActual

/-! # S726: PaperHullVsS663ThetaAverageGap is false

The paper per-b Theta hull log is the normalized log of the root hull, hence
nonpositive (the root hull is contained in the canonical unit reference).
The S663 positive theta magnitude average is strictly positive (the label-1
term is positive).  Therefore the gap equality can never hold; this is a
genuine negation, not a numerical l=29-only observation.
-/

noncomputable section
open scoped BigOperators
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 3000000

namespace LeanFormal.IUT.XiFPaper.S726PaperHullVsS663GapActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.S716PaperThetaHullLogSourceAuditActual
open LeanFormal.IUT.XiFPaper.PaperLevelXiFTargetProofActual
open LeanFormal.IUT.XiFPaper.RootHullMeasureActual
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.QPilotZeroLocusDivisorActual
open LeanFormal.IUT.XiFPaper.RootHullContainmentInequalityActual
open LeanFormal.IUT.XiFPaper.QVFamRootFactorCorrectionActual
open LeanFormal.IUT.XiFPaper.S657RootSignedHullIndependentActual
open LeanFormal.IUT.XiFPaper.SignedLabelOneActual
open MeasureTheory

universe u
variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]
variable [∀ b : Bad (nativePlaceSelection T), MeasurableSpace (qVFamTensorBlock T b)]
variable [∀ b : Bad (nativePlaceSelection T), BorelSpace (qVFamTensorBlock T b)]
variable (b : Bad (nativePlaceSelection T))

/-- The paper per-b Theta hull log is nonpositive. -/
theorem paperPerBThetaHullLog_nonpos :
    paperPerBThetaHullLog (l := l) T b ≤ 0 := by
  unfold paperPerBThetaHullLog perBThetaHullLog rootThetaHullLog
  rw [← arithmeticTupleNormalizedLogVolume_canonicalUnitReference
    (qVFamTensorPlaces T b) qVFamTensorTuple Measure.addHaar]
  apply arithmeticTupleNormalizedLogVolume_mono
  · exact rootNormHull_subset_holomorphic (l := l) T b
  · exact rootNormHull_measure_pos (l := l) T b Measure.addHaar
  · exact (measure_arithmeticTupleCanonicalRegions_pos_lt_top
      (qVFamTensorPlaces T b) qVFamTensorTuple Measure.addHaar).2.2

/-- The label-1 positive theta magnitude is strictly positive. -/
theorem rootThetaMagnitudeValue_one_pos :
    0 < rootThetaMagnitudeValue (l := l) T b (oneLabel l) := by
  unfold rootThetaMagnitudeValue
  apply mul_pos
  · apply Finset.sum_pos
    · intro i _
      unfold qVFamPaperThetaTensorCoefficient qVFamPaperRootCoefficient
      have hge : (0 : Real) < (gaussExponent (oneLabel l).1).toNat := by
        rw [gaussExponent_oneLabel]
        norm_num
      apply mul_pos
      · exact_mod_cast hge
      · apply div_pos
        · exact_mod_cast (qVFamily T b).order_pos
        · positivity
    · exact Finset.univ_nonempty
  · apply Real.log_pos
    exact_mod_cast (Fact.out : Nat.Prime (qVFamTensorP T b)).one_lt

/-- The S663 theta-average is strictly positive. -/
theorem rootThetaMagnitudeProcession_average_pos :
    0 < (rootThetaMagnitudeProcession T b).average := by
  rw [WeightedValues.average]
  rw [show (rootThetaMagnitudeProcession T b).weightTotal = 1 by rfl, div_one]
  change 0 < ∑ j : SignedLabel l.value,
    (Fintype.card (SignedLabel l.value) : Real)⁻¹ *
      rootThetaMagnitudeValue T b j
  apply Finset.sum_pos'
  · intro j _
    exact mul_nonneg (inv_nonneg.mpr (Nat.cast_nonneg _))
      (rootThetaMagnitudeValue_nonneg (l := l) T b j)
  · refine ⟨oneLabel l, Finset.mem_univ _, ?_⟩
    exact mul_pos (inv_pos.mpr (by exact_mod_cast Fintype.card_pos_iff.mpr ⟨oneLabel l⟩))
      (rootThetaMagnitudeValue_one_pos (l := l) T b)

/-- The S716 gap equality is false, for every l and b. -/
theorem paperHullVsS663ThetaAverageGap_false :
    ¬ PaperHullVsS663ThetaAverageGap (l := l) T b := by
  intro h
  unfold PaperHullVsS663ThetaAverageGap at h
  have hle : paperPerBThetaHullLog (l := l) T b ≤ 0 :=
    paperPerBThetaHullLog_nonpos (l := l) T b
  have hpos : 0 < (rootThetaMagnitudeProcession T b).average :=
    rootThetaMagnitudeProcession_average_pos (l := l) T b
  linarith

end LeanFormal.IUT.XiFPaper.S726PaperHullVsS663GapActual
end
