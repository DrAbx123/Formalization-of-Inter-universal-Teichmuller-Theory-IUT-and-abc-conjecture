import tmp.sheaf.xif.paper.S2675BadCardNoGoActual
import tmp.sheaf.xif.paper.S2681HcompBadQAlignmentActual
import tmp.sheaf.xif.paper.S2682HullNormalizationCorrectionActual

noncomputable section
open scoped BigOperators
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT.XiFPaper.S2684PaperNormalizationAuditActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.XiFPaper.S2675BadCardNoGoActual
open LeanFormal.IUT.XiFPaper.S1280SourceDefinition31Actual
open LeanFormal.IUT.XiFPaper.S1895OIdentificationsActual
open LeanFormal.IUT.XiFPaper.S2682HullNormalizationCorrectionActual
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction

universe u

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)

theorem S2684PaperInput_bad_card (D : S1895PaperInput) :
    Nat.card (S1895PaperInput.I D).initial.badPlaces = 1 :=
  S2675_paperInput_bad_card D

theorem S2684Alignment_nativeBad_card_eq_one
    (D : S1895PaperInput)
    (h : S2681BadQAlignment (I := S1895PaperInput.I D) T) :
    Nat.card (Bad (nativePlaceSelection T)) = 1 := by
  obtain ⟨e, _⟩ := h
  rw [← Nat.card_congr e]
  exact S2684PaperInput_bad_card D

theorem S2684CorrectedHull_gt_badQ
    (baseNormalization : Real) [Fintype (Bad (nativePlaceSelection T))]
    (hbase : 0 < baseNormalization) :
    S2682BadQCorrection T <
      S2682CorrectedHullNormalization T baseNormalization := by
  unfold S2682CorrectedHullNormalization S2682BadQCorrection
  linarith

theorem S2684CorrectedHull_sourceComparison_false
    (baseNormalization : Real) [Fintype (Bad (nativePlaceSelection T))]
    (hbase : 0 < baseNormalization) :
    ¬ (S2682CorrectedHullNormalization T baseNormalization ≤
        -(-(S2682BadQCorrection T))) := by
  unfold S2682CorrectedHullNormalization S2682BadQCorrection
  linarith

#check S2684PaperInput_bad_card
#check S2684Alignment_nativeBad_card_eq_one
#check S2684CorrectedHull_sourceComparison_false
#print axioms S2684PaperInput_bad_card
#print axioms S2684Alignment_nativeBad_card_eq_one
#print axioms S2684CorrectedHull_sourceComparison_false

end LeanFormal.IUT.XiFPaper.S2684PaperNormalizationAuditActual
end
