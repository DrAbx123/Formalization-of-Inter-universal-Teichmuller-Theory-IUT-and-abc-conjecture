import tmp.sheaf.xif.paper.S2708MultiQSourcePilotActual
import tmp.sheaf.xif.paper.S2706DirectHcompActual
import tmp.sheaf.xif.paper.S2710GaussianResidueDegreeActual
import tmp.sheaf.xif.paper.S2710PerPlaceLogEqActual
import tmp.sheaf.xif.paper.S2704S2696SourceDataActual
import tmp.sheaf.xif.PaperQPilotObject
import LeanFormal.IUT.IUTIII.Corollary312.ArithmeticQPilotBaseChange

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 8000000

namespace LeanFormal.IUT.XiFPaper.S2712MultiQDonorActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.ArithmeticQPilotBaseChange
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.XiFPaper
open LeanFormal.IUT.XiFPaper.S1280SourceDefinition31Actual
open LeanFormal.IUT.XiFPaper.S2696VbadActual
open LeanFormal.IUT.XiFPaper.S2704S2696SourceDataActual
open LeanFormal.IUT.XiFPaper.S2706DirectHcompActual
open LeanFormal.IUT.XiFPaper.S2708MultiQSourcePilotActual
open LeanFormal.IUT.XiFPaper.S2710GaussianResidueDegreeActual
open LeanFormal.IUT.XiFPaper.S2710PerPlaceLogEqActual

local instance : Fact (Irreducible (Polynomial.X ^ 2 - Polynomial.C (-1) : Polynomial ℚ)) :=
  ⟨gaussianPolynomial_irreducible⟩

theorem S2712_sectionFiniteLift_eq_self (l : PrimeGeFive)
    (b : Bad (S2696SelectionTwo l)) :
    sectionFiniteLift (S2696SelectionTwo l) b.1 = b.1 := by
  have h := sectionFiniteLift_comap (P := S2696SelectionTwo l) b.1
  have h2 := S1280_comap_eq_self l (sectionFiniteLift (S2696SelectionTwo l) b.1)
  exact h2.symm.trans h

theorem S2712_badPlace_eq_five_or_2161 (l : PrimeGeFive)
    (b : Bad (S2696SelectionTwo l)) :
    (b.1 : NumberField.FinitePlace GaussianField) = concreteGaussianFivePlace ∨
      (b.1 : NumberField.FinitePlace GaussianField) = S2696GaussianPlace2161 := by
  have hb := b.2
  change (b.1 : NumberField.FinitePlace GaussianField) ∈
    S2696Vbad S2696TwoPlaceData at hb
  simp only [S2696Vbad, S2696TwoPlaceData, Set.mem_setOf_eq] at hb
  rcases hb with h | h | h | h
  · exact Or.inl h
  · exact Or.inl h
  · exact Or.inr h
  · exact Or.inr h

theorem S2712_residueNormBase_sectionFiniteLift (l : PrimeGeFive)
    (b : Bad (S2696SelectionTwo l)) :
    residueNormBase (sectionFiniteLift (S2696SelectionTwo l) b.1) =
      (NumberFieldFinitePlace.residueCharacteristic b.1 : ℝ) := by
  rw [S2712_sectionFiniteLift_eq_self]
  rcases S2712_badPlace_eq_five_or_2161 l b with h | h
  · rw [h]; exact S2710_residueNormBase_eq_residueCharacteristic_five
  · rw [h]; exact S2710_residueNormBase_eq_residueCharacteristic_2161

noncomputable def S2712MultiQDonor
    (R : S1280RemainingClauses fiveLabel)
    (redCompat : Prop) (hredCompat : redCompat)
    (torCompat : Prop) (htorCompat : torCompat)
    (orbCompat : Prop) (horbCompat : orbCompat)
    (secCompat : Prop) (hsecCompat : secCompat)
    (cusCompat : Prop) (hcusCompat : cusCompat) :
    MultiQSourcePilotData
      (I := S2706I (l := fiveLabel) R redCompat hredCompat torCompat htorCompat
        orbCompat horbCompat secCompat hsecCompat cusCompat hcusCompat) where
  index := Bad (S2696SelectionTwo fiveLabel)
  fintype := S2696BadFintype fiveLabel
  place := fun b => sectionFiniteLift (S2696SelectionTwo fiveLabel) b.1
  q := fun b => badPlaceQCandidate (S2696SelectionTwo fiveLabel) b
  logVolume := sourceBadQAbsLog
    (S2706SourceData (l := fiveLabel) R redCompat hredCompat torCompat htorCompat
      orbCompat horbCompat secCompat hsecCompat cusCompat hcusCompat)
  logVolume_eq := by
    classical
    letI : Fintype (Bad (S2696SelectionTwo fiveLabel)) := S2696BadFintype fiveLabel
    rw [S2696SourceData_sourceBadQAbsLog_eq_sum]
    refine Finset.sum_congr rfl ?_
    intro b _
    exact (S2710_localLog_eq_abs_log_proxy
      (P := S2696SelectionTwo fiveLabel) b
      (place := sectionFiniteLift (S2696SelectionTwo fiveLabel) b.1)
      (q := badPlaceQCandidate (S2696SelectionTwo fiveLabel) b) rfl
      (S2712_residueNormBase_sectionFiniteLift fiveLabel b)).symm
  logVolume_eq_source := rfl

#check S2712MultiQDonor
#check S2712_residueNormBase_sectionFiniteLift
#print axioms S2712MultiQDonor
end LeanFormal.IUT.XiFPaper.S2712MultiQDonorActual
end
