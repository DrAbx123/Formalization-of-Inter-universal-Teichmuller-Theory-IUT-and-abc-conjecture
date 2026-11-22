import tmp.sheaf.xif.paper.S2704S2696SourceDataActual
import tmp.sheaf.xif.paper.S3096S3097S3098AttemptActual
import tmp.sheaf.xif.paper.S1280SourceDefinition31Actual

noncomputable section
open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.XiFPaper.S2704S2696SourceDataActual
open LeanFormal.IUT.XiFPaper.S1280SourceDefinition31Actual
open LeanFormal.IUT.XiFPaper.S2696VbadActual
open LeanFormal.IUT.XiFPaper.S2697Gaussian2161Actual
open LeanFormal.IUT.XiFPaper.S3096S3097S3098AttemptActual
open LeanFormal.IUT.XiFPaper.S2678PaperUnconditionalHcompActual
set_option relaxedAutoImplicit false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 16000

namespace LeanFormal.IUT.XiFPaper.S3097SourceBadLabelInjectiveActualAdapted

variable (R : S1280RemainingClauses fiveLabel)
variable (redCompat : Prop) (hredCompat : redCompat)
variable (torCompat : Prop) (htorCompat : torCompat)
variable (orbCompat : Prop) (horbCompat : orbCompat)
variable (secCompat : Prop) (hsecCompat : secCompat)
variable (cusCompat : Prop) (hcusCompat : cusCompat)

abbrev S3097SourceData := S2696SourceData fiveLabel R redCompat hredCompat
  torCompat htorCompat orbCompat horbCompat secCompat hsecCompat cusCompat hcusCompat

theorem S3097_bad_eq_five_or_2161
    (b : Bad (S2696SelectionTwo fiveLabel)) :
    b = S2696BadFive fiveLabel ∨ b = S2696Bad2161 fiveLabel := by
  have hb : b.1 = S1280Place fiveLabel ∨
      b.1 = S2696Place2161Arith fiveLabel := by
    have hmem : b.1 ∈ S2696Vbad S2696TwoPlaceData := b.2
    rw [S2696Vbad_twoPlace_eq] at hmem
    rw [Set.mem_insert_iff, Set.mem_singleton_iff] at hmem
    simpa [S1280Place, S2696Place2161Arith] using hmem
  rcases hb with h | h
  · left; exact Subtype.ext h
  · right; exact Subtype.ext h

theorem S3097_badLabel_eq_residue
    (b : Bad (S2696SelectionTwo fiveLabel)) :
    (S3097SourceData R redCompat hredCompat torCompat htorCompat orbCompat
      horbCompat secCompat hsecCompat cusCompat hcusCompat).reduction.partition.badLabel b =
      NumberFieldFinitePlace.residueCharacteristic b.1 := by
  rw [S2696SourceData_reduction]
  simp [toSourceReductionClause, toSourcePlacePartition_badLabel, badResidueLabel]

theorem S3097_badLabel_injective :
    Function.Injective
      (S3097SourceData R redCompat hredCompat torCompat htorCompat orbCompat
        horbCompat secCompat hsecCompat cusCompat hcusCompat).reduction.partition.badLabel := by
  intro b1 b2 h
  have hlabel : ∀ b : Bad (S2696SelectionTwo fiveLabel),
      (S3097SourceData R redCompat hredCompat torCompat htorCompat orbCompat
        horbCompat secCompat hsecCompat cusCompat hcusCompat).reduction.partition.badLabel b =
      NumberFieldFinitePlace.residueCharacteristic b.1 :=
    fun b => S3097_badLabel_eq_residue R redCompat hredCompat torCompat htorCompat
      orbCompat horbCompat secCompat hsecCompat cusCompat hcusCompat b
  rw [hlabel b1, hlabel b2] at h
  rcases S3097_bad_eq_five_or_2161 b1 with rfl | rfl <;>
  rcases S3097_bad_eq_five_or_2161 b2 with rfl | rfl
  · rfl
  · exfalso
    have h5 : NumberFieldFinitePlace.residueCharacteristic
        (S2696BadFive fiveLabel).1 = 5 := by
      rw [show (S2696BadFive fiveLabel).1 = S1280Place fiveLabel from rfl,
        S1280Place_residueCharacteristic]
    have h2161 : NumberFieldFinitePlace.residueCharacteristic
        (S2696Bad2161 fiveLabel).1 = 2161 := by
      rw [show (S2696Bad2161 fiveLabel).1 = S2696Place2161Arith fiveLabel from rfl,
        S2696Place2161Arith_residueCharacteristic]
    rw [h5, h2161] at h
    norm_num at h
  · exfalso
    have h5 : NumberFieldFinitePlace.residueCharacteristic
        (S2696BadFive fiveLabel).1 = 5 := by
      rw [show (S2696BadFive fiveLabel).1 = S1280Place fiveLabel from rfl,
        S1280Place_residueCharacteristic]
    have h2161 : NumberFieldFinitePlace.residueCharacteristic
        (S2696Bad2161 fiveLabel).1 = 2161 := by
      rw [show (S2696Bad2161 fiveLabel).1 = S2696Place2161Arith fiveLabel from rfl,
        S2696Place2161Arith_residueCharacteristic]
    rw [h5, h2161] at h
    norm_num at h
  · rfl

theorem S3097_badIncluded_injective :
    Function.Injective
      (S3097SourceData R redCompat hredCompat torCompat htorCompat orbCompat
        horbCompat secCompat hsecCompat cusCompat hcusCompat).reduction.partition.badIncluded :=
  LeanFormal.IUT.XiFPaper.S3096S3097S3098AttemptActual.S3097_badIncluded_injective _
    (S3097_badLabel_injective R redCompat hredCompat
      torCompat htorCompat orbCompat horbCompat secCompat hsecCompat cusCompat hcusCompat)

#check S3097_badLabel_injective
#check S3097_badIncluded_injective
#print axioms S3097_badLabel_injective

end LeanFormal.IUT.XiFPaper.S3097SourceBadLabelInjectiveActualAdapted
end
