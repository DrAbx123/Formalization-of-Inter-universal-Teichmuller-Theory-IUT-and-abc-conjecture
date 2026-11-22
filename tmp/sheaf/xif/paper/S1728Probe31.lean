import tmp.sheaf.xif.paper.S1728CoverCategoryActual

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000

namespace ProbeModel2

open CategoryTheory
open LeanFormal.IUT.XiFPaper.S1728CoverCategoryActual
open LeanFormal.IUT.XiFPaper.S1728CoverCategoryActual.S1728Paper

noncomputable def SmallRawFamily (M : S1728SmallGaloisModel)
    (A B : S1728Cover) : Type :=
  @Quiver.Hom _ M.category.toQuiver (M.objEquiv.symm A) (M.objEquiv.symm B)

noncomputable def SmallRawEquiv (M : S1728SmallGaloisModel)
    (A B : S1728Cover) :
    SmallRawFamily M A B ≃ S1728CoverMap A B := by
  let a : M.SmallCover := M.objEquiv.symm A
  let b : M.SmallCover := M.objEquiv.symm B
  have hA : M.objEquiv a = A := M.objEquiv.apply_symm_apply A
  have hB : M.objEquiv b = B := M.objEquiv.apply_symm_apply B
  exact (M.homEquiv a b).trans (Equiv.cast (by rw [hA, hB]))

noncomputable def SmallRawData (M : S1728SmallGaloisModel)
    (A B : S1728Cover) : S1728ActualSmallRawCoverData A B where
  Carrier := SmallRawFamily M A B
  equiv := SmallRawEquiv M A B

theorem SmallRawRequired (M : S1728SmallGaloisModel) :
    S1728SmallRawCoverDataRequired :=
  fun A B => ⟨SmallRawData M A B⟩

noncomputable def ActualCategory01OfModel (M : S1728SmallGaloisModel) :
    Category.{0,1} S1728Cover :=
  S1728ActualCategory01 (SmallRawFamily M) (SmallRawEquiv M)

end ProbeModel2
