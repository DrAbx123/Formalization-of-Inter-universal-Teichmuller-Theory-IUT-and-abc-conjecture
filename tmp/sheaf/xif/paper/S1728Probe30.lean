import tmp.sheaf.xif.paper.S1728CoverCategoryActual

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000

namespace ProbeModel

open CategoryTheory
open LeanFormal.IUT.XiFPaper.S1728CoverCategoryActual
open LeanFormal.IUT.XiFPaper.S1728CoverCategoryActual.S1728Paper

example (M : S1728SmallGaloisModel) (A B : S1728Cover) :
    S1728ActualSmallRawCoverData A B := by
  let a : M.SmallCover := M.objEquiv.symm A
  let b : M.SmallCover := M.objEquiv.symm B
  have hA : M.objEquiv a = A := M.objEquiv.apply_symm_apply A
  have hB : M.objEquiv b = B := M.objEquiv.apply_symm_apply B
  refine
    { Carrier := @Quiver.Hom _ M.category.toQuiver a b
      equiv := ?_ }
  exact (M.homEquiv a b).trans
    (Equiv.cast (by rw [hA, hB]))

end ProbeModel
