import tmp.sheaf.xif.paper.S3069QPrimeTorsorStack

noncomputable section
open CategoryTheory
open LeanFormal.IUT
open Iut
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.XiFPaper.S3049TorsorFiberCategory
open LeanFormal.IUT.XiFPaper.S3069QPrimeTorsorStack
open LeanFormal.IUT.XiFPaper.S3048StackificationQPrime
open LeanFormal.IUT.XiFPaper.S2994A6Stackification
open LeanFormal.IUT.XiFPaper.S2882A6PointwisePseudofunctorActual
open LeanFormal.IUT.XiFPaper.S2847A6ArithmeticActual
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 0

namespace LeanFormal.IUT.XiFPaper.S3071TorsorGroupoid

/-- The inverse equivariant isomorphism. -/
noncomputable def S3071IsoInv
    (U : LocallyDiscrete (Iut.SchemeOverField S2994A6K)ᵒᵖ)
    {P Q : S3048SignTorsorFiber U} (f : S3049TorsorIso U P Q) :
    S3049TorsorIso U Q P :=
  haveI : IsIso f.hom := f.isIso
  { hom := CategoryTheory.inv f.hom
    comm := by
      haveI : IsIso f.hom := f.isIso
      calc
        CategoryTheory.inv f.hom ≫ P.projection
            = CategoryTheory.inv f.hom ≫ (f.hom ≫ Q.projection) := by
                rw [f.comm]
        _ = (CategoryTheory.inv f.hom ≫ f.hom) ≫ Q.projection := by
                rw [Category.assoc]
        _ = Q.projection := by
                rw [IsIso.inv_hom_id, Category.id_comp]
    equivariant := by
      intro g
      haveI : IsIso f.hom := f.isIso
      have h1 : CategoryTheory.inv f.hom ≫ P.action g ≫ f.hom =
          Q.action g := by
        calc
          CategoryTheory.inv f.hom ≫ P.action g ≫ f.hom
              = CategoryTheory.inv f.hom ≫ (P.action g ≫ f.hom) := rfl
          _ = CategoryTheory.inv f.hom ≫ (f.hom ≫ Q.action g) := by
                  rw [← f.equivariant g]
          _ = (CategoryTheory.inv f.hom ≫ f.hom) ≫ Q.action g := by
                  rw [Category.assoc]
          _ = Q.action g := by
                  rw [IsIso.inv_hom_id, Category.id_comp]
      calc
        CategoryTheory.inv f.hom ≫ P.action g
            = CategoryTheory.inv f.hom ≫ P.action g ≫ 𝟙 P.total := by simp
        _ = CategoryTheory.inv f.hom ≫ P.action g ≫ (f.hom ≫ CategoryTheory.inv f.hom) := by
                rw [IsIso.hom_inv_id]
        _ = (CategoryTheory.inv f.hom ≫ P.action g ≫ f.hom) ≫
              CategoryTheory.inv f.hom := by
                simp only [Category.assoc]
        _ = Q.action g ≫ CategoryTheory.inv f.hom := by rw [h1]
    isIso := by infer_instance }

/-- Actual Groupoid structure on the sign-torsor fiber. -/
noncomputable def S3071TorsorGroupoid
    (U : LocallyDiscrete (Iut.SchemeOverField S2994A6K)ᵒᵖ) :
    Groupoid (S3048SignTorsorFiber U) :=
  Groupoid.mk
    (fun {P Q} f => S3071IsoInv U f)
    (by
      intro P Q f
      haveI : IsIso f.hom := f.isIso
      apply S3049TorsorIso.ext
      simp only [S3071IsoInv, CategoryStruct.comp, CategoryStruct.id]
      exact IsIso.inv_hom_id f.hom)
    (by
      intro P Q f
      haveI : IsIso f.hom := f.isIso
      apply S3049TorsorIso.ext
      simp only [S3071IsoInv, CategoryStruct.comp, CategoryStruct.id]
      exact IsIso.hom_inv_id f.hom)

#check S3071IsoInv
#check S3071TorsorGroupoid
#print axioms S3071TorsorGroupoid

end LeanFormal.IUT.XiFPaper.S3071TorsorGroupoid
end
