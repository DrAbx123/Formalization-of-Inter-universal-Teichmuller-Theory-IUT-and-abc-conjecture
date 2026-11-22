import tmp.sheaf.xif.paper.S1922IsoCommaCoherenceActual

noncomputable section
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 800000
open CategoryTheory
open CategoryTheory.Bicategory
open Iut
open LeanFormal.IUT.XiFPaper.S1726OrbicurveFPrimeActual
open LeanFormal.IUT.XiFPaper.S1728CoverCategoryActual
open LeanFormal.IUT.XiFPaper.S1728CoverCategoryActual.S1728Paper
open LeanFormal.IUT.XiFPaper.S1864GeneralPullbackStackActual
open LeanFormal.IUT.XiFPaper.S1890IsoCommaPseudofunctorActual

section
variable {A C : S1728Cover} (f : S1728CoverMap A C)
  {U V W : LocallyDiscrete (SchemeOverField S1726K)ᵒᵖ} (φ : U ⟶ V) (ψ : V ⟶ W)

#check natCompHomApp (F := A.source.fiber) (G := C.source.fiber) f.map φ ψ

example (x : ↥(A.source.fiber.obj U)) :
    (f.map.naturality (φ ≫ ψ)).hom.toNatTrans.app x =
      (f.map.app W).toFunctor.map ((A.source.fiber.mapComp φ ψ).hom.toNatTrans.app x) ≫
        (f.map.naturality ψ).hom.toNatTrans.app ((A.source.fiber.map φ).toFunctor.obj x) ≫
          (C.source.fiber.map ψ).toFunctor.map ((f.map.naturality φ).hom.toNatTrans.app x) ≫
            (C.source.fiber.mapComp φ ψ).inv.toNatTrans.app ((f.map.app U).toFunctor.obj x) := by
  rw [natCompHomApp]

example (x : ↥(A.source.fiber.obj U)) :
    (f.map.naturality (φ ≫ ψ)).hom.toNatTrans.app x =
      (f.map.app W).toFunctor.map ((A.source.fiber.mapComp φ ψ).hom.toNatTrans.app x) ≫
        (f.map.naturality ψ).hom.toNatTrans.app ((A.source.fiber.map φ).toFunctor.obj x) ≫
          (C.source.fiber.map ψ).toFunctor.map ((f.map.naturality φ).hom.toNatTrans.app x) ≫
            (C.source.fiber.mapComp φ ψ).inv.toNatTrans.app ((f.map.app U).toFunctor.obj x) :=
  natCompHomApp (F := A.source.fiber) (G := C.source.fiber) f.map φ ψ x

end

end
