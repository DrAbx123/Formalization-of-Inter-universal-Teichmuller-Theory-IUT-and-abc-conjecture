import tmp.sheaf.xif.paper.S3076QPrimeNatIsoActual
noncomputable section
open CategoryTheory
open CategoryTheory.Limits
open LeanFormal.IUT
open Iut
open LeanFormal.IUT.XiFPaper.S3069QPrimeTorsorStack
open LeanFormal.IUT.XiFPaper.S3049TorsorFiberCategory
open LeanFormal.IUT.XiFPaper.S3073TorsorPullbackActual
open LeanFormal.IUT.XiFPaper.S3048StackificationQPrime
open LeanFormal.IUT.XiFPaper.S3076QPrimeNatIsoActual
namespace LeanFormal.IUT.XiFPaper.S3076MapIdObjHelper
set_option backward.isDefEq.respectTransparency false

variable {U : LocallyDiscrete (Iut.SchemeOverField S2994A6Stackification.S2994A6K)ᵒᵖ}
variable (P : S3048SignTorsorFiber U)

abbrev idMor (U : LocallyDiscrete (Iut.SchemeOverField S2994A6Stackification.S2994A6K)ᵒᵖ) :
    U ⟶ U := 𝟙 U

@[simp] lemma S3076MapIdObj_hom :
    (S3076MapIdObj U P).hom =
      pullback.fst (f := P.projection) (g := (idMor U).as.unop) := rfl

@[simp] lemma idMor_as_unop
    (U : LocallyDiscrete (Iut.SchemeOverField S2994A6Stackification.S2994A6K)ᵒᵖ) :
    (idMor U).as.unop = 𝟙 (Opposite.unop U.as) := rfl

#check S3076MapIdObj_hom
#check idMor_as_unop
end LeanFormal.IUT.XiFPaper.S3076MapIdObjHelper
end
