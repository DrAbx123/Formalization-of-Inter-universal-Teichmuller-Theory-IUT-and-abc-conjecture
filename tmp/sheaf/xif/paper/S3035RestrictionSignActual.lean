import tmp.sheaf.xif.paper.S2976bA6QDescentGluing
import tmp.sheaf.xif.paper.S2975bA6QPresheafHomSheaf
import tmp.sheaf.xif.paper.S2847A6ArithmeticActual
noncomputable section
open CategoryTheory Opposite
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S2882A6PointwisePseudofunctorActual
open LeanFormal.IUT.XiFPaper.S2976bA6QDescentGluing
open LeanFormal.IUT.XiFPaper.S2975bA6QPresheafHomSheaf
open LeanFormal.IUT.XiFPaper.S2847A6ArithmeticActual
namespace LeanFormal.IUT.XiFPaper.S3035RestrictionSignActual

abbrev K : Type := S2882A6PointwisePseudofunctorActual.K
local instance : Field K := S2847A6.fieldF
local instance : NumberField K := S2847A6.numberFieldF

lemma S3035_presheafHom_map_val
    {S : Iut.SchemeOverField K}
    (M N : S2882A6Q.obj (LocallyDiscrete.mk (Opposite.op S)))
    {T₁ T₂ : Over S} (p : T₂ ⟶ T₁)
    (x : (S2882A6Q.presheafHom M N).obj (Opposite.op T₁)) :
    ((S2882A6Q.presheafHom M N).map p.op x).val = x.val := by
  change (Pseudofunctor.LocallyDiscreteOpToCat.pullHom x
    p.left T₂.hom T₂.hom p.w p.w).val = x.val
  exact pullHom_val x p.left T₂.hom T₂.hom p.w p.w

#check S3035_presheafHom_map_val
#print axioms S3035_presheafHom_map_val

end LeanFormal.IUT.XiFPaper.S3035RestrictionSignActual