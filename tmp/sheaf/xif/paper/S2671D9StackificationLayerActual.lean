import tmp.sheaf.xif.paper.S2668D9ReductionActual
import tmp.sheaf.xif.paper.S2668FiberCoherenceActual

noncomputable section
open CategoryTheory
open LeanFormal.IUT
open scoped CategoryTheory.Bicategory
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT.XiFPaper.S2671D9StackificationLayerActual
open LeanFormal.IUT.XiFPaper.S2668D9ReductionActual
open LeanFormal.IUT.XiFPaper.S2668FiberCoherenceActual
open LeanFormal.IUT.XiFPaper.S2619ActionGroupoidFiberSkeleton

universe u
variable {l : PrimeGeFive} {F : Type u} [Field F]

structure S2671TorsorStackificationData
    (D : S2619ActionGroupoidData l F) where
  stack : LocallyDiscrete (Iut.SchemeOverField F)ᵒᵖ ⥤ᵖ Cat.{0, u}
  isStack : stack.IsStack (Iut.SchemeOverField.etaleTopology F)

theorem S2671TorsorStackificationData_isStack
    {D : S2619ActionGroupoidData l F}
    (X : S2671TorsorStackificationData D) :
    X.stack.IsStack (Iut.SchemeOverField.etaleTopology F) :=
  X.isStack

def S2671EssSurjInput
    (fib : LocallyDiscrete (Iut.SchemeOverField F)ᵒᵖ ⥤ᵖ Cat.{0, u}) : Prop :=
  forall {S : Iut.SchemeOverField F} (R : Sieve S)
    (hR : R ∈ Iut.SchemeOverField.etaleTopology F S),
    (fib.toDescentData (fun (f : R.arrows.category) => f.obj.hom)).EssSurj

theorem S2671IsStack_of_sheaf_and_essSurj
    (fib : LocallyDiscrete (Iut.SchemeOverField F)ᵒᵖ ⥤ᵖ Cat.{0, u})
    (hsheaf : forall {S : Iut.SchemeOverField F}
      (M N : fib.obj (LocallyDiscrete.mk (Opposite.op S))),
      Presheaf.IsSheaf ((Iut.SchemeOverField.etaleTopology F).over S)
        (fib.presheafHom M N))
    (hess : S2671EssSurjInput fib) :
    fib.IsStack (Iut.SchemeOverField.etaleTopology F) :=
  (S2668D9IsStack_iff fib).mpr ⟨hsheaf, hess⟩

#check S2671TorsorStackificationData
#check S2671TorsorStackificationData_isStack
#check S2671IsStack_of_sheaf_and_essSurj
#print axioms S2671IsStack_of_sheaf_and_essSurj
end LeanFormal.IUT.XiFPaper.S2671D9StackificationLayerActual
end