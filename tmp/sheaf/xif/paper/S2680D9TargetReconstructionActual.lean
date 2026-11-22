import tmp.sheaf.xif.paper.S2670D9EssSurjActual
import tmp.sheaf.xif.paper.S2668D9ReductionActual
import tmp.sheaf.xif.paper.S2668FiberCoherenceActual

noncomputable section
open CategoryTheory
open LeanFormal.IUT
open scoped SpecOfNotation CategoryTheory.Bicategory
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT.XiFPaper.S2680D9TargetReconstructionActual

open LeanFormal.IUT.XiFPaper.S2619ActionGroupoidFiberSkeleton
open LeanFormal.IUT.XiFPaper.S2668D9ReductionActual
open LeanFormal.IUT.XiFPaper.S2668FiberCoherenceActual
open LeanFormal.IUT.XiFPaper.S2669D9PrestackActual
open LeanFormal.IUT.XiFPaper.S2670D9EssSurjActual

universe u
variable {l : PrimeGeFive} {F : Type u} [Field F]

structure S2680CorrectedDatum extends
    S2619ActionGroupoidData (l := l) (F := F) where
  nonempty_slice_free : Prop

abbrev S2680CorrectedFiber
    (D : S2680CorrectedDatum (l := l) (F := F)) :
    LocallyDiscrete (Iut.SchemeOverField F)ᵒᵖ ⥤ᵖ Cat.{0, u} :=
  S2668FiberPseudofunctor (l := l) (F := F) D.toS2619ActionGroupoidData

def S2680EssSurjInput
    (fib : LocallyDiscrete (Iut.SchemeOverField F)ᵒᵖ ⥤ᵖ Cat.{0, u}) : Prop :=
  ∀ {S : Iut.SchemeOverField F} (R : Sieve S)
    (hR : R ∈ Iut.SchemeOverField.etaleTopology F S),
    (fib.toDescentData (fun (f : R.arrows.category) => f.obj.hom)).EssSurj

def S2680D9CorrectedTarget
    (D : S2680CorrectedDatum (l := l) (F := F)) : Prop :=
  (S2680CorrectedFiber (l := l) (F := F) D).IsStack
    (Iut.SchemeOverField.etaleTopology F)

theorem S2680D9CorrectedTarget_conditional
    (D : S2680CorrectedDatum (l := l) (F := F))
    (hsheaf : ∀ {S : Iut.SchemeOverField F}
      (M N : (S2680CorrectedFiber (l := l) (F := F) D).obj
        (LocallyDiscrete.mk (Opposite.op S))),
      Presheaf.IsSheaf ((Iut.SchemeOverField.etaleTopology F).over S)
        ((S2680CorrectedFiber (l := l) (F := F) D).presheafHom M N))
    (hess : S2680EssSurjInput (S2680CorrectedFiber (l := l) (F := F) D)) :
    S2680D9CorrectedTarget (l := l) (F := F) D :=
  (S2668D9IsStack_iff (F := F)
    (S2680CorrectedFiber (l := l) (F := F) D)).mpr ⟨hsheaf, hess⟩

structure S2680StackificationTarget
    (D : S2680CorrectedDatum (l := l) (F := F)) where
  stack : LocallyDiscrete (Iut.SchemeOverField F)ᵒᵖ ⥤ᵖ Cat.{0, u}
  isStack : stack.IsStack (Iut.SchemeOverField.etaleTopology F)
  unit_exists : Prop

def S2680StackificationTargetRequired
    (D : S2680CorrectedDatum (l := l) (F := F)) : Prop :=
  Nonempty (S2680StackificationTarget (l := l) (F := F) D)

#print axioms S2680D9CorrectedTarget_conditional

end LeanFormal.IUT.XiFPaper.S2680D9TargetReconstructionActual
end
