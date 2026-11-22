import tmp.sheaf.xif.paper.S2675PresheafHomSheafActual
import tmp.sheaf.xif.paper.S2676D9StackConditionalActual

noncomputable section
open CategoryTheory
open LeanFormal.IUT
open scoped CategoryTheory.Bicategory
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT.XiFPaper.S2679D9FiberIsStackConditionalActual
open LeanFormal.IUT.XiFPaper.S2619ActionGroupoidFiberSkeleton
open LeanFormal.IUT.XiFPaper.S2622TorsorSectionUniqueActual
open LeanFormal.IUT.XiFPaper.S2667FiberCoherenceActual
open LeanFormal.IUT.XiFPaper.S2675PresheafHomSheafActual
open LeanFormal.IUT.XiFPaper.S2676D9StackConditionalActual

universe u
variable {l : PrimeGeFive} {F : Type u} [Field F]

def S2679EssSurjInput (D : S2622TorsorData (l := l) (F := F)) : Prop :=
  forall {S : Iut.SchemeOverField F} (R : Sieve S)
    (hR : R ∈ Iut.SchemeOverField.etaleTopology F S),
    ((S2667FiberPseudofunctor (l := l) (F := F) D.toS2619ActionGroupoidData).toDescentData
      (fun (f : R.arrows.category) => f.obj.hom)).EssSurj

theorem S2679FiberIsStack
    (D : S2622TorsorData (l := l) (F := F))
    (hess : S2679EssSurjInput (l := l) (F := F) D) :
    (S2667FiberPseudofunctor (l := l) (F := F) D.toS2619ActionGroupoidData).IsStack
      (Iut.SchemeOverField.etaleTopology F) :=
  S2676FiberIsStack_of_input D.toS2619ActionGroupoidData
    (S2675FiberIsPrestack (l := l) (F := F) D) hess

#check S2679EssSurjInput
#check S2679FiberIsStack
#print axioms S2679FiberIsStack
end LeanFormal.IUT.XiFPaper.S2679D9FiberIsStackConditionalActual
end