import tmp.sheaf.xif.paper.S2667FiberCoherenceActual

noncomputable section
open CategoryTheory
open LeanFormal.IUT
open scoped CategoryTheory.Bicategory
set_option linter.unusedVariables false

namespace LeanFormal.IUT.XiFPaper.S2676D9StackConditionalActual

open LeanFormal.IUT.XiFPaper.S2619ActionGroupoidFiberSkeleton
open LeanFormal.IUT.XiFPaper.S2667FiberCoherenceActual

universe u
variable {l : PrimeGeFive} {F : Type u} [Field F]

/-- Conditional D9 IsStack: the honest non-vacuous target is IsPrestack plus the
effectivity input (essential surjectivity of toDescentData for every covering sieve). -/
theorem S2676FiberIsStack_of_input
    (D : S2619ActionGroupoidData (l := l) (F := F))
    (hpre : (S2667FiberPseudofunctor (l := l) (F := F) D).IsPrestack
      (Iut.SchemeOverField.etaleTopology F))
    (hess : ∀ {S : Iut.SchemeOverField F} (R : Sieve S),
      R ∈ Iut.SchemeOverField.etaleTopology F S →
      ((S2667FiberPseudofunctor (l := l) (F := F) D).toDescentData
        (fun (f : R.arrows.category) => f.obj.hom)).EssSurj) :
    (S2667FiberPseudofunctor (l := l) (F := F) D).IsStack
      (Iut.SchemeOverField.etaleTopology F) where
  toIsPrestack := hpre
  essSurj_of_sieve := fun R hR => hess R hR

#check S2676FiberIsStack_of_input
#print axioms S2676FiberIsStack_of_input

end LeanFormal.IUT.XiFPaper.S2676D9StackConditionalActual
end
