import tmp.sheaf.xif.paper.S2671D9StackRepairActual
import tmp.sheaf.xif.paper.S2676D9StackConditionalActual

noncomputable section
open CategoryTheory
open LeanFormal.IUT
open scoped CategoryTheory.Bicategory
set_option linter.unusedVariables false

namespace LeanFormal.IUT.XiFPaper.S2678D9AuditActual

open LeanFormal.IUT.XiFPaper.S2619ActionGroupoidFiberSkeleton
open LeanFormal.IUT.XiFPaper.S2667FiberCoherenceActual
open LeanFormal.IUT.XiFPaper.S2671D9StackRepairActual
open LeanFormal.IUT.XiFPaper.S2676D9StackConditionalActual

universe u
variable {l : PrimeGeFive} {F : Type u} [Field F]

/-- The original D9 target family (one stack claim per bare action-groupoid
datum) is false: the empty-object obstruction refutes it pointwise. -/
theorem S2678D9OriginalTarget_false :
    ¬ (∀ D : S2619ActionGroupoidData (l := l) (F := F),
        (S2667FiberPseudofunctor (l := l) (F := F) D).IsStack
          (Iut.SchemeOverField.etaleTopology F)) := by
  intro h
  obtain ⟨D⟩ := S2671TorsorDataNonempty_nonempty (l := l) (F := F)
  exact S2671Fiber_not_isStack (l := l) (F := F) D.toBare
    (h D.toBare)

/-- The honest conditional target: prestack plus descent effectivity implies
IsStack, for any bare action-groupoid datum.  This is the only surviving D9
statement after the empty-object no-go. -/
theorem S2678D9ConditionalTarget
    (D : S2619ActionGroupoidData (l := l) (F := F))
    (hpre : (S2667FiberPseudofunctor (l := l) (F := F) D).IsPrestack
      (Iut.SchemeOverField.etaleTopology F))
    (hess : ∀ {S : Iut.SchemeOverField F} (R : Sieve S),
      R ∈ Iut.SchemeOverField.etaleTopology F S →
      ((S2667FiberPseudofunctor (l := l) (F := F) D).toDescentData
        (fun (f : R.arrows.category) => f.obj.hom)).EssSurj) :
    (S2667FiberPseudofunctor (l := l) (F := F) D).IsStack
      (Iut.SchemeOverField.etaleTopology F) :=
  S2676FiberIsStack_of_input (l := l) (F := F) D hpre hess

#check S2678D9OriginalTarget_false
#check S2678D9ConditionalTarget
#print axioms S2678D9OriginalTarget_false
#print axioms S2678D9ConditionalTarget

end LeanFormal.IUT.XiFPaper.S2678D9AuditActual
end
