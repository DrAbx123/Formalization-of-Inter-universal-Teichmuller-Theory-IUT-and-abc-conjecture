import tmp.sheaf.xif.paper.S2671D9NonemptyRepairActual
import tmp.sheaf.xif.paper.S2668D9ReductionActual
import tmp.sheaf.xif.paper.S2667FiberCoherenceActual
import tmp.sheaf.xif.paper.S2663D9IsStackReductionActual

noncomputable section
open CategoryTheory
open LeanFormal.IUT
open scoped CategoryTheory.Bicategory
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT.XiFPaper.S2672D9NonemptyConditionalActual
open LeanFormal.IUT.XiFPaper.S2619ActionGroupoidFiberSkeleton
open LeanFormal.IUT.XiFPaper.S2671D9NonemptyRepairActual
open LeanFormal.IUT.XiFPaper.S2668D9ReductionActual
open LeanFormal.IUT.XiFPaper.S2667FiberCoherenceActual
open LeanFormal.IUT.XiFPaper.S2663D9IsStackReductionActual

universe u
variable {l : PrimeGeFive} {F : Type u} [Field F]

def S2672EssSurjInput (D : S2671TorsorDataNonempty (l := l) (F := F)) : Prop :=
  forall {S : Iut.SchemeOverField F} (R : Sieve S)
    (hR : R ∈ Iut.SchemeOverField.etaleTopology F S),
    ((S2667FiberPseudofunctor l F D.toActionGroupoidData).toDescentData
      (fun (f : R.arrows.category) => f.obj.hom)).EssSurj

theorem S2672NonemptyIsStack
    (D : S2671TorsorDataNonempty (l := l) (F := F))
    (hpre : (S2667FiberPseudofunctor l F D.toActionGroupoidData).IsPrestack
      (Iut.SchemeOverField.etaleTopology F))
    (hess : S2672EssSurjInput D) :
    (S2667FiberPseudofunctor l F D.toActionGroupoidData).IsStack
      (Iut.SchemeOverField.etaleTopology F) :=
  (S2663IsStack_iff (F := S2667FiberPseudofunctor l F D.toActionGroupoidData)
    (J := Iut.SchemeOverField.etaleTopology F)).mpr ⟨hpre, hess⟩

#check S2672EssSurjInput
#check S2672NonemptyIsStack
#print axioms S2672NonemptyIsStack
end LeanFormal.IUT.XiFPaper.S2672D9NonemptyConditionalActual
end