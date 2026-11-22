import tmp.sheaf.xif.paper.S2670D9EssSurjActual
import tmp.sheaf.xif.paper.S2663D9IsStackReductionActual

noncomputable section
open CategoryTheory
open LeanFormal.IUT
open scoped CategoryTheory.Bicategory
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.XiFPaper.S2671D9NonemptyRepairActual

open LeanFormal.IUT.XiFPaper.S2619ActionGroupoidFiberSkeleton
open LeanFormal.IUT.XiFPaper.S2670D9EssSurjActual
open LeanFormal.IUT.XiFPaper.S2663D9IsStackReductionActual

universe u
variable {l : PrimeGeFive} {F : Type u} [Field F]

/-- Repaired torsor datum: freeness is required only on non-empty test objects.
This avoids the empty-scheme contradiction that makes S2622TorsorData empty. -/
structure S2671TorsorDataNonempty
    extends S2619ActionGroupoidData (l := l) (F := F) where
  hfree_nonempty :
    forall (V : (Iut.SchemeOverField F)ᵒᵖ), Nonempty V.unop.left ->
      forall (M : V.unop ⟶ toS2619ActionGroupoidData.U)
        {g1 g2 : S2619G l},
        M ≫ (toS2619ActionGroupoidData.rho g1).hom =
          M ≫ (toS2619ActionGroupoidData.rho g2).hom -> g1 = g2

namespace S2671TorsorDataNonempty

variable (D : S2671TorsorDataNonempty (l := l) (F := F))

/-- Forget the repaired structure to the bare action-groupoid datum. -/
abbrev toActionGroupoidData : S2619ActionGroupoidData (l := l) (F := F) :=
  D.toS2619ActionGroupoidData

end S2671TorsorDataNonempty

/-- Conditional D9 IsStack theorem: prestack plus the explicit effectivity
input `S2670EssSurjInput` gives a stack. This is deliberately conditional;
it does not assert the effectivity input. -/
theorem S2669FiberIsStack_of_input
    (D : S2619ActionGroupoidData (l := l) (F := F))
    (hpre : (S2670FiberPF (l := l) (F := F) D).IsPrestack
      (Iut.SchemeOverField.etaleTopology F))
    (hess : S2670EssSurjInput (l := l) (F := F) D) :
    (S2670FiberPF (l := l) (F := F) D).IsStack
      (Iut.SchemeOverField.etaleTopology F) :=
  (S2663IsStack_iff
    (F := S2670FiberPF (l := l) (F := F) D)
    (J := Iut.SchemeOverField.etaleTopology F)).mpr ⟨hpre, hess⟩

#print axioms S2669FiberIsStack_of_input

end LeanFormal.IUT.XiFPaper.S2671D9NonemptyRepairActual
end
