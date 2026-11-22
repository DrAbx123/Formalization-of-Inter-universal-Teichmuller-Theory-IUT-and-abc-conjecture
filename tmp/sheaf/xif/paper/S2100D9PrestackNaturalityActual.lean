import tmp.sheaf.xif.paper.S2093D9StackActual
import Mathlib.CategoryTheory.Sites.SheafHom
import Mathlib.CategoryTheory.Sites.PseudofunctorSheafOver
import Mathlib.CategoryTheory.Sites.DenseSubsite.SheafEquiv

noncomputable section
open CategoryTheory AlgebraicGeometry Opposite
open scoped AlgebraicGeometry
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency false

namespace LeanFormal.IUT.XiFPaper.S2100D9PrestackNaturalityActual

open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S2093D9StackActual
open LeanFormal.IUT.XiFPaper.S2029GiraudStackificationActual

universe u

variable {K : Type u} [Field K]

/-- The component comparison of the two slice pullbacks. For a test object
T : Over S, the pseudofunctor pullback overMapPullback T.hom is the composite
of the slice pullback overPullback T with the pushforward along the
iterated-slice inverse equivalence. This is Mathlib sheafPushforwardContinuousComp
plus iteratedSliceBackward_forget. -/
noncomputable def S2100SlicePullbackIso (S : Iut.SchemeOverField K)
    (T : Over S) :
    (Iut.SchemeOverField.etaleTopology K).overMapPullback (Type u) T.hom ≅
      ((Iut.SchemeOverField.etaleTopology K).over S).overPullback (Type u) T ⋙
        T.iteratedSliceBackward.sheafPushforwardContinuous (Type u)
          ((Iut.SchemeOverField.etaleTopology K).over T.left)
          (((Iut.SchemeOverField.etaleTopology K).over S).over T) := by
  have h := Functor.sheafPushforwardContinuousComp
    (F := T.iteratedSliceBackward) (G := Over.forget T) (Type u)
    ((Iut.SchemeOverField.etaleTopology K).over T.left)
    (((Iut.SchemeOverField.etaleTopology K).over S).over T)
    ((Iut.SchemeOverField.etaleTopology K).over S)
  let e : T.iteratedSliceBackward ⋙ Over.forget T ≅ Over.map T.hom :=
    eqToIso (Over.iteratedSliceBackward_forget T)
  haveI : (T.iteratedSliceBackward ⋙ Over.forget T).IsContinuous
      ((Iut.SchemeOverField.etaleTopology K).over T.left)
      ((Iut.SchemeOverField.etaleTopology K).over S) := by
    rw [Over.iteratedSliceBackward_forget T]
    infer_instance
  exact h ≪≫ Functor.sheafPushforwardContinuousIso
    (F := T.iteratedSliceBackward ⋙ Over.forget T)
    (F' := Over.map T.hom) e (Type u)
    ((Iut.SchemeOverField.etaleTopology K).over T.left)
    ((Iut.SchemeOverField.etaleTopology K).over S)

/-- The exact naturality input: for every test object T, the Hom sets of the
slice-sheaf prestack and of sheafHom are naturally identified. This is the
prestack half isolated by S2093; no inhabitant is asserted. -/
def S2100PrestackNaturalityIso : Prop :=
  forall (S : Iut.SchemeOverField K)
    (M N : (S2029SheafPrestack K).obj (LocallyDiscrete.mk (Opposite.op S))),
    Nonempty
      ((S2029SheafPrestack K).presheafHom M N ≅
        (sheafHom M N).1)

/-- If the naturality isomorphism exists, the prestack half follows: the
hom-presheaf of the slice-sheaf prestack is a sheaf because it is isomorphic to
the underlying presheaf of sheafHom. -/
theorem S2100SheafPrestack_of_naturality
    (h : S2100PrestackNaturalityIso (K := K)) :
    S2093SheafPrestack K := by
  exact ⟨fun {S} M N => by
    obtain ⟨e⟩ := h S M N
    exact (Presheaf.isSheaf_of_iso_iff e).mpr ((sheafHom M N).2)⟩

/-- The component comparison is an actual iso of functors, independent of the
global naturality in the test object. -/
theorem S2100SlicePullbackIso_actual (S : Iut.SchemeOverField K) (T : Over S) :
    Nonempty ((Iut.SchemeOverField.etaleTopology K).overMapPullback (Type u) T.hom ≅
      ((Iut.SchemeOverField.etaleTopology K).over S).overPullback (Type u) T ⋙
        T.iteratedSliceBackward.sheafPushforwardContinuous (Type u)
          ((Iut.SchemeOverField.etaleTopology K).over T.left)
          (((Iut.SchemeOverField.etaleTopology K).over S).over T)) :=
  ⟨S2100SlicePullbackIso S T⟩

#print axioms S2100SlicePullbackIso
#print axioms S2100SheafPrestack_of_naturality
#print axioms S2100SlicePullbackIso_actual

end LeanFormal.IUT.XiFPaper.S2100D9PrestackNaturalityActual

end
