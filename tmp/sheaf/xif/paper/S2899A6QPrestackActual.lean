import tmp.sheaf.xif.paper.S2893A6QIsStackActual
import Mathlib.CategoryTheory.Sites.SheafOfTypes
open CategoryTheory
open LeanFormal.IUT
noncomputable section
universe u
namespace LeanFormal.IUT.XiFPaper.S2899A6QPrestackActual
open LeanFormal.IUT.XiFPaper.S2882A6PointwisePseudofunctorActual
open LeanFormal.IUT.XiFPaper.S2847A6ArithmeticActual
open LeanFormal.IUT.InitialThetaSource

def S2899A6QIsPrestack : Prop :=
  S2882A6Q.IsPrestack (Iut.SchemeOverField.etaleTopology S2847A6.F)

theorem S2899A6QIsPrestack_iff :
    S2899A6QIsPrestack ↔
      ∀ {S : Iut.SchemeOverField S2847A6.F}
        (M N : (S2882A6Q.obj { as := Opposite.op S })),
        Presheaf.IsSheaf
          ((Iut.SchemeOverField.etaleTopology S2847A6.F).over S)
          (S2882A6Q.presheafHom M N) := by
  constructor
  · intro h S M N
    exact h.isSheaf M N
  · intro h
    exact { isSheaf := fun {S} M N => h M N }

/-- The exact sheaf condition left by IsPrestack. -/
def S2899A6QHomSheafCondition : Prop :=
  ∀ {S : Iut.SchemeOverField S2847A6.F}
    (M N : (S2882A6Q.obj { as := Opposite.op S })),
    Presheaf.IsSheaf
      ((Iut.SchemeOverField.etaleTopology S2847A6.F).over S)
      (S2882A6Q.presheafHom M N)

theorem S2899A6QIsPrestack_iff_sheaf :
    S2899A6QIsPrestack ↔ S2899A6QHomSheafCondition :=
  S2899A6QIsPrestack_iff

#check S2899A6QIsPrestack_iff
#check S2899A6QIsPrestack_iff_sheaf

end LeanFormal.IUT.XiFPaper.S2899A6QPrestackActual