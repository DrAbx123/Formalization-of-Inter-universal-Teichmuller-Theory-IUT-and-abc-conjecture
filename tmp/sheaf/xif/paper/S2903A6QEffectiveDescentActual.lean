import tmp.sheaf.xif.paper.S2893A6QIsStackActual
open CategoryTheory
open LeanFormal.IUT
noncomputable section
universe u
namespace LeanFormal.IUT.XiFPaper.S2903A6QEffectiveDescentActual
open LeanFormal.IUT.XiFPaper.S2882A6PointwisePseudofunctorActual
open LeanFormal.IUT.XiFPaper.S2893A6QIsStackActual
open LeanFormal.IUT.XiFPaper.S2847A6ArithmeticActual
open LeanFormal.IUT.InitialThetaSource

def S2903A6QEffectiveDescent : Prop :=
  S2893A6QEffectiveDescent

theorem S2903A6QEffectiveDescent_iff :
    S2903A6QEffectiveDescent ↔
      ∀ (U : Iut.SchemeOverField S2847A6.F) (R : Sieve U),
        R ∈ Iut.SchemeOverField.etaleTopology S2847A6.F U →
          (S2882A6Q.toDescentData (fun f : R.arrows.category => f.obj.hom)).EssSurj :=
  Iff.rfl

#check S2903A6QEffectiveDescent
#check S2903A6QEffectiveDescent_iff

end LeanFormal.IUT.XiFPaper.S2903A6QEffectiveDescentActual