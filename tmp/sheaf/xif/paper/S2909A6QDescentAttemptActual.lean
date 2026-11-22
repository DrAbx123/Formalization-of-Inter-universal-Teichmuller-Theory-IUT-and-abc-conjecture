import tmp.sheaf.xif.paper.S2903A6QEffectiveDescentActual
open CategoryTheory
open LeanFormal.IUT
noncomputable section
universe u
namespace LeanFormal.IUT.XiFPaper.S2909A6QDescentAttemptActual
open LeanFormal.IUT.XiFPaper.S2882A6PointwisePseudofunctorActual
open LeanFormal.IUT.XiFPaper.S2893A6QIsStackActual
open LeanFormal.IUT.XiFPaper.S2903A6QEffectiveDescentActual
open LeanFormal.IUT.XiFPaper.S2847A6ArithmeticActual
open LeanFormal.IUT.InitialThetaSource

def S2909A6QEffectiveDescent : Prop :=
  S2903A6QEffectiveDescent

theorem S2909A6QEffectiveDescent_iff :
    S2909A6QEffectiveDescent ↔
      ∀ (U : Iut.SchemeOverField S2847A6.F) (R : Sieve U),
        R ∈ Iut.SchemeOverField.etaleTopology S2847A6.F U →
          (S2882A6Q.toDescentData (fun f : R.arrows.category => f.obj.hom)).EssSurj :=
  Iff.rfl

/-- Concrete gluing datum needed for one descent datum. -/
structure S2909GluingDatum
    {U : Iut.SchemeOverField S2847A6.F} (R : Sieve U)
    (D : S2882A6Q.DescentData (fun f : R.arrows.category => f.obj.hom)) where
  M : S2882A6Q.obj { as := Opposite.op U }
  iso : (S2882A6Q.toDescentData (fun f : R.arrows.category => f.obj.hom)).obj M ≅ D

#check S2909A6QEffectiveDescent
#check S2909A6QEffectiveDescent_iff
#check S2909GluingDatum

end LeanFormal.IUT.XiFPaper.S2909A6QDescentAttemptActual