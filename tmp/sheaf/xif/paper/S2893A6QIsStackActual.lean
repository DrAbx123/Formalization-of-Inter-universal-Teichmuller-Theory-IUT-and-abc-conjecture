import tmp.sheaf.xif.paper.S2882A6PointwisePseudofunctorActual
import Mathlib.CategoryTheory.Sites.SheafOfTypes
open CategoryTheory
open LeanFormal.IUT
noncomputable section
universe u
namespace LeanFormal.IUT.XiFPaper.S2893A6QIsStackActual
open LeanFormal.IUT.XiFPaper.S2882A6PointwisePseudofunctorActual
open LeanFormal.IUT.XiFPaper.S2847A6ArithmeticActual
open LeanFormal.IUT.InitialThetaSource

/-- A6 pointwise Q is an etale stack. -/
def S2893A6QIsStack : Prop :=
  S2882A6Q.IsStack (Iut.SchemeOverField.etaleTopology S2847A6.F)

/-- Effective descent for the A6 pointwise Q. -/
def S2893A6QEffectiveDescent : Prop :=
  ∀ (U : Iut.SchemeOverField S2847A6.F) (R : Sieve U),
    R ∈ Iut.SchemeOverField.etaleTopology S2847A6.F U →
      (S2882A6Q.toDescentData (fun f : R.arrows.category => f.obj.hom)).EssSurj

/-- The required descent API for the A6 pointwise Q. -/
def S2893A6QDescentAPI : Prop :=
  S2882A6Q.IsPrestack (Iut.SchemeOverField.etaleTopology S2847A6.F) ∧
    S2893A6QEffectiveDescent

/-- IsStack is exactly prestack plus effective descent. -/
theorem S2893A6QIsStack_iff_descent :
    S2893A6QIsStack ↔ S2893A6QDescentAPI := by
  constructor
  · intro h
    refine ⟨h.toIsPrestack, ?_⟩
    intro U R hR
    exact h.essSurj_of_sieve R hR
  · intro hAPI
    change S2882A6Q.IsPrestack (Iut.SchemeOverField.etaleTopology S2847A6.F) ∧
      S2893A6QEffectiveDescent at hAPI
    rcases hAPI with ⟨hP, hD⟩
    have hD' : ∀ (U : Iut.SchemeOverField S2847A6.F) (R : Sieve U),
        R ∈ Iut.SchemeOverField.etaleTopology S2847A6.F U →
          (S2882A6Q.toDescentData (fun f : R.arrows.category => f.obj.hom)).EssSurj := hD
    exact { toIsPrestack := hP, essSurj_of_sieve := fun {U} R hR => hD' U R hR }


theorem S2893A6QDescentAPI_iff :
    S2893A6QDescentAPI ↔ S2893A6QIsStack :=
  S2893A6QIsStack_iff_descent.symm

#check S2893A6QDescentAPI_iff
#print axioms S2893A6QDescentAPI_iff

#print axioms S2893A6QIsStack_iff_descent

end LeanFormal.IUT.XiFPaper.S2893A6QIsStackActual