import tmp.sheaf.xif.paper.S3075QPrimeAssembly
import tmp.sheaf.xif.paper.S3042bUnconditionalQEffectiveDescent

noncomputable section
open CategoryTheory
open CategoryTheory.Limits
open LeanFormal.IUT
open Iut
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.XiFPaper.S3049TorsorFiberCategory
open LeanFormal.IUT.XiFPaper.S3069QPrimeTorsorStack
open LeanFormal.IUT.XiFPaper.S3073TorsorPullbackActual
open LeanFormal.IUT.XiFPaper.S3075QPrimeAssembly
open LeanFormal.IUT.XiFPaper.S3048StackificationQPrime
open LeanFormal.IUT.XiFPaper.S2994A6Stackification
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 0

namespace LeanFormal.IUT.XiFPaper.S3076QPrimeIsStack

abbrev S3076K : Type 1 := Iut.SchemeOverField S2994A6K

noncomputable abbrev S3076QPrimeObj
    (U : CategoryTheory.LocallyDiscrete (S3076Kᵒᵖ)) : Cat.{0, 1} :=
  Cat.of (S3048SignTorsorFiber U)

noncomputable abbrev S3076QPrimeMap
    {U V : CategoryTheory.LocallyDiscrete (S3076Kᵒᵖ)}
    (f : U ⟶ V) :
    S3076QPrimeObj U ⥤ S3076QPrimeObj V :=
  S3075PullbackFunctor f

abbrev S3076QPrimePseudofunctor :=
  Pseudofunctor (CategoryTheory.LocallyDiscrete (S3076Kᵒᵖ)) Cat.{0, 1}

/-- Exact Q' target: object/map functors plus IsStack.  No Q' pseudofunctor or
prestack is asserted yet. -/
structure S3076QPrimeIsStackTarget where
  Qprime : S3076QPrimePseudofunctor
  fiber_eq : ∀ U : CategoryTheory.LocallyDiscrete (S3076Kᵒᵖ),
    Nonempty (CategoryTheory.Equivalence (Qprime.obj U) (S3076QPrimeObj U))
  map_eq : ∀ {U V : CategoryTheory.LocallyDiscrete (S3076Kᵒᵖ)}
    (f : U ⟶ V),
    ∃ (eU : CategoryTheory.Equivalence (Qprime.obj U) (S3076QPrimeObj U))
      (eV : CategoryTheory.Equivalence (Qprime.obj V) (S3076QPrimeObj V)),
      Nonempty ((Qprime.map f).toFunctor ⋙ eV.functor ≅
        eU.functor ⋙ S3076QPrimeMap f)
  isStack : Qprime.IsStack (Iut.SchemeOverField.etaleTopology S2994A6K)

def S3076QPrimeIsStackTargetProp : Prop :=
  Nonempty S3076QPrimeIsStackTarget

/-- The S3042b effective-descent theorem for the pointwise prestack S2882A6Q,
separate from the torsor stack Q'. -/
theorem S3076_pointwise_effective_descent :
    LeanFormal.IUT.XiFPaper.S2893A6QIsStackActual.S2893A6QEffectiveDescent :=
  LeanFormal.IUT.XiFPaper.S3042bUnconditionalQEffectiveDescent.S3042b_QEffectiveDescent


/-- Exact effective-descent target for the corrected Q', using the same
quantification as S2893A6QEffectiveDescent. -/
def S3076EffectiveDescentTarget
    (Q : S3076QPrimePseudofunctor) : Prop :=
  ∀ (U : Iut.SchemeOverField S2994A6K) (R : Sieve U),
    R ∈ Iut.SchemeOverField.etaleTopology S2994A6K U →
      (Q.toDescentData (fun f : R.arrows.category => f.obj.hom)).EssSurj

/-- Exact prestack target for the corrected Q'. -/
def S3076PrestackTarget
    (Q : S3076QPrimePseudofunctor) : Prop :=
  Q.IsPrestack (Iut.SchemeOverField.etaleTopology S2994A6K)

/-- IsStack gives the exact effective-descent target. -/
theorem S3076_effectiveDescent_of_isStack
    (Q : S3076QPrimePseudofunctor)
    (h : Q.IsStack (Iut.SchemeOverField.etaleTopology S2994A6K)) :
    S3076EffectiveDescentTarget Q := by
  intro U R hR
  exact h.essSurj_of_sieve R hR

/-- IsStack gives the prestack target. -/
theorem S3076_prestack_of_isStack
    (Q : S3076QPrimePseudofunctor)
    (h : Q.IsStack (Iut.SchemeOverField.etaleTopology S2994A6K)) :
    S3076PrestackTarget Q :=
  h.toIsPrestack

/-- Exact combined target: corrected Q' with fiber/map equivalences,
prestack, effective descent, and IsStack. -/
structure S3076QPrimeExactIsStackTarget
    extends S3076QPrimeIsStackTarget where
  prestack : S3076PrestackTarget Qprime
  effective_descent : S3076EffectiveDescentTarget Qprime

/-- S3042b proves effective descent only for the pointwise prestack
S2882A6Q; it is a separate theorem from the corrected Q' target. -/
def S3076S3042bScopeNote : Prop :=
  LeanFormal.IUT.XiFPaper.S2893A6QIsStackActual.S2893A6QEffectiveDescent

#check S3076EffectiveDescentTarget
#check S3076PrestackTarget
#check S3076_effectiveDescent_of_isStack
#check S3076_prestack_of_isStack
#check S3076QPrimeExactIsStackTarget
#check S3076S3042bScopeNote

#check S3076QPrimeObj
#check S3076QPrimeMap
#check S3076QPrimePseudofunctor
#check S3076QPrimeIsStackTarget
#check S3076QPrimeIsStackTargetProp
#check S3076_pointwise_effective_descent

end LeanFormal.IUT.XiFPaper.S3076QPrimeIsStack
end
