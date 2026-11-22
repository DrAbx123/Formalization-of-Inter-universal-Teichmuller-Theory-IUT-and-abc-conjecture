import tmp.sheaf.xif.paper.S3010TorsorFiberEquiv
import tmp.sheaf.xif.paper.S2994A6Stackification
import Mathlib.CategoryTheory.Bicategory.Functor.LocallyDiscrete

noncomputable section
open CategoryTheory
open LeanFormal.IUT
open Iut
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.XiFPaper.S3010TorsorFiberEquiv
open LeanFormal.IUT.XiFPaper.S2994A6Stackification
open LeanFormal.IUT.XiFPaper.S2882A6PointwisePseudofunctorActual
open LeanFormal.IUT.XiFPaper.S2847A6ArithmeticActual
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 0

namespace LeanFormal.IUT.XiFPaper.S3048StackificationQPrime

/-- Spec of a sign-torsor fiber at a test object: total scheme, projection,
SignGroup action, simple transitivity (as a Prop field) and an equivariant map
to X.  This is the exact fiber shape of [X/SignGroup]. -/
structure S3048SignTorsorFiber
    (U : LocallyDiscrete (Iut.SchemeOverField S2994A6K)ᵒᵖ) where
  total : Iut.SchemeOverField S2994A6K
  projection : total ⟶ Opposite.unop U.as
  action : SignGroup → (total ⟶ total)
  action_one : action 1 = 𝟙 total
  action_mul : ∀ (g h : SignGroup), action ((g * h : SignGroup)) = action g ≫ action h
  action_projection : ∀ g : SignGroup, action g ≫ projection = projection
  simplyTransitive : Prop
  equivariantMap : total ⟶ S2844D6F6BaseChangeActual.S2844X
  equivariance : Prop

/-- Exact target data for Q' = [X/SignGroup]: a pseudofunctor whose fibers
carry sign-torsor data, is a stack, and whose trivial-torsor part matches the
A6 pointwise action groupoid. -/
structure S3048StackificationQPrimeSpec where
  Qprime : Iut.EtaleStackPseudofunctor S2994A6K
  isStack : Qprime.IsStack (Iut.SchemeOverField.etaleTopology S2994A6K)
  fiber_torsor_shape :
    ∀ U : LocallyDiscrete (Iut.SchemeOverField S2994A6K)ᵒᵖ,
      Prop
  fiber_torsor_actual :
    ∀ U : LocallyDiscrete (Iut.SchemeOverField S2994A6K)ᵒᵖ,
      fiber_torsor_shape U
  trivialFiberEquiv :
    ∀ U : LocallyDiscrete (Iut.SchemeOverField S2994A6K)ᵒᵖ,
      Nonempty (CategoryTheory.Equivalence (Qprime.obj U)
        (S2994A6PointwiseQuotient U))

/-- Exact first missing target: no Q' with IsStack and trivial-fiber
equivalence has been constructed. -/
def S3048StackificationQPrimeTarget : Prop :=
  Nonempty S3048StackificationQPrimeSpec

/-- Conditional consumer: a spec of Q' feeds the S3010 torsor-stack interface. -/
noncomputable def S3048StackificationQPrimeSpec.toS3010
    (S : S3048StackificationQPrimeSpec) : S3010TorsorStackData where
  stack := S.Qprime
  fiberEquiv := S.trivialFiberEquiv

#check S3048SignTorsorFiber
#check S3048StackificationQPrimeSpec
#check S3048StackificationQPrimeTarget
#check S3048StackificationQPrimeSpec.toS3010

end LeanFormal.IUT.XiFPaper.S3048StackificationQPrime
end
