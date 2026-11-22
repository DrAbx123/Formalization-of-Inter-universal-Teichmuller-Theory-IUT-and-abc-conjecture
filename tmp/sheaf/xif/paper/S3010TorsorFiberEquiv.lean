import tmp.sheaf.xif.paper.S2996A6StackWitnessConstruction
import tmp.sheaf.xif.paper.S2994A6Stackification
import Mathlib.CategoryTheory.Bicategory.Functor.LocallyDiscrete

noncomputable section
open CategoryTheory
open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.XiFPaper.S2996A6StackWitnessConstruction
open LeanFormal.IUT.XiFPaper.S2994A6Stackification
open LeanFormal.IUT.XiFPaper.S2882A6PointwisePseudofunctorActual
open LeanFormal.IUT.XiFPaper.S2847A6ArithmeticActual
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 0

namespace LeanFormal.IUT.XiFPaper.S3010TorsorFiberEquiv

/-- Exact data required for the torsor-stack route: a stack with pointwise
equivalence to the A6 action-groupoid fibers at every test object.
The torsor stack itself is an explicit field; no stackification is claimed. -/
structure S3010TorsorStackData where
  stack : Iut.EtaleStackPseudofunctor S2994A6K
  fiberEquiv :
    ∀ U : LocallyDiscrete (Iut.SchemeOverField S2994A6K)ᵒᵖ,
      Nonempty (CategoryTheory.Equivalence (stack.obj U)
        (S2994A6PointwiseQuotient U))

/-- The torsor-stack pointwise equivalence spec. -/
structure S3010TorsorFiberEquiv extends S3010TorsorStackData where
  isStack : toS3010TorsorStackData.stack.IsStack
    (Iut.SchemeOverField.etaleTopology S2994A6K)

/-- Feed the torsor-stack data into the actual S2996 witness core. -/
noncomputable def S3010TorsorFiberEquiv.toS2996Core
    (D : S3010TorsorStackData) :
    S2995A6StackWitnessCore where
  stack := D.stack
  fiber_equiv := D.fiberEquiv

/-- Feed the full torsor-stack data into the S2996 witness. -/
noncomputable def S3010TorsorFiberEquiv.toS2996Witness
    (D : S3010TorsorFiberEquiv) :
    S2995A6StackWitness :=
  S2996A6StackWitnessCore.toWitness
    (S3010TorsorFiberEquiv.toS2996Core D.toS3010TorsorStackData)
    (by
      -- prestack follows from stack
      exact D.isStack.toIsPrestack)
    D.isStack

#check S3010TorsorStackData
#check S3010TorsorFiberEquiv
#check S3010TorsorFiberEquiv.toS2996Core
#check S3010TorsorFiberEquiv.toS2996Witness

end LeanFormal.IUT.XiFPaper.S3010TorsorFiberEquiv
end
