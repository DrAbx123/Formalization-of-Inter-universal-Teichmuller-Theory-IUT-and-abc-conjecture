import tmp.sheaf.xif.paper.S3123OrbicurveScalarExtensionWitnessNonemptyActual

universe u

noncomputable section
open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.Pseudofunctor.StrongTrans
open LeanFormal.IUT
open Iut
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.XiFPaper.S3123OrbicurveScalarExtensionWitnessActual

attribute [local instance] CategoryTheory.Pseudofunctor.StrongTrans.instBicategory

namespace LeanFormal.IUT.XiFPaper.S3123OrbicurveScalarExtensionWitnessFiberActual

variable {F K : Type u} [Field F] [Field K] [Algebra F K]

theorem S3123OrbicurveScalarExtensionWitness_fiber_nonempty
    (W : S3123OrbicurveScalarExtensionWitness F K) :
    Nonempty (Bicategory.Equivalence (W.R.stack).fiber
      (Pseudofunctor.comp (schemeRestrictScalarsPseudofunctor F K)
        W.X.stack.fiber)) := by
  rw [W.target_stack]
  exact ⟨W.stackExtension.fiberEquivalence⟩

theorem S3123OrbicurveScalarExtensionWitness_fiber_nonempty_of_stack
    (W : S3123OrbicurveScalarExtensionWitness F K) :
    Nonempty (Bicategory.Equivalence W.stackExtension.result.fiber
      (Pseudofunctor.comp (schemeRestrictScalarsPseudofunctor F K)
        W.X.stack.fiber)) :=
  ⟨W.stackExtension.fiberEquivalence⟩

#check S3123OrbicurveScalarExtensionWitness_fiber_nonempty
#check S3123OrbicurveScalarExtensionWitness_fiber_nonempty_of_stack

end LeanFormal.IUT.XiFPaper.S3123OrbicurveScalarExtensionWitnessFiberActual
end
