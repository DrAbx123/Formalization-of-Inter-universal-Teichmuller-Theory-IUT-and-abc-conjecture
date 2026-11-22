import LeanFormal.IUT.IUTI.InitialTheta.SourceDefinition31Quantifiers

universe u

noncomputable section
open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.Pseudofunctor.StrongTrans
open LeanFormal.IUT
open Iut
open LeanFormal.IUT.InitialThetaSource

attribute [local instance] CategoryTheory.Pseudofunctor.StrongTrans.instBicategory

namespace LeanFormal.IUT.XiFPaper.S3123SourceOrbicurveScalarExtensionFiberActual

variable {F K : Type u} [Field F] [Field K] [Algebra F K]
variable {X : Iut.HyperbolicOrbicurve F}

theorem S3123SourceOrbicurveScalarExtension_fiber_nonempty
    (E : SourceOrbicurveScalarExtension F K X) :
    Nonempty (Bicategory.Equivalence (E.result.stack).fiber
      (Pseudofunctor.comp (schemeRestrictScalarsPseudofunctor F K)
        X.stack.fiber)) := by
  rw [E.target_stack]
  exact ⟨E.stackExtension.fiberEquivalence⟩

theorem S3123SourceOrbicurveScalarExtension_stack_nonempty
    (E : SourceOrbicurveScalarExtension F K X) :
    Nonempty (SourceEtaleStackScalarExtension F K X.stack) :=
  ⟨E.stackExtension⟩

#check S3123SourceOrbicurveScalarExtension_fiber_nonempty
#check S3123SourceOrbicurveScalarExtension_stack_nonempty

end LeanFormal.IUT.XiFPaper.S3123SourceOrbicurveScalarExtensionFiberActual
end
