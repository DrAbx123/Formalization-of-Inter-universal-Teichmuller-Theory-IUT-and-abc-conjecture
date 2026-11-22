import LeanFormal.IUT.IUTI.InitialTheta.SourceDefinition31Quantifiers

universe u

noncomputable section
open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.Pseudofunctor.StrongTrans
open LeanFormal.IUT
open Iut
open LeanFormal.IUT.InitialThetaSource

attribute [local instance] CategoryTheory.Pseudofunctor.StrongTrans.instBicategory

namespace LeanFormal.IUT.XiFPaper.S3123SourceOrbicurveScalarExtensionOfActual

variable {F K : Type u} [Field F] [Field K] [Algebra F K]
variable {X : Iut.HyperbolicOrbicurve F}

noncomputable def SourceOrbicurveScalarExtensionOf
    (R : Iut.HyperbolicOrbicurve K)
    (stackExtension : SourceEtaleStackScalarExtension F K X.stack)
    (target_stack : R.stack = stackExtension.result)
    (genus_preserved : R.signature.genus = X.signature.genus) :
    SourceOrbicurveScalarExtension F K X :=
  ⟨R, stackExtension, target_stack, genus_preserved⟩

@[simp] theorem SourceOrbicurveScalarExtensionOf_result
    (R : Iut.HyperbolicOrbicurve K)
    (stackExtension : SourceEtaleStackScalarExtension F K X.stack)
    (target_stack : R.stack = stackExtension.result)
    (genus_preserved : R.signature.genus = X.signature.genus) :
    (SourceOrbicurveScalarExtensionOf R stackExtension target_stack
      genus_preserved).result = R := rfl

@[simp] theorem SourceOrbicurveScalarExtensionOf_stackExtension
    (R : Iut.HyperbolicOrbicurve K)
    (stackExtension : SourceEtaleStackScalarExtension F K X.stack)
    (target_stack : R.stack = stackExtension.result)
    (genus_preserved : R.signature.genus = X.signature.genus) :
    (SourceOrbicurveScalarExtensionOf R stackExtension target_stack
      genus_preserved).stackExtension = stackExtension := rfl

#check SourceOrbicurveScalarExtensionOf

end LeanFormal.IUT.XiFPaper.S3123SourceOrbicurveScalarExtensionOfActual
end
