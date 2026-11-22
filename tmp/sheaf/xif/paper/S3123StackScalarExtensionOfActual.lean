import LeanFormal.IUT.IUTI.InitialTheta.SourceDefinition31Quantifiers

universe u

noncomputable section
open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.Pseudofunctor.StrongTrans
open LeanFormal.IUT
open Iut
open LeanFormal.IUT.InitialThetaSource

attribute [local instance] CategoryTheory.Pseudofunctor.StrongTrans.instBicategory

namespace LeanFormal.IUT.XiFPaper.S3123StackScalarExtensionOfActual

variable {F K : Type u} [Field F] [Field K] [Algebra F K]
variable {X : EtaleStackOverField F}

noncomputable def SourceEtaleStackScalarExtensionOf
    (E : EtaleStackOverField K)
    (eqv : Bicategory.Equivalence E.fiber
      (Pseudofunctor.comp (schemeRestrictScalarsPseudofunctor F K) X.fiber)) :
    SourceEtaleStackScalarExtension F K X :=
  ⟨E, eqv⟩

@[simp] theorem SourceEtaleStackScalarExtensionOf_result
    (E : EtaleStackOverField K)
    (eqv : Bicategory.Equivalence E.fiber
      (Pseudofunctor.comp (schemeRestrictScalarsPseudofunctor F K) X.fiber)) :
    (SourceEtaleStackScalarExtensionOf E eqv).result = E := rfl

@[simp] theorem SourceEtaleStackScalarExtensionOf_fiberEquivalence
    (E : EtaleStackOverField K)
    (eqv : Bicategory.Equivalence E.fiber
      (Pseudofunctor.comp (schemeRestrictScalarsPseudofunctor F K) X.fiber)) :
    (SourceEtaleStackScalarExtensionOf E eqv).fiberEquivalence = eqv := rfl

#check SourceEtaleStackScalarExtensionOf

end LeanFormal.IUT.XiFPaper.S3123StackScalarExtensionOfActual
end
