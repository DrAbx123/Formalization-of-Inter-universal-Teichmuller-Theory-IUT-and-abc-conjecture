import tmp.sheaf.xif.paper.S3123SourceOrbicurveScalarExtensionOfActual

universe u

noncomputable section
open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.Pseudofunctor.StrongTrans
open LeanFormal.IUT
open Iut
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.XiFPaper.S3123SourceOrbicurveScalarExtensionOfActual

attribute [local instance] CategoryTheory.Pseudofunctor.StrongTrans.instBicategory

namespace LeanFormal.IUT.XiFPaper.S3123SourceOrbicurveScalarExtensionOfGenusActual

variable {F K : Type u} [Field F] [Field K] [Algebra F K]
variable {X : Iut.HyperbolicOrbicurve F}

theorem SourceOrbicurveScalarExtensionOf_signature_genus
    (R : Iut.HyperbolicOrbicurve K)
    (stackExtension : SourceEtaleStackScalarExtension F K X.stack)
    (target_stack : R.stack = stackExtension.result)
    (genus_preserved : R.signature.genus = X.signature.genus) :
    (SourceOrbicurveScalarExtensionOf R stackExtension target_stack
      genus_preserved).result.signature.genus = X.signature.genus :=
  genus_preserved

theorem SourceOrbicurveScalarExtensionOf_result_stack
    (R : Iut.HyperbolicOrbicurve K)
    (stackExtension : SourceEtaleStackScalarExtension F K X.stack)
    (target_stack : R.stack = stackExtension.result)
    (genus_preserved : R.signature.genus = X.signature.genus) :
    (SourceOrbicurveScalarExtensionOf R stackExtension target_stack
      genus_preserved).result.stack = stackExtension.result :=
  target_stack

#check SourceOrbicurveScalarExtensionOf_signature_genus
#check SourceOrbicurveScalarExtensionOf_result_stack

end LeanFormal.IUT.XiFPaper.S3123SourceOrbicurveScalarExtensionOfGenusActual
end
