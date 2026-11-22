import tmp.sheaf.xif.paper.S3123OrbicurveScalarExtensionWitnessActual

universe u

noncomputable section
open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.Pseudofunctor.StrongTrans
open LeanFormal.IUT
open Iut
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.XiFPaper.S3123OrbicurveScalarExtensionWitnessActual

attribute [local instance] CategoryTheory.Pseudofunctor.StrongTrans.instBicategory

namespace LeanFormal.IUT.XiFPaper.S3123OrbicurveScalarExtensionWitnessNonemptyActual

variable {F K : Type u} [Field F] [Field K] [Algebra F K]

theorem S3123OrbicurveScalarExtensionWitness_nonempty
    (W : S3123OrbicurveScalarExtensionWitness F K) :
    Nonempty (SourceOrbicurveScalarExtension F K W.X) :=
  ⟨W.toSource⟩

theorem S3123OrbicurveScalarExtensionWitness_stack_nonempty
    (W : S3123OrbicurveScalarExtensionWitness F K) :
    Nonempty (SourceEtaleStackScalarExtension F K W.X.stack) :=
  ⟨W.stackExtension⟩

theorem S3123OrbicurveScalarExtensionWitness_genus
    (W : S3123OrbicurveScalarExtensionWitness F K) :
    (Iut.HyperbolicOrbicurve.signature W.R).genus =
      (Iut.HyperbolicOrbicurve.signature W.X).genus := W.genus_preserved

#check S3123OrbicurveScalarExtensionWitness_nonempty
#check S3123OrbicurveScalarExtensionWitness_stack_nonempty
#check S3123OrbicurveScalarExtensionWitness_genus

end LeanFormal.IUT.XiFPaper.S3123OrbicurveScalarExtensionWitnessNonemptyActual
end
