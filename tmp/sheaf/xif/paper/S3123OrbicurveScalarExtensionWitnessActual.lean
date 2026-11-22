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

namespace LeanFormal.IUT.XiFPaper.S3123OrbicurveScalarExtensionWitnessActual

structure S3123OrbicurveScalarExtensionWitness
    (F K : Type u) [Field F] [Field K] [Algebra F K] where
  X : Iut.HyperbolicOrbicurve F
  R : Iut.HyperbolicOrbicurve K
  stackExtension : SourceEtaleStackScalarExtension F K X.stack
  target_stack : R.stack = stackExtension.result
  genus_preserved : R.signature.genus = X.signature.genus

noncomputable def S3123OrbicurveScalarExtensionWitness.toSource
    {F K : Type u} [Field F] [Field K] [Algebra F K]
    (W : S3123OrbicurveScalarExtensionWitness F K) :
    SourceOrbicurveScalarExtension F K W.X :=
  SourceOrbicurveScalarExtensionOf W.R W.stackExtension W.target_stack
    W.genus_preserved

@[simp] theorem S3123OrbicurveScalarExtensionWitness.toSource_result
    {F K : Type u} [Field F] [Field K] [Algebra F K]
    (W : S3123OrbicurveScalarExtensionWitness F K) :
    W.toSource.result = W.R := by
  show (SourceOrbicurveScalarExtensionOf W.R W.stackExtension W.target_stack
    W.genus_preserved).result = W.R
  rfl

@[simp] theorem S3123OrbicurveScalarExtensionWitness.toSource_stackExtension
    {F K : Type u} [Field F] [Field K] [Algebra F K]
    (W : S3123OrbicurveScalarExtensionWitness F K) :
    W.toSource.stackExtension = W.stackExtension := by
  show (SourceOrbicurveScalarExtensionOf W.R W.stackExtension W.target_stack
    W.genus_preserved).stackExtension = W.stackExtension
  rfl

#check S3123OrbicurveScalarExtensionWitness.toSource

end LeanFormal.IUT.XiFPaper.S3123OrbicurveScalarExtensionWitnessActual
end
