import tmp.sheaf.xif.paper.S2495cFUnconditionalActual
import LeanFormal.IUT.IUTI.InitialTheta.SourceDefinition31Quantifiers
import Mathlib.CategoryTheory.Bicategory.FunctorBicategory.Pseudo

noncomputable section
open CategoryTheory
open scoped CategoryTheory.Pseudofunctor.StrongTrans
open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.XiFPaper.S2490RestrictionSectionActual
open LeanFormal.IUT.XiFPaper.S2495cFUnconditionalActual
noncomputable local instance : Field S2490A.K := inferInstance
noncomputable local instance : CommRing S2490A.K := inferInstance
noncomputable local instance : Algebra S2490A.K S2490A.K := Algebra.id S2490A.K
set_option maxHeartbeats 12000000

namespace LeanFormal.IUT.XiFPaper.S2520ScalarExtensionConditional

abbrev K : Type := S2490A.K

/-- The exact missing F=K scalar-extension equivalence. -/
structure S2520ScalarExtensionData where
  fiberEquivalence :
    Bicategory.Equivalence S2495cK.stack.fiber
      ((schemeRestrictScalarsPseudofunctor K K).comp S2495cK.stack.fiber)

noncomputable def S2520StackExtension (D : S2520ScalarExtensionData) :
    SourceEtaleStackScalarExtension K K S2495cK.stack where
  result := S2495cK.stack
  fiberEquivalence := D.fiberEquivalence

noncomputable def S2520OrbicurveExtension (D : S2520ScalarExtensionData) :
    SourceOrbicurveScalarExtension K K S2495cK where
  result := S2495cK
  stackExtension := S2520StackExtension D
  target_stack := rfl
  genus_preserved := rfl

#check S2520StackExtension
#print axioms S2520OrbicurveExtension
end LeanFormal.IUT.XiFPaper.S2520ScalarExtensionConditional
end