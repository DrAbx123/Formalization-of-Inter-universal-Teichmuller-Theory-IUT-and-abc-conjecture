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
set_option maxHeartbeats 12000000

namespace LeanFormal.IUT.XiFPaper.S2519ScalarExtensionActual

abbrev K : Type := S2490A.K
noncomputable local instance : Field K := inferInstance

/-- The F=K scalar extension of the K-side stack: the restricted-scalars
pseudofunctor is the identity, so the fiber equivalence is the identity
adjoint equivalence. -/
noncomputable def S2519StackExtension :
    SourceEtaleStackScalarExtension K K S2495cK.stack where
  result := S2495cK.stack
  fiberEquivalence := by
    change Bicategory.Equivalence S2495cK.stack.fiber S2495cK.stack.fiber
    exact Bicategory.Equivalence.id S2495cK.stack.fiber

/-- The orbicurve scalar extension in the F=K case, with stack and genus
preserved. -/
noncomputable def S2519OrbicurveExtension :
    SourceOrbicurveScalarExtension K K S2495cK where
  result := S2495cK
  stackExtension := S2519StackExtension
  target_stack := rfl
  genus_preserved := rfl

#check S2519StackExtension
#check S2519OrbicurveExtension
#print axioms S2519StackExtension
#print axioms S2519OrbicurveExtension
end LeanFormal.IUT.XiFPaper.S2519ScalarExtensionActual
end