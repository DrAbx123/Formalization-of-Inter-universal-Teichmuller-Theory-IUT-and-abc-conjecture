import tmp.sheaf.xif.paper.S2495cFUnconditionalActual
import LeanFormal.IUT.IUTI.InitialTheta.SourceDefinition31Quantifiers
import Mathlib.CategoryTheory.Bicategory.FunctorBicategory.Pseudo

noncomputable section
open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.Pseudofunctor.StrongTrans
open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.XiFPaper.S2490RestrictionSectionActual
open LeanFormal.IUT.XiFPaper.S2495cFUnconditionalActual
noncomputable local instance : Field S2490A.K := inferInstance
noncomputable local instance : CommRing S2490A.K := inferInstance
noncomputable local instance : Algebra S2490A.K S2490A.K := Algebra.id S2490A.K
set_option maxHeartbeats 12000000

namespace LeanFormal.IUT.XiFPaper.S2521SchemeRestrictIsoActual

abbrev K : Type := S2490A.K

theorem S2521SpecMapId :
    Spec.map (CommRingCat.ofHom (algebraMap K K : K →+* K)) =
      𝟙 (Spec (CommRingCat.of K)) := by
  rw [Algebra.algebraMap_self]
  change Spec.map (𝟙 (CommRingCat.of K)) = 𝟙 (Spec (CommRingCat.of K))
  rw [Spec.map_id]

/-- The restrict-scalars functor along `K -> K` is isomorphic to the identity
functor. -/
noncomputable def S2521RestrictIso :
    schemeRestrictScalars K K ≅ 𝟭 (Iut.SchemeOverField K) :=
  Over.mapCongr (Spec.map (CommRingCat.ofHom (algebraMap K K : K →+* K)))
    (𝟙 (Spec (CommRingCat.of K))) S2521SpecMapId ≪≫ Over.mapId _

noncomputable def S2521StackExtensionConditional
    (fiberEquivalence :
      Bicategory.Equivalence S2495cK.stack.fiber
        ((schemeRestrictScalarsPseudofunctor K K).comp S2495cK.stack.fiber)) :
    SourceEtaleStackScalarExtension K K S2495cK.stack where
  result := S2495cK.stack
  fiberEquivalence := fiberEquivalence

noncomputable def S2521OrbicurveExtensionConditional
    (fiberEquivalence :
      Bicategory.Equivalence S2495cK.stack.fiber
        ((schemeRestrictScalarsPseudofunctor K K).comp S2495cK.stack.fiber)) :
    SourceOrbicurveScalarExtension K K S2495cK where
  result := S2495cK
  stackExtension := S2521StackExtensionConditional fiberEquivalence
  target_stack := rfl
  genus_preserved := rfl

#check S2521RestrictIso
#print axioms S2521RestrictIso
end LeanFormal.IUT.XiFPaper.S2521SchemeRestrictIsoActual
end