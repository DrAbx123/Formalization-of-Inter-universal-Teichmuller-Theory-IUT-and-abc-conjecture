import LeanFormal.IUT.Foundations.AlgebraicGeometry.FiniteEtaleQuotientGluedCover
import Mathlib.Tactic

set_option relaxedAutoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 2000000

noncomputable section

namespace ABCBridge.RegularPermutationSectionsInvariance

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open LeanFormal.IUT.Foundations.AlgebraicGeometry
open LeanFormal.IUT.Foundations.AlgebraicGeometry.AffineLocalQuotientGluingConstruct
open AffineLocalQuotientGluingConstruct
open LeanFormal.IUT.Foundations.AlgebraicGeometry.FiniteEtaleGroupQuotient
open LeanFormal.IUT.IUTII.Frobenioid.Example36.EtaleCoverFoundations

universe u

variable (R : Type u) [CommRing R] (G : Type u) [Group G] [Fintype G]

/-- The sections algebra map of a cocone over the regular permutation action. -/
noncomputable def sectionsAlgMap
    (c : Cocone (regularPermutationActionFunctor R G)) :
    Γ(c.pt.carrier, ⊤) →+* (G → R) :=
  (Spec.preimage ((c.ι.app (SingleObj.star G)).hom.left ≫
    c.pt.carrier.isoSpec.hom)).hom

/-- Stable-context version of the sections map using the forgetOver left projection. -/
noncomputable def sectionsAlgMapOver
    (c : Cocone (regularPermutationActionFunctor R G)) :
    Γ(c.pt.carrier, ⊤) →+* (G → R) :=
  (Spec.preimage (((FiniteEtaleCover.forgetOver
    (Spec (CommRingCat.of R))).map (c.ι.app (SingleObj.star G))).left ≫
    c.pt.carrier.isoSpec.hom)).hom

lemma sectionsAlgMapOver_spec
    (c : Cocone (regularPermutationActionFunctor R G)) :
    Spec.map (CommRingCat.ofHom (sectionsAlgMapOver R G c)) =
      ((FiniteEtaleCover.forgetOver (Spec (CommRingCat.of R))).map
        (c.ι.app (SingleObj.star G))).left ≫ c.pt.carrier.isoSpec.hom :=
  Spec.map_preimage _

lemma actionEnd_left_eq_specMap (h : G) :
    (regularPermutationActionEnd R G h).hom.left =
      Spec.map (CommRingCat.ofHom
        ((MulSemiringAction.toAlgEquiv R (G → R) h).toRingEquiv.toRingHom)) :=
  rfl

lemma cocone_component_invariant
    (c : Cocone (regularPermutationActionFunctor R G)) (h : G) :
    regularPermutationActionEnd R G h ≫ c.ι.app (SingleObj.star G) =
      c.ι.app (SingleObj.star G) := by
  have hnat := c.ι.naturality (f := (h⁻¹ : G))
    (X := SingleObj.star G) (Y := SingleObj.star G)
  simpa [regularPermutationActionFunctor, Functor.const] using hnat


lemma actionEnd_hom_left_eq_specMap (h : G) :
    (regularPermutationActionEnd R G h).hom.left =
      Spec.map (CommRingCat.ofHom
        ((groupActionRingEquiv (G → R) G h).toRingHom)) := by
  rfl

lemma sectionsAlgMap_spec
    (c : Cocone (regularPermutationActionFunctor R G)) :
    Spec.map (CommRingCat.ofHom (sectionsAlgMap R G c)) =
      (c.ι.app (SingleObj.star G)).hom.left ≫ c.pt.carrier.isoSpec.hom :=
  Spec.map_preimage _

lemma action_specMap_comp_component
    (c : Cocone (regularPermutationActionFunctor R G)) (h : G) :
    (regularPermutationActionEnd R G h).hom.left ≫
        (c.ι.app (SingleObj.star G)).hom.left =
      (c.ι.app (SingleObj.star G)).hom.left := by
  have hinv := cocone_component_invariant (R := R) (G := G) c h
  have hleft := congrArg (fun f : regularPermutationCover R G ⟶ c.pt => f.hom.left) hinv
  change (regularPermutationActionEnd R G h).hom.left ≫
      (c.ι.app (SingleObj.star G)).hom.left =
    (c.ι.app (SingleObj.star G)).hom.left at hleft
  exact hleft

lemma sectionsAlgMap_invariant
    (c : Cocone (regularPermutationActionFunctor R G)) (h : G)
    (b : Γ(c.pt.carrier, ⊤)) :
    groupActionRingEquiv (G → R) G h (sectionsAlgMap R G c b) =
      sectionsAlgMap R G c b := by
  let φ : Γ(c.pt.carrier, ⊤) →+* (G → R) := sectionsAlgMap R G c
  have hspec : Spec.map (CommRingCat.ofHom
        ((groupActionRingEquiv (G → R) G h).toRingHom.comp φ)) =
      Spec.map (CommRingCat.ofHom φ) := by
    rw [CommRingCat.ofHom_comp, Spec.map_comp]
    rw [sectionsAlgMap_spec, ← actionEnd_hom_left_eq_specMap]
    exact (Category.assoc
      (regularPermutationActionEnd R G h).hom.left
      (c.ι.app (SingleObj.star G)).hom.left
      c.pt.carrier.isoSpec.hom).symm.trans
      (congrArg (fun f => f ≫ c.pt.carrier.isoSpec.hom)
        (action_specMap_comp_component (R := R) (G := G) c h))
  have hring : (groupActionRingEquiv (G → R) G h).toRingHom.comp φ = φ := by
    have hcat := Spec.map_injective hspec
    exact congrArg (fun f : CommRingCat.of Γ(c.pt.carrier, ⊤) ⟶
      CommRingCat.of (G → R) => f.hom) hcat
  exact congrFun (congrArg (fun f : Γ(c.pt.carrier, ⊤) →+* (G → R) =>
    (f : Γ(c.pt.carrier, ⊤) → (G → R))) hring) b

end ABCBridge.RegularPermutationSectionsInvariance