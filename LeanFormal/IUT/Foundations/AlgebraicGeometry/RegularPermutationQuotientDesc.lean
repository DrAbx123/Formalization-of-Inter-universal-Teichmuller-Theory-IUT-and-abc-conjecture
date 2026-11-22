import LeanFormal.IUT.Foundations.AlgebraicGeometry.RegularPermutationActionColimit
import LeanFormal.IUT.Foundations.AlgebraicGeometry.AffineFixedPointDescNormalForm
import Mathlib.Tactic

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open LeanFormal.IUT.IUTII.Frobenioid.Example36.EtaleCoverFoundations
open LeanFormal.IUT.Foundations.AlgebraicGeometry.FiniteEtaleGroupQuotient
open LeanFormal.IUT.Foundations.AlgebraicGeometry.AffineLocalQuotientGluingConstruct
open AffineLocalQuotientGluingConstruct

noncomputable section

namespace ABCBridge.RegularPermutationQuotientDesc

universe u

variable {R : Type u} [CommRing R] {G : Type u} [Group G] [Fintype G]

noncomputable def descPhi
    (c : Cocone (regularPermutationActionFunctor R G)) :
    Γ(c.pt.carrier, ⊤) →ₐ[R] (G → R) :=
  RegularPermutationActionColimit.sectionsAlgMapAlgHom c

noncomputable def descPsi0
    (c : Cocone (regularPermutationActionFunctor R G)) :
    Γ(c.pt.carrier, ⊤) →ₐ[R] fixedPointSubalgebra R (G → R) G :=
  Classical.choose
    (ABCBridge.AffineFixedPointDescNormalForm.exists_affineFixedPointLiftAlgHom
      (R := R) (A := (G → R)) (B := Γ(c.pt.carrier, ⊤)) (G := G)
      (descPhi c)
      (RegularPermutationActionColimit.sectionsAlgMapAlgHom_invariant c))

lemma descPsi0_spec
    (c : Cocone (regularPermutationActionFunctor R G)) :
    (fixedPointInclusion R (G → R) G).comp (descPsi0 c) = descPhi c :=
  (Classical.choose_spec
    (ABCBridge.AffineFixedPointDescNormalForm.exists_affineFixedPointLiftAlgHom
      (R := R) (A := (G → R)) (B := Γ(c.pt.carrier, ⊤)) (G := G)
      (descPhi c)
      (RegularPermutationActionColimit.sectionsAlgMapAlgHom_invariant c))).1

lemma descPsi0_commutes
    (c : Cocone (regularPermutationActionFunctor R G)) :
    (descPsi0 c).toRingHom.comp (algebraMap R Γ(c.pt.carrier, ⊤)) =
      algebraMap R (fixedPointSubalgebra R (G → R) G) :=
  (Classical.choose_spec
    (ABCBridge.AffineFixedPointDescNormalForm.exists_affineFixedPointLiftAlgHom
      (R := R) (A := (G → R)) (B := Γ(c.pt.carrier, ⊤)) (G := G)
      (descPhi c)
      (RegularPermutationActionColimit.sectionsAlgMapAlgHom_invariant c))).2


lemma descPsi0_unique
    (c : Cocone (regularPermutationActionFunctor R G))
    (ψ : Γ(c.pt.carrier, ⊤) →ₐ[R] fixedPointSubalgebra R (G → R) G)
    (hψ : (fixedPointInclusion R (G → R) G).comp ψ = descPhi c) :
    ψ = descPsi0 c := by
  let uni : Γ(c.pt.carrier, ⊤) →ₐ[R] fixedPointSubalgebra R (G → R) G :=
    Classical.choose
      (ABCBridge.InvariantsGeneralAssembly.affineFixedPointQuotient_universal
        R (G → R) G (descPhi c)
        (RegularPermutationActionColimit.sectionsAlgMapAlgHom_invariant c))
  have hdesc : descPsi0 c = uni :=
    (Classical.choose_spec
      (ABCBridge.InvariantsGeneralAssembly.affineFixedPointQuotient_universal
        R (G → R) G (descPhi c)
        (RegularPermutationActionColimit.sectionsAlgMapAlgHom_invariant c))).2
      (descPsi0 c) (descPsi0_spec c)
  have huniq : ψ = uni :=
    (Classical.choose_spec
      (ABCBridge.InvariantsGeneralAssembly.affineFixedPointQuotient_universal
        R (G → R) G (descPhi c)
        (RegularPermutationActionColimit.sectionsAlgMapAlgHom_invariant c))).2 ψ hψ
  exact huniq.trans hdesc.symm

noncomputable def descF
    (c : Cocone (regularPermutationActionFunctor R G)) :
    (regularPermutationQuotientCover R G).carrier ⟶ c.pt.carrier :=
  ABCBridge.AffineFixedPointDescNormalForm.descSchemeMap
    (R := R) (A := (G → R)) (G := G) (Z := c.pt) (descPsi0 c)

lemma descW
    (c : Cocone (regularPermutationActionFunctor R G)) :
    descF c ≫ c.pt.structureMap =
      (regularPermutationQuotientCover R G).structureMap := by
  have h := ABCBridge.AffineFixedPointDescNormalForm.descSchemeMap_structureMap
    (R := R) (A := (G → R)) (G := G) (Z := c.pt) (descPsi0 c) (descPsi0_commutes c)
  change descF c ≫ c.pt.structureMap =
    Spec.map (CommRingCat.ofHom
      (algebraMap R (fixedPointSubalgebra R (G → R) G)))
  exact h

noncomputable def desc
    (c : Cocone (regularPermutationActionFunctor R G)) :
    regularPermutationQuotientCover R G ⟶ c.pt :=
  finiteEtaleCoverHomMk (descF c) (descW c)

end ABCBridge.RegularPermutationQuotientDesc
