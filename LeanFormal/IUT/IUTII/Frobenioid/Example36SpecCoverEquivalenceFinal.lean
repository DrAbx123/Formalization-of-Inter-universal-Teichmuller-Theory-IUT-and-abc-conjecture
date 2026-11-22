import LeanFormal.IUT.IUTII.Frobenioid.Example36SpecCoverFullEquivalence

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option backward.isDefEq.respectTransparency false

/-!
# Foundation F1e-equivalence: fullness and the assembled Spec-cover equivalence

Builds on task-86 (faithfulness): proves fullness of the plain-CommAlgCat Over
functor via `Spec.fullyFaithful.preimage` and the Over triangle, then Full for
the restricted and lifted functors, assembles the equivalence
`(CommAlgCat.FiniteEtale K)ᵒᵖ ≌ FiniteEtaleCover (Spec K)` and inhabits the
residual card.

Boundary: field-level Spec/Gamma correspondence only; no curve Pi_1, no
theta/q-pilot claim.
-/

noncomputable section

open CategoryTheory AlgebraicGeometry
open LeanFormal.IUT.IUTII.Frobenioid.Example36.EtaleCoverFoundations
open LeanFormal.IUT.IUTII.Frobenioid.Example36.SpecEssentialSurjectivity
open LeanFormal.IUT.IUTII.Frobenioid.Example36.SpecCoverFunctor
open LeanFormal.IUT.IUTII.Frobenioid.Example36.SpecCoverFullEquivalence

namespace LeanFormal.IUT.IUTII.Frobenioid.Example36.SpecCoverEquivalenceFinal

universe u

variable (K : Type u) [Field K]

/-- The K-algebra map `B → A` underlying an Over morphism of the Spec covers. -/
noncomputable def overHomToAlgHom {A B : (CommAlgCat.{u} K)ᵒᵖ}
    (φ : (specCoverFunctorCommAlgCat K).obj A ⟶ (specCoverFunctorCommAlgCat K).obj B) :
    B.unop →ₐ[K] A.unop := by
  classical
  let ψ : CommRingCat.of B.unop ⟶ CommRingCat.of A.unop :=
    (Spec.fullyFaithful.preimage (Over.Hom.left φ)).unop
  have hψ : Spec.map ψ = Over.Hom.left φ :=
    Spec.fullyFaithful.map_preimage (Over.Hom.left φ)
  have hB : ((specCoverFunctorCommAlgCat K).obj B).hom = commAlgCatStructureMap K B.unop := rfl
  have hA : ((specCoverFunctorCommAlgCat K).obj A).hom = commAlgCatStructureMap K A.unop := rfl
  have hw : ∀ x, ψ.hom (algebraMap K B.unop x) = algebraMap K A.unop x := by
    intro x
    have h := φ.w
    rw [← hψ, hB, hA, commAlgCatStructureMap, commAlgCatStructureMap] at h
    erw [← Spec.map_comp] at h
    have h' : CommRingCat.ofHom (algebraMap K B.unop) ≫ ψ =
        CommRingCat.ofHom (algebraMap K A.unop) := Spec.map_inj.mp h
    simpa using congrArg (fun m => m.hom x) h'
  exact { toRingHom := ψ.hom, commutes' := hw }

/-- Fullness of the plain-`CommAlgCat` Over functor. -/
instance specCoverFunctorCommAlgCat_full :
    (specCoverFunctorCommAlgCat K).Full where
  map_surjective {A B} φ :=
    ⟨(CommAlgCat.ofHom (overHomToAlgHom K φ)).op, by
      apply Over.OverMorphism.ext
      change Spec.map (CommRingCat.ofHom ((overHomToAlgHom K φ).toRingHom)) =
        Over.Hom.left φ
      rw [← Spec.fullyFaithful.map_preimage (Over.Hom.left φ)]
      apply Spec.map_inj.mpr
      rw [show (overHomToAlgHom K φ).toRingHom =
          (Spec.fullyFaithful.preimage (Over.Hom.left φ)).unop.hom from rfl]
      rfl⟩

/-- Fullness of the finite-etale inclusion (via `ObjectProperty.ι` and op). -/
instance finiteEtaleInclusion_full : (finiteEtaleInclusion K).Full := by
  unfold finiteEtaleInclusion
  infer_instance

instance specCoverFunctorOver_full : (specCoverFunctorOver K).Full := by
  unfold specCoverFunctorOver
  infer_instance

instance specCoverFunctor_full : (specCoverFunctor K).Full := by
  unfold specCoverFunctor
  infer_instance

/-- The actual functor is an equivalence (Full + Faithful + EssSurj). -/
instance specCoverFunctor_isEquivalence : (specCoverFunctor K).IsEquivalence where
  faithful := inferInstance
  full := inferInstance
  essSurj := specCoverFunctor_essentially_surjective K

/-- The assembled category equivalence. -/
noncomputable def specCoverEquivalence :
    (CommAlgCat.FiniteEtale.{u} K)ᵒᵖ ≌ FiniteEtaleCover (specBase K) :=
  (specCoverFunctor K).asEquivalence

/-- The residual card of task-86 is now inhabited. -/
def specCoverFullEquivalenceCard : SpecCoverFullEquivalenceCard K where
  full_faithful := ⟨inferInstance, inferInstance⟩
  equivalence := specCoverEquivalence K
  functor_eq := rfl

end LeanFormal.IUT.IUTII.Frobenioid.Example36.SpecCoverEquivalenceFinal