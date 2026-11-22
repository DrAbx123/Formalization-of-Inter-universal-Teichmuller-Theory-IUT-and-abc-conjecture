import LeanFormal.IUT.IUTII.Frobenioid.Example36SpecCoverFunctor

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option backward.isDefEq.respectTransparency false

/-!
# Foundation F1e-equivalence: faithfulness and the residual full-equivalence card

Extends `Example36SpecCoverFunctor` (task-80): proves faithfulness of the
actual functor `specCoverFunctor`; fullness and the assembled category
equivalence remain frozen as `SpecCoverFullEquivalenceResidualCard`.

Boundary: field-level Spec/Gamma correspondence only; no curve Pi_1, no
theta/q-pilot claim.
-/

noncomputable section

open CategoryTheory AlgebraicGeometry
open LeanFormal.IUT.IUTII.Frobenioid.Example36.EtaleCoverFoundations
open LeanFormal.IUT.IUTII.Frobenioid.Example36.SpecEssentialSurjectivity
open LeanFormal.IUT.IUTII.Frobenioid.Example36.SpecCoverFunctor

namespace LeanFormal.IUT.IUTII.Frobenioid.Example36.SpecCoverFullEquivalence

universe u

variable (K : Type u) [Field K]

/-- Faithfulness of the plain-`CommAlgCat` Over functor, via `Spec.map_injective`. -/
instance specCoverFunctorCommAlgCat_faithful :
    (specCoverFunctorCommAlgCat K).Faithful where
  map_injective {A B} f g h := by
    have hspec : Spec.map (CommRingCat.ofHom (f.unop.hom.toRingHom)) =
        Spec.map (CommRingCat.ofHom (g.unop.hom.toRingHom)) :=
      congrArg Over.Hom.left h
    have hring : CommRingCat.ofHom (f.unop.hom.toRingHom) =
        CommRingCat.ofHom (g.unop.hom.toRingHom) := Spec.map_injective hspec
    have halg : f.unop.hom = g.unop.hom := by
      apply AlgHom.ext
      intro x
      exact congrArg (fun m => m.hom x) hring
    apply Opposite.unop_injective
    exact CommAlgCat.hom_ext halg

/-- Faithfulness of the finite-etale inclusion. -/
instance finiteEtaleInclusion_faithful : (finiteEtaleInclusion K).Faithful where
  map_injective {A B} f g h := by
    apply Opposite.unop_injective
    exact (ObjectProperty.ι (CommAlgCat.finiteEtale K)).map_injective
      (congrArg Opposite.unop h)

/-- Faithfulness of the restricted Over functor. -/
instance specCoverFunctorOver_faithful : (specCoverFunctorOver K).Faithful := by
  unfold specCoverFunctorOver
  infer_instance

/-- Faithfulness of the actual Spec-cover functor. -/
instance specCoverFunctor_faithful : (specCoverFunctor K).Faithful := by
  unfold specCoverFunctor
  infer_instance

/-- **Frozen residual card.**  Fullness of the actual functor and the
assembled category equivalence.  No inhabitant is provided. -/
structure SpecCoverFullEquivalenceResidualCard (K : Type u) [Field K] where
  /-- Fullness of the actual functor. -/
  full : (specCoverFunctor K).Full
  /-- The assembled equivalence. -/
  equivalence : (CommAlgCat.FiniteEtale K)ᵒᵖ ≌ FiniteEtaleCover (specBase K)
  /-- The equivalence functor is the actual functor. -/
  functor_eq : equivalence.functor = specCoverFunctor K

end LeanFormal.IUT.IUTII.Frobenioid.Example36.SpecCoverFullEquivalence