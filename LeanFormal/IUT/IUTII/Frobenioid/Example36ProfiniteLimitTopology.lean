/-
Copyright (c) 2026 LeanFormal contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanFormal IUT/ABC contributors
-/
import Mathlib.Topology.Algebra.Category.ProfiniteGrp.Basic
import Mathlib.Tactic

set_option linter.unusedSectionVars false

/-!
# Initial topology of the bundled profinite-group limit

Task task-121.  Mathlib constructs the limit of a diagram of profinite groups as
the limit of the underlying profinite spaces (ProfiniteGrp.limitCone).  This
module proves that the topology of the bundled limit is the initial topology of
the projections to the finite levels:

* profiniteLimitHomeomorphTopCatLimit: the bundled limit point is the TopCat
  limit subtype of compatible families (homeomorphism, identity on underlying
  elements);
* profiniteLimitProjectionMap: the projection map to the product of the finite
  levels;
* continuous_into_profiniteGrpLimit_iff: a map into the bundled limit is
  continuous if and only if all composites with the projections are continuous
  (the initial-topology universal property);
* profiniteLimitProjectionMap_isClosedEmbedding: the projection map is a closed
  embedding (continuous injective from a compact space to a Hausdorff space).

The last two results give the missing topology API for the joint continuity of
the pro-2 Tate module action in Example36TateGaloisAction.lean.
-/

noncomputable section

namespace LeanFormal.IUT.IUTII.Frobenioid
namespace ProfiniteLimitTopology

open CategoryTheory CategoryTheory.Limits

universe v u

variable {J : Type v} [SmallCategory J]

/-- The TopCat limit subtype of compatible families underlying the bundled
profinite-group limit. -/
abbrev profiniteLimitPointModel (F : J ⥤ ProfiniteGrp.{max v u}) : Type (max v u) :=
  ↑(TopCat.limitCone (F ⋙ forget₂ ProfiniteGrp Profinite ⋙ Profinite.toTopCat)).pt

/-- The underlying type of the bundled limit is the TopCat limit subtype. -/
theorem profiniteLimit_type_eq_model (F : J ⥤ ProfiniteGrp.{max v u}) :
    (↑(ProfiniteGrp.limitCone F).pt : Type (max v u)) =
      profiniteLimitPointModel F :=
  rfl

/-- The identity between the bundled limit and the TopCat limit model is a
homeomorphism. -/
noncomputable def profiniteLimitHomeomorphTopCatLimit
    (F : J ⥤ ProfiniteGrp.{max v u}) :
    (↑(ProfiniteGrp.limitCone F).pt : Type (max v u)) ≃ₜ
      profiniteLimitPointModel F :=
  Homeomorph.refl _

/-- The projection map from the bundled limit to the product of the finite
levels (the values of the limit projections). -/
noncomputable def profiniteLimitProjectionMap
    (F : J ⥤ ProfiniteGrp.{max v u}) :
    (↑(ProfiniteGrp.limitCone F).pt : Type (max v u)) →
      ((j : J) → ↑(F.obj j)) :=
  fun x j => (ProfiniteGrp.limitCone F).π.app j x

/-- The projection map is continuous. -/
theorem profiniteLimitProjectionMap_continuous
    (F : J ⥤ ProfiniteGrp.{max v u}) :
    Continuous (profiniteLimitProjectionMap F) := by
  apply continuous_pi
  intro j
  exact ((ProfiniteGrp.limitCone F).π.app j).hom.2

/-- The projection map is injective: the limit projections separate points. -/
theorem profiniteLimitProjectionMap_injective
    (F : J ⥤ ProfiniteGrp.{max v u}) :
    Function.Injective (profiniteLimitProjectionMap F) := by
  intro x y hxy
  apply Subtype.ext
  funext j
  exact congrFun hxy j

/-- The projection map is a closed embedding: continuous and injective from a
compact space into a Hausdorff product. -/
theorem profiniteLimitProjectionMap_isClosedEmbedding
    (F : J ⥤ ProfiniteGrp.{max v u}) :
    Topology.IsClosedEmbedding (profiniteLimitProjectionMap F) :=
  Continuous.isClosedEmbedding (profiniteLimitProjectionMap_continuous F)
    (profiniteLimitProjectionMap_injective F)

/-- **Continuity from projection continuity.**  A map into the bundled limit is
continuous as soon as all its composites with the limit projections are
continuous. -/
theorem continuous_into_profiniteGrpLimit_of_projections {X : Type*}
    [TopologicalSpace X]
    (F : J ⥤ ProfiniteGrp.{max v u})
    (f : X → (↑(ProfiniteGrp.limitCone F).pt : Type (max v u)))
    (h : ∀ j : J, Continuous
      (fun x : X => (ProfiniteGrp.limitCone F).π.app j (f x))) :
    Continuous f := by
  have hv : Continuous
      (fun x : X => fun j : J =>
        (ProfiniteGrp.limitCone F).π.app j (f x)) := by
    rw [continuous_pi_iff]
    exact h
  have hmem : ∀ x : X,
      (fun j : J => (ProfiniteGrp.limitCone F).π.app j (f x)) ∈
        ProfiniteGrp.limitConePtAux F := by
    intro x i j π
    exact (ProfiniteGrp.limitCone F).w_apply π (f x)
  have hsub : Continuous
      (fun x : X =>
        (⟨(fun j : J => (ProfiniteGrp.limitCone F).π.app j (f x)),
          hmem x⟩ : ↑(ProfiniteGrp.limitConePtAux F))) :=
    Continuous.subtype_mk hv hmem
  have hfun : (fun x : X =>
        (⟨(fun j : J => (ProfiniteGrp.limitCone F).π.app j (f x)),
          hmem x⟩ : ↑(ProfiniteGrp.limitConePtAux F))) =
      (fun x : X =>
        ((f x : ↑(ProfiniteGrp.limitCone F).pt) :
          ↑(ProfiniteGrp.limitConePtAux F))) := by
    funext x
    apply Subtype.ext
    funext j
    rfl
  have hcont2 : Continuous
      (fun x : X =>
        ((f x : ↑(ProfiniteGrp.limitCone F).pt) :
          ↑(ProfiniteGrp.limitConePtAux F))) := by
    rw [← hfun]
    exact hsub
  exact hcont2

/-- **Initial topology of the bundled limit.**  A map into the bundled limit is
continuous if and only if all its composites with the limit projections are
continuous. -/
theorem continuous_into_profiniteGrpLimit_iff {X : Type*} [TopologicalSpace X]
    (F : J ⥤ ProfiniteGrp.{max v u})
    (f : X → (↑(ProfiniteGrp.limitCone F).pt : Type (max v u))) :
    Continuous f ↔
      ∀ j : J, Continuous
        (fun x : X => (ProfiniteGrp.limitCone F).π.app j (f x)) :=
  ⟨fun hf j => ((ProfiniteGrp.limitCone F).π.app j).hom.2.comp hf,
    continuous_into_profiniteGrpLimit_of_projections F f⟩

end ProfiniteLimitTopology
end LeanFormal.IUT.IUTII.Frobenioid
