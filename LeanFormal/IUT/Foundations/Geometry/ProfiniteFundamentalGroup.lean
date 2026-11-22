/-
Copyright (c) 2026 LeanFormal contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanFormal IUT/ABC contributors
-/
import Mathlib.Topology.Algebra.Category.ProfiniteGrp.Completion
import LeanFormal.IUT.Foundations.Geometry.PuncturedEllipticCurve
import Iut.Foundations.Orbicurve
import Mathlib.Tactic

set_option linter.unusedSectionVars false

/-!
# Profinite completion of fundamental groups and the curve Pi_v interface

Task task-128 infrastructure.  This module provides:

* the profinite completion of an (abstract or topological) group, using
  Mathlib's actual construction as a limit of finite quotients
  (ProfiniteGrp.ProfiniteCompletion), together with its canonical map, its
  universal property, dense range, residual-finiteness injectivity criterion,
  and the fact that the completion of a surjective homomorphism is surjective;
* the arithmetic/geometric Pi_v interface for a once-punctured elliptic curve:
  an abstract/topological fundamental group with a surjective homomorphism to a
  profinite Galois group, its profinite completion Pi_v, the projection to the
  Galois group, the geometric kernel, and the criterion that a nontrivial
  element of the abstract kernel survives in the completed geometric kernel;
* an anabelioid interface bundling a punctured elliptic curve with a chosen
  Iut.EtaleFundamentalGroup and a surjective comparison map to a profinite
  Galois group;
* the concrete free-group model of the geometric fundamental group of a
  once-punctured genus-one curve (free group on two generators), for which
  injectivity of the canonical map to the profinite completion is equivalent to
  residual finiteness of the free group (the residual-finiteness instance itself
  is the exact missing Mathlib API).

## Exact missing API

Mathlib 4.32.2 contains the profinite completion of abstract groups
(Mathlib.Topology.Algebra.Category.ProfiniteGrp.Completion), but it does NOT
contain:

* an etale fundamental group of a scheme or of a curve (there is a concrete
  category of finite etale covers of a scheme and the field-side Galois
  category in the tree, but no pi_1^et of a curve);
* a curve-to-anabelioid functor (i.e. the assignment from a curve to its Galois
  category/pointed fiber functor with the full IsFundamentalGroup certificate);
* a tempered fundamental group, or a free profinite group on two generators;
* the residual-finiteness instance for the free group on two generators
  (residual finiteness of free groups is classical, but the instance is absent),
  so injectivity of the free-group eta is stated conditionally;
* a residual-finiteness instance for profinite groups (supplied here as the
  theorem residuallyFinite_of_profinite, with injectivity of the canonical map
  from a profinite group to its completion);
* an unconditional identification of the profinite completion of a profinite
  group with the group itself (the completion is over all finite-index normal
  subgroups, while a profinite group is the limit over open normal subgroups;
  the comparison requires strong completeness, and Mathlib has no comparison of
  the two diagrams); only the general residual-finiteness/injectivity statements
  are included here.
* the geometric action of the etale fundamental group on the local value
  monoid of the source F-prime-strip.

Consequently no actual curve Pi_v instance is constructed here; the interface
below is the exact shape which a future construction must inhabit.  No card,
unproved placeholder or assumption is used.
-/

noncomputable section

open CategoryTheory

namespace LeanFormal.IUT.Foundations.Geometry

open LeanFormal.IUT

universe u

/-! ## 1. Profinite completion of a group -/

/-- The profinite completion of an abstract group: the limit of its finite
quotients (Mathlib's ProfiniteGrp.ProfiniteCompletion.completion). -/
noncomputable abbrev profiniteCompletionOfGroup (G : GrpCat.{u}) :
    ProfiniteGrp.{u} :=
  ProfiniteGrp.ProfiniteCompletion.completion G

/-- The canonical homomorphism from a group to its profinite completion. -/
noncomputable abbrev profiniteCompletionEta (G : GrpCat.{u}) :
    G ⟶ GrpCat.of (profiniteCompletionOfGroup G) :=
  ProfiniteGrp.ProfiniteCompletion.eta G

/-- The universal morphism from the profinite completion of G to a profinite
group P, induced by a homomorphism G -> P. -/
noncomputable abbrev profiniteCompletionLift {G : GrpCat.{u}} {P : ProfiniteGrp.{u}}
    (f : G ⟶ GrpCat.of P) : profiniteCompletionOfGroup G ⟶ P :=
  ProfiniteGrp.ProfiniteCompletion.lift f

/-- The universal morphism extends the given homomorphism on the dense image of
the canonical map. -/
theorem profiniteCompletionLift_eta {G : GrpCat.{u}} {P : ProfiniteGrp.{u}}
    (f : G ⟶ GrpCat.of P) (g : G) :
    profiniteCompletionLift f (profiniteCompletionEta G g) = f g := by
  have h := ProfiniteGrp.ProfiniteCompletion.lift_eta f
  exact ConcreteCategory.congr_hom h g

/-- The canonical map from a group to its profinite completion has dense
range. -/
theorem profiniteCompletionEta_denseRange (G : GrpCat.{u}) :
    DenseRange (profiniteCompletionEta G) :=
  ProfiniteGrp.ProfiniteCompletion.denseRange G

/-- The canonical map to the profinite completion is injective if and only if
the group is residually finite. -/
theorem profiniteCompletionEta_injective_iff_residuallyFinite (G : GrpCat.{u}) :
    Function.Injective (profiniteCompletionEta G) ↔ Group.ResiduallyFinite G :=
  ProfiniteGrp.ProfiniteCompletion.etaFn_injective_iff_residuallyFinite G

/-- Two morphisms out of the profinite completion are equal if they agree on the
dense image of the canonical map. -/
theorem profiniteCompletionLift_unique {G : GrpCat.{u}} {P : ProfiniteGrp.{u}}
    (f g : profiniteCompletionOfGroup G ⟶ P)
    (h : ∀ x : G, f (profiniteCompletionEta G x) = g (profiniteCompletionEta G x)) :
    f = g := by
  apply ProfiniteGrp.ProfiniteCompletion.lift_unique
  ext x
  exact h x

/-- The completion of a surjective homomorphism of groups is surjective onto the
target profinite group. -/
theorem profiniteCompletionLift_surjective {G : GrpCat.{u}} {P : ProfiniteGrp.{u}}
    (f : G ⟶ GrpCat.of P) (hf : Function.Surjective f) :
    Function.Surjective (profiniteCompletionLift f) := by
  intro p
  obtain ⟨g, rfl⟩ := hf p
  exact ⟨profiniteCompletionEta G g, profiniteCompletionLift_eta f g⟩

/-- The profinite completion functor on abstract groups. -/
noncomputable abbrev profiniteCompletionFunctor : GrpCat.{u} ⥤ ProfiniteGrp.{u} :=
  ProfiniteGrp.profiniteCompletion

/-! ## 2. Profinite completion of a topological group -/

/-- The profinite completion of a topological group, taken on the underlying
abstract group. -/
noncomputable abbrev profiniteCompletionOfTopologicalGroup
    (G : Type u) [Group G] [TopologicalSpace G] : ProfiniteGrp.{u} :=
  profiniteCompletionOfGroup (GrpCat.of G)

/-- The canonical map from a topological group to its profinite completion. -/
noncomputable abbrev profiniteCompletionOfTopologicalGroupEta
    (G : Type u) [Group G] [TopologicalSpace G] :
    G → profiniteCompletionOfTopologicalGroup G :=
  profiniteCompletionEta (GrpCat.of G)

/-- The canonical map from a topological group to its profinite completion has
dense range. -/
theorem profiniteCompletionOfTopologicalGroupEta_denseRange
    (G : Type u) [Group G] [TopologicalSpace G] :
    DenseRange (profiniteCompletionOfTopologicalGroupEta G) :=
  profiniteCompletionEta_denseRange (GrpCat.of G)

/-- The canonical map from a topological group to its profinite completion is
injective if and only if the underlying group is residually finite. -/
theorem profiniteCompletionOfTopologicalGroupEta_injective_iff_residuallyFinite
    (G : Type u) [Group G] [TopologicalSpace G] :
    Function.Injective (profiniteCompletionOfTopologicalGroupEta G) ↔
      Group.ResiduallyFinite G :=
  profiniteCompletionEta_injective_iff_residuallyFinite (GrpCat.of G)

/-! ## 2b. Residual finiteness of profinite groups (missing instance in Mathlib) -/

/-- A profinite group is residually finite as an abstract group.  Mathlib
4.32.2 does not provide this as an instance; the proof separates a non-identity
element by an open normal subgroup (whose index is finite by compactness). -/
theorem residuallyFinite_of_profinite (P : ProfiniteGrp.{u}) :
    Group.ResiduallyFinite P := by
  rw [Group.residuallyFinite_iff_forall_finiteIndexNormalSubgroup]
  intro g hg
  by_contra hne
  obtain ⟨H, hH⟩ := ProfiniteGrp.exist_openNormalSubgroup_sub_open_nhds_of_one
    (U := ({g}ᶜ : Set P)) isOpen_compl_singleton (by
      simpa [Set.mem_compl_singleton_iff, eq_comm] using hne)
  exact hH (hg H.toFiniteIndexNormalSubgroup) rfl

/-- The underlying function of the canonical map from a profinite group to its
profinite completion is injective, because a profinite group is residually
finite. -/
theorem profiniteCompletionEtaFn_injective_of_profinite (P : ProfiniteGrp.{u}) :
    Function.Injective (ProfiniteGrp.ProfiniteCompletion.etaFn (GrpCat.of P)) :=
  (ProfiniteGrp.ProfiniteCompletion.etaFn_injective_iff_residuallyFinite
    (GrpCat.of P)).mpr (residuallyFinite_of_profinite P)

/-- The canonical morphism from a profinite group to its profinite completion is
injective. -/
theorem profiniteCompletionEta_injective_of_profinite (P : ProfiniteGrp.{u}) :
    Function.Injective (profiniteCompletionEta (GrpCat.of P)) := by
  change Function.Injective
    (ProfiniteGrp.ProfiniteCompletion.etaFn (GrpCat.of P))
  exact profiniteCompletionEtaFn_injective_of_profinite P

/-! ## 3. The curve Pi_v interface -/

/-- The Pi_v interface for a once-punctured elliptic curve over a field K: an
abstract/topological fundamental group gamma of the curve, a profinite Galois
group, and a surjective homomorphism gamma -> galois.  The completed Pi_v, the
projection and the geometric kernel are derived below. -/
structure CurvePiOneInterface (K : Type u) [Field K] where
  /-- The once-punctured elliptic curve. -/
  curve : PuncturedEllipticCurve K
  /-- The abstract/topological fundamental group of the curve (a model of the
  etale or tempered fundamental group). -/
  gamma : GrpCat.{u}
  /-- The profinite Galois group of the base field. -/
  galois : ProfiniteGrp.{u}
  /-- The homomorphism from the fundamental group to the Galois group. -/
  projAbstract : gamma ⟶ GrpCat.of galois
  /-- It is surjective: the curve Pi_v surjects onto the local Galois group. -/
  projAbstract_surjective : Function.Surjective projAbstract

namespace CurvePiOneInterface

variable {K : Type u} [Field K] (I : CurvePiOneInterface K)

/-- The profinite group Pi_v of the curve: the profinite completion of its
abstract fundamental group. -/
noncomputable abbrev piOne : ProfiniteGrp.{u} :=
  profiniteCompletionOfGroup I.gamma

/-- The canonical map from the abstract fundamental group to Pi_v. -/
noncomputable abbrev toPiOne : I.gamma → I.piOne :=
  profiniteCompletionEta I.gamma

/-- The projection from the curve Pi_v to the Galois group, obtained from the
abstract homomorphism by the universal property of the completion. -/
noncomputable abbrev projection : I.piOne ⟶ I.galois :=
  profiniteCompletionLift I.projAbstract

/-- The projection is surjective. -/
theorem projection_surjective : Function.Surjective I.projection :=
  profiniteCompletionLift_surjective I.projAbstract I.projAbstract_surjective

/-- The geometric kernel of Pi_v: the kernel of the projection to the Galois
group.  In the source it is the geometric fundamental group of the curve. -/
noncomputable def geometricKernel : Subgroup (I.piOne : Type u) :=
  I.projection.hom.toMonoidHom.ker

/-- The geometric kernel is trivial exactly when the projection is injective. -/
theorem geometricKernel_eq_bot_iff :
    I.geometricKernel = ⊥ ↔ Function.Injective I.projection :=
  MonoidHom.ker_eq_bot_iff I.projection.hom.toMonoidHom

/-- If the canonical map to the completion is injective and the abstract
projection kills a nontrivial element of the fundamental group, then the
completed geometric kernel is nontrivial. -/
theorem geometricKernel_ne_bot_of_eta_injective
    (heta : Function.Injective I.toPiOne) {x : I.gamma}
    (hx : x ≠ 1) (hker : I.projAbstract x = 1) :
    I.geometricKernel ≠ ⊥ := by
  have hmem : I.toPiOne x ∈ I.geometricKernel := by
    change I.projection.hom.toMonoidHom (I.toPiOne x) = 1
    have hproj : I.projection.hom.toMonoidHom (I.toPiOne x) = I.projAbstract x :=
      profiniteCompletionLift_eta I.projAbstract x
    rw [hproj, hker]
  have hne : I.toPiOne x ≠ 1 := by
    intro h
    apply hx
    apply heta
    simpa using h
  intro hbot
  rw [hbot] at hmem
  exact hne (by simpa using hmem)

end CurvePiOneInterface

/-! ## 4. The anabelioid interface for a punctured elliptic curve -/

/-- The anabelioid interface of a once-punctured elliptic curve: a chosen
Iut.EtaleFundamentalGroup for the curve together with a profinite Galois group
and a surjective comparison homomorphism from its fundamental group. -/
structure CurveAnabelioidInterface (K : Type u) [Field K] where
  /-- The once-punctured elliptic curve. -/
  curve : PuncturedEllipticCurve K
  /-- The chosen Galois category/fiber functor/fundamental group of the curve. -/
  anabelioid : Iut.EtaleFundamentalGroup
  /-- The profinite Galois group of the base field. -/
  galois : ProfiniteGrp.{u}
  /-- The comparison homomorphism from the curve fundamental group to the
  Galois group. -/
  comparison : anabelioid.group ⟶ galois
  /-- It is surjective. -/
  comparison_surjective : Function.Surjective comparison

namespace CurveAnabelioidInterface

variable {K : Type u} [Field K] (I : CurveAnabelioidInterface K)

/-- The geometric kernel of the anabelioid fundamental group as a subgroup of
the curve fundamental group. -/
noncomputable def geometricKernel : Subgroup (I.anabelioid.group : Type u) :=
  I.comparison.hom.toMonoidHom.ker

/-- The geometric kernel is trivial exactly when the comparison is injective. -/
theorem geometricKernel_eq_bot_iff :
    I.geometricKernel = ⊥ ↔ Function.Injective I.comparison :=
  MonoidHom.ker_eq_bot_iff I.comparison.hom.toMonoidHom

end CurveAnabelioidInterface


/-! ## 5. The free-group geometric Pi_v model -/

namespace FreeGroupModel

/-- The standard topological model of the geometric fundamental group of a
once-punctured genus-one curve over the complex numbers: the free group on two
generators (a once-punctured genus-one curve has the homotopy type of a wedge of
two circles).  This is a topological model, not a curve and not an etale Pi_v;
no curve-to-group functor is asserted. -/
noncomputable abbrev geometricPiOneModel : GrpCat.{0} :=
  GrpCat.of (FreeGroup (Fin 2))

/-- For the free-group model, injectivity of the canonical map to the profinite
completion is equivalent to residual finiteness of the free group. -/
theorem eta_injective_iff :
    Function.Injective (profiniteCompletionEta geometricPiOneModel) ↔
      Group.ResiduallyFinite (FreeGroup (Fin 2)) :=
  profiniteCompletionEta_injective_iff_residuallyFinite geometricPiOneModel

/-- Conditional injectivity of the canonical map for the free-group model.  The
only missing ingredient is the residual finiteness of the free group, which is
not available as an instance in Mathlib 4.32.2; this is the exact API gap for
turning the free-group model into a faithful geometric Pi_v. -/
theorem eta_injective
    (h : Group.ResiduallyFinite (FreeGroup (Fin 2))) :
    Function.Injective (profiniteCompletionEta geometricPiOneModel) :=
  eta_injective_iff.mpr h

end FreeGroupModel


end LeanFormal.IUT.Foundations.Geometry
