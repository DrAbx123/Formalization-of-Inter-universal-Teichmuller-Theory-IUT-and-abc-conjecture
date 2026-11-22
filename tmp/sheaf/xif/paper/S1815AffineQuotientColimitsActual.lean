/-
# S1815: affine quotient colimits for the finite-etale slice

Target: `S1792AffineQuotientColimits` for the S1726 base `Spec R'`,
`R' = S1726CoordinateRing`, i.e. for every finite group `G` the affine
finite-etale slice `S1733Slice` has colimits of shape `SingleObj G`.

## Contents

1. For an arbitrary commutative ring `R` and a finite group `G` acting on a
   finite etale `R`-algebra, the invariant subalgebra `A^G` is finite etale
   over `R` (this is the kernel-checked general fixed-point theorem
   `FiniteEtaleFixedPointsGeneral.fixedPointSubalgebra_finiteEtale`), and the
   invariant cone is a limit cone in `CommAlgCat.FiniteEtale R`.  Hence
   `(CommAlgCat.FiniteEtale R)^op` has colimits of shape `SingleObj G`.
   This is the general-ring version of S1746/S1770 (which are stated over a
   field); no field hypothesis is used.

2. The affine finite-etale slice `S1733Slice = P.CostructuredArrow ⊤ Spec
   (Spec R')` is equivalent to `(CommAlgCat.FiniteEtale R')^op`.  The functor
   sends a finite etale `R'`-algebra `A` to `Spec A ⟶ Spec R'`; the inverse
   sends a slice object to the ring of global sections with the algebra
   structure induced by its structure morphism.  This is the affine-slice
   refinement of S1799's equivalence `(FiniteEtale R)^op ≌ FiniteEtaleCover
   (Spec R)`; S1799 is imported and checked below.

3. Transporting the algebra-side colimits across this equivalence gives
   `S1792AffineQuotientColimits` for all finite groups (the index group is
   shrunk to universe 0 when necessary).

## Honest boundary

No `sorry`, no axiom, no fabricated colimit.  The colimit is the actual
invariant subalgebra, and the equivalence is an actual `CategoryTheory.Equivalence`.
Only `propext`, `Classical.choice` and `Quot.sound` are used; see the audit at
the end.
-/

import tmp.sheaf.xif.paper.S1792QuotientCoverActual
import tmp.sheaf.xif.paper.S1799AffineFiniteEtaleEquivActual
import tmp.sheaf.xif.paper.S1733EssentiallySmallCoversActual
import LeanFormal.IUT.Foundations.AlgebraicGeometry.FiniteEtaleFixedPointsGeneral
import LeanFormal.IUT.Foundations.AlgebraicGeometry.InvariantsGeneralAssembly
import Mathlib.CategoryTheory.Limits.Opposites
import Mathlib.CategoryTheory.Limits.Shapes.SingleObj
import Mathlib.Algebra.Group.TransferInstance
import Mathlib.RingTheory.Etale.Finite
import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Mathlib.AlgebraicGeometry.Morphisms.Etale
import Mathlib.AlgebraicGeometry.GammaSpecAdjunction
import Mathlib.AlgebraicGeometry.AffineScheme

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency false

namespace LeanFormal.IUT.XiFPaper.S1815AffineQuotientColimitsActual
namespace General

open CategoryTheory
open CategoryTheory.Limits
open LeanFormal.IUT.Foundations.AlgebraicGeometry.FiniteEtaleGroupQuotient
open LeanFormal.IUT.Foundations.AlgebraicGeometry

universe u

variable {R : Type u} [CommRing R] {G : Type u} [Group G] [Fintype G] [DecidableEq G]
variable (F : (SingleObj G)ᵒᵖ ⥤ CommAlgCat.FiniteEtale.{u} R)

abbrev shapePoint (G : Type u) : (SingleObj G)ᵒᵖ := Opposite.op (SingleObj.star G)

abbrev actionAlgebra (F : (SingleObj G)ᵒᵖ ⥤ CommAlgCat.FiniteEtale.{u} R) : Type u :=
  (F.obj (shapePoint G)).obj

noncomputable def opHom (g : G) : shapePoint G ⟶ shapePoint G :=
  (SingleObj.toEnd G g).op

lemma opHom_mul_inv (g : G) : opHom (G := G) g ≫ opHom (G := G) (g⁻¹) = 𝟙 _ := by
  unfold opHom
  change (SingleObj.toEnd G g * SingleObj.toEnd G (g⁻¹)).op = 𝟙 _
  rw [← map_mul, mul_inv_cancel]
  rfl

lemma opHom_inv_mul (g : G) : opHom (G := G) (g⁻¹) ≫ opHom (G := G) g = 𝟙 _ := by
  unfold opHom
  change (SingleObj.toEnd G (g⁻¹) * SingleObj.toEnd G g).op = 𝟙 _
  rw [← map_mul, inv_mul_cancel]
  rfl

noncomputable def sigma (g : G) : actionAlgebra F ≃ₐ[R] actionAlgebra F where
  toFun := (F.map (opHom (G := G) g)).hom.hom
  invFun := (F.map (opHom (G := G) (g⁻¹))).hom.hom
  left_inv := by
    intro a
    change (F.map (opHom (G := G) (g⁻¹))).hom.hom ((F.map (opHom (G := G) g)).hom.hom a) = a
    have hcomp : F.map (opHom (G := G) g) ≫ F.map (opHom (G := G) (g⁻¹)) = 𝟙 (F.obj (shapePoint G)) := by
      rw [← F.map_comp, opHom_mul_inv]
      exact F.map_id _
    have h := congrArg (fun (m : F.obj (shapePoint G) ⟶ F.obj (shapePoint G)) => m.hom.hom a) hcomp
    simpa using h
  right_inv := by
    intro a
    change (F.map (opHom (G := G) g)).hom.hom ((F.map (opHom (G := G) (g⁻¹))).hom.hom a) = a
    have hcomp : F.map (opHom (G := G) (g⁻¹)) ≫ F.map (opHom (G := G) g) = 𝟙 (F.obj (shapePoint G)) := by
      rw [← F.map_comp, opHom_inv_mul]
      exact F.map_id _
    have h := congrArg (fun (m : F.obj (shapePoint G) ⟶ F.obj (shapePoint G)) => m.hom.hom a) hcomp
    simpa using h
  map_add' := by intro a b; exact map_add _ a b
  map_mul' := by intro a b; exact map_mul _ a b
  commutes' := by intro r; exact AlgHom.commutes _ r

lemma sigma_apply (g : G) (a : actionAlgebra F) :
    sigma (F := F) g a = (F.map (opHom (G := G) g)).hom.hom a := rfl


lemma opHom_mul (g h : G) : opHom (G := G) (g * h) = opHom (G := G) g ≫ opHom (G := G) h := by
  unfold opHom
  rw [map_mul]
  rfl

lemma sigma_one : sigma (F := F) 1 = 1 := by
  ext a
  rw [sigma_apply]
  have h1 : opHom (G := G) 1 = 𝟙 (shapePoint G) := by
    simp [opHom]
  rw [h1, F.map_id]
  rfl

lemma sigma_mul (g h : G) :
    sigma (F := F) (g * h) = sigma (F := F) h * sigma (F := F) g := by
  ext a
  simp only [sigma_apply, AlgEquiv.mul_apply]
  rw [opHom_mul, F.map_comp]
  rfl

/-- The left action homomorphism (using inverse to turn the anti-hom into a hom). -/
noncomputable def actionEquiv (g : G) : actionAlgebra F ≃+* actionAlgebra F :=
  (sigma (F := F) (g⁻¹)).toRingEquiv

lemma actionEquiv_one : actionEquiv (F := F) 1 = 1 := by
  ext a
  simp [actionEquiv, sigma_one]

lemma actionEquiv_mul (g h : G) :
    actionEquiv (F := F) (g * h) = actionEquiv (F := F) g * actionEquiv (F := F) h := by
  ext a
  change sigma (F := F) ((g * h)⁻¹) a =
    sigma (F := F) (g⁻¹) (sigma (F := F) (h⁻¹) a)
  rw [mul_inv_rev, sigma_mul]
  rfl

/-- The monoid homomorphism encoding the action. -/
noncomputable def actionHom : G →* (actionAlgebra F ≃+* actionAlgebra F) where
  toFun := actionEquiv (F := F)
  map_one' := actionEquiv_one (F := F)
  map_mul' := actionEquiv_mul (F := F)

/-- The induced multiplicative semiring action. -/
@[reducible] noncomputable def actionMulSemiringAction :
    MulSemiringAction G (actionAlgebra F) :=
  letI : MulSemiringAction (actionAlgebra F ≃+* actionAlgebra F) (actionAlgebra F) :=
    inferInstance
  MulSemiringAction.compHom (M := actionAlgebra F ≃+* actionAlgebra F)
    (R := actionAlgebra F) (actionHom (F := F))

/-- The action is R-linear. -/
theorem actionSMulCommClass :
    letI := actionMulSemiringAction (F := F)
    SMulCommClass G R (actionAlgebra F) := by
  letI := actionMulSemiringAction (F := F)
  exact
    { smul_comm := fun g r a => by
        change actionEquiv (F := F) g (r • a) = r • actionEquiv (F := F) g a
        rw [Algebra.smul_def, Algebra.smul_def, map_mul]
        congr 1
        exact (sigma (F := F) (g⁻¹)).commutes r }


lemma action_smul (g : G) (a : actionAlgebra F) :
    letI := actionMulSemiringAction (F := F)
    g • a = actionEquiv (F := F) g a := rfl

/-- The invariant subalgebra. -/
noncomputable def invariants : Subalgebra R (actionAlgebra F) :=
  letI := actionMulSemiringAction (F := F)
  letI := actionSMulCommClass (F := F)
  FixedPoints.subalgebra R (actionAlgebra F) G

/-- The fixed-point algebra is finite etale over any commutative base ring. -/
theorem invariants_finiteEtale :
    Algebra.Etale R ↥(invariants (F := F)) ∧ Module.Finite R ↥(invariants (F := F)) :=
  letI := actionMulSemiringAction (F := F)
  letI := actionSMulCommClass (F := F)
  FiniteEtaleFixedPointsGeneral.fixedPointSubalgebra_finiteEtale
    (R := R) (A := actionAlgebra F) (G := G)

/-- The invariant subalgebra as an object of the finite etale category. -/
noncomputable def invariantsObject : CommAlgCat.FiniteEtale.{u} R :=
  let h := invariants_finiteEtale (F := F)
  letI : Algebra.Etale R ↥(invariants (F := F)) := h.1
  letI : Module.Finite R ↥(invariants (F := F)) := h.2
  CommAlgCat.FiniteEtale.of R ↥(invariants (F := F))

/-- The structure map from the invariants to the acted algebra. -/
noncomputable def invariantsMap (j : (SingleObj G)ᵒᵖ) :
    invariantsObject (F := F) ⟶ F.obj j :=
  { hom := CommAlgCat.ofHom
      (Subalgebra.val (invariants (F := F)) :
        ↥(invariants (F := F)) →ₐ[R] (F.obj j).obj) }

/-- Naturality of the invariants cone. -/
theorem invariantsMap_naturality {j j' : (SingleObj G)ᵒᵖ} (f : j ⟶ j') :
    invariantsMap (F := F) j' = invariantsMap (F := F) j ≫ F.map f := by
  apply ObjectProperty.hom_ext
  apply CommAlgCat.hom_ext
  show (Subalgebra.val (invariants (F := F)) : ↥(invariants (F := F)) →ₐ[R] (F.obj j').obj) =
    ((F.map f).hom.hom).comp
      (Subalgebra.val (invariants (F := F)) : ↥(invariants (F := F)) →ₐ[R] (F.obj j).obj)
  apply AlgHom.ext
  intro x
  show (Subalgebra.val (invariants (F := F))) x =
    ((F.map f).hom.hom) ((Subalgebra.val (invariants (F := F))) x)
  have hf : f = opHom (G := G) (Opposite.unop f) := by
    change f = (SingleObj.toEnd G (Opposite.unop f)).op
    rw [SingleObj.toEnd_def]
    exact (Quiver.Hom.op_unop f).symm
  rw [hf]
  have hx : sigma (F := F) (Opposite.unop f)
      ((Subalgebra.val (invariants (F := F))) x) =
      (Subalgebra.val (invariants (F := F))) x := by
    have h := x.2 ((Opposite.unop f)⁻¹)
    simpa [action_smul, actionEquiv, inv_inv] using h
  exact hx.symm

/-- The invariants cone. -/
noncomputable def invariantsCone : Cone F where
  pt := invariantsObject (F := F)
  π :=
    { app := invariantsMap (F := F)
      naturality := by
        intro j j' f
        exact invariantsMap_naturality (F := F) f }

/-- The factorization of a cone through the invariants. -/
noncomputable def invariantsLift (c : Cone F) :
    c.pt ⟶ (invariantsCone (F := F)).pt :=
  { hom := CommAlgCat.ofHom
      (AlgHom.codRestrict ((c.π.app (shapePoint G)).hom.hom)
        (invariants (F := F)) (by
          intro x
          show ∀ g : G, actionEquiv (F := F) g
            ((c.π.app (shapePoint G)).hom.hom x) =
            (c.π.app (shapePoint G)).hom.hom x
          intro g
          change sigma (F := F) (g⁻¹) ((c.π.app (shapePoint G)).hom.hom x) =
            (c.π.app (shapePoint G)).hom.hom x
          exact congrArg
            (fun (m : c.pt ⟶ F.obj (shapePoint G)) => m.hom.hom x)
            (Cone.w (j := shapePoint G) (j' := shapePoint G) c (opHom (G := G) (g⁻¹))))) }

/-- The lift makes the triangles commute. -/
theorem invariantsLift_fac (c : Cone F) (j : (SingleObj G)ᵒᵖ) :
    invariantsLift (F := F) c ≫ (invariantsCone (F := F)).π.app j = c.π.app j := by
  apply ObjectProperty.hom_ext
  apply CommAlgCat.hom_ext
  apply AlgHom.ext
  intro x
  rfl

/-- The invariants cone is a limit cone. -/
noncomputable def invariantsIsLimit : IsLimit (invariantsCone (F := F)) where
  lift := invariantsLift (F := F)
  fac := invariantsLift_fac (F := F)
  uniq c m hm := by
    apply ObjectProperty.hom_ext
    apply CommAlgCat.hom_ext
    apply AlgHom.ext
    intro x
    have h3 : m ≫ (invariantsCone (F := F)).π.app (shapePoint G) =
        invariantsLift (F := F) c ≫ (invariantsCone (F := F)).π.app (shapePoint G) := by
      rw [hm (shapePoint G), invariantsLift_fac (F := F) c (shapePoint G)]
    have h4 := congrArg (fun (g : c.pt ⟶ F.obj (shapePoint G)) => g.hom.hom x) h3
    exact Subtype.ext h4

instance hasLimitInvariants : HasLimit F :=
  HasLimit.mk ⟨invariantsCone (F := F), invariantsIsLimit (F := F)⟩

instance hasLimitsOfShapeOpSingleObj :
    HasLimitsOfShape (SingleObj G)ᵒᵖ (CommAlgCat.FiniteEtale.{u} R) :=
  ⟨fun F => hasLimitInvariants (F := F)⟩

/-- The opposite finite etale algebra category has finite-group quotient colimits. -/
instance hasColimitsOfShape_finiteEtaleAlg :
    HasColimitsOfShape (SingleObj G) ((CommAlgCat.FiniteEtale.{u} R)ᵒᵖ) :=
  hasColimitsOfShape_op_of_hasLimitsOfShape (J := SingleObj G)
    (C := CommAlgCat.FiniteEtale.{u} R)

end General

namespace Slice

open CategoryTheory AlgebraicGeometry
open LeanFormal.IUT.XiFPaper.S1726OrbicurveFPrimeActual
open LeanFormal.IUT.XiFPaper.S1733EssentiallySmallCoversActual

abbrev R : Type := S1726CoordinateRing
abbrev Base : Scheme.{0} := S1733BaseScheme
abbrev Alg : Type 1 := CommAlgCat.FiniteEtale.{0} R

noncomputable def structMap (A : Alg) : Spec (CommRingCat.of (↥A)) ⟶ Base :=
  Spec.map (CommRingCat.ofHom (algebraMap R (↥A)))

lemma structMap_isFinite (A : Alg) : IsFinite (structMap A) := by
  rw [structMap, IsFinite.SpecMap_iff, CommRingCat.hom_ofHom]
  exact RingHom.finite_algebraMap.mpr inferInstance

lemma structMap_etale (A : Alg) : Etale (structMap A) := by
  rw [structMap, HasRingHomProperty.Spec_iff (P := @Etale) (Q := @RingHom.Etale),
    CommRingCat.hom_ofHom]
  exact RingHom.etale_algebraMap.mpr inferInstance

noncomputable def obj (A : Algᵒᵖ) : S1733Slice :=
  MorphismProperty.CostructuredArrow.mk (Q := ⊤) (P := S1733FiniteEtale)
    (F := Scheme.Spec) (X := Base) (structMap A.unop)
    ⟨structMap_isFinite A.unop, structMap_etale A.unop⟩

@[simp] lemma obj_left (A : Algᵒᵖ) :
    (obj A).left = Opposite.op (CommRingCat.of (↥A.unop)) := rfl
@[simp] lemma obj_hom (A : Algᵒᵖ) : (obj A).hom = structMap A.unop := rfl

lemma structMap_comp {A B : Algᵒᵖ} (g : A ⟶ B) :
    CommRingCat.ofHom (algebraMap R (↥B.unop)) ≫
        CommRingCat.ofHom g.unop.hom.hom.toRingHom =
      CommRingCat.ofHom (algebraMap R (↥A.unop)) := by
  rw [← CommRingCat.ofHom_comp]
  apply congrArg CommRingCat.ofHom
  apply RingHom.ext
  intro x
  exact g.unop.hom.hom.commutes x

lemma sliceFunctor_map_triangle {A B : Algᵒᵖ} (g : A ⟶ B) :
    Scheme.Spec.map
        (Opposite.op (CommRingCat.ofHom g.unop.hom.hom.toRingHom)) ≫ structMap B.unop =
      structMap A.unop := by
  show Spec.map (CommRingCat.ofHom g.unop.hom.hom.toRingHom) ≫ structMap B.unop = structMap A.unop
  rw [structMap, structMap, ← Spec.map_comp]
  exact congrArg Spec.map (structMap_comp g)

noncomputable def sliceFunctor : Algᵒᵖ ⥤ S1733Slice where
  obj := obj
  map {A B} g :=
    MorphismProperty.CostructuredArrow.homMk (Q := ⊤) (P := S1733FiniteEtale)
      (F := Scheme.Spec) (X := Base)
      (Opposite.op (CommRingCat.ofHom g.unop.hom.hom.toRingHom)) (by trivial)
      (sliceFunctor_map_triangle g)
  map_id A := by
    apply MorphismProperty.CostructuredArrow.Hom.ext
    show (Opposite.op (CommRingCat.ofHom (𝟙 A).unop.hom.hom.toRingHom) : _) =
      𝟙 (Opposite.op (CommRingCat.of (↥A.unop)))
    rw [show (𝟙 A).unop.hom.hom.toRingHom = RingHom.id (↥A.unop) from rfl, CommRingCat.ofHom_id]
    exact CategoryTheory.op_id
  map_comp {A B C} g h := by
    apply MorphismProperty.CostructuredArrow.Hom.ext
    rfl


lemma sliceHom_algMap_comp {A B : Algᵒᵖ} (φ : obj A ⟶ obj B) :
    CommRingCat.ofHom (algebraMap R (↥B.unop)) ≫ φ.left.unop =
      CommRingCat.ofHom (algebraMap R (↥A.unop)) := by
  have htri : Scheme.Spec.map φ.left ≫ (obj B).hom = (obj A).hom := φ.w
  have hgoal : Spec.map (CommRingCat.ofHom (algebraMap R (↥B.unop)) ≫ φ.left.unop) =
      Spec.map (CommRingCat.ofHom (algebraMap R (↥A.unop))) := by
    rw [Spec.map_comp]
    exact htri
  exact Spec.map_injective hgoal

instance sliceFunctor_faithful : sliceFunctor.Faithful where
  map_injective {A B} f g h := by
    have hleft : (sliceFunctor.map f).left = (sliceFunctor.map g).left :=
      congrArg (fun φ => φ.left) h
    have h1 : (CommRingCat.ofHom f.unop.hom.hom.toRingHom) =
        (CommRingCat.ofHom g.unop.hom.hom.toRingHom) := Quiver.Hom.op_inj hleft
    have h2 : f.unop.hom.hom.toRingHom = g.unop.hom.hom.toRingHom :=
      congrArg CommRingCat.Hom.hom h1
    have h3 : f.unop.hom.hom = g.unop.hom.hom :=
      AlgHom.ext (fun x => congrArg (fun φ => φ x) h2)
    have h4 : f.unop.hom = g.unop.hom := CommAlgCat.hom_ext h3
    have h5 : f.unop = g.unop := InducedCategory.hom_ext h4
    exact Opposite.unop_injective h5

instance sliceFunctor_full : sliceFunctor.Full where
  map_surjective {A B} φ := by
    have hcomm : CommRingCat.ofHom (algebraMap R (↥B.unop)) ≫ φ.left.unop =
        CommRingCat.ofHom (algebraMap R (↥A.unop)) := sliceHom_algMap_comp φ
    let ψ : ↥(B.unop) →ₐ[R] ↥(A.unop) :=
      { toRingHom := CommRingCat.Hom.hom φ.left.unop
        commutes' := fun x => by
          have h := congrArg (fun (f : CommRingCat.of R ⟶ CommRingCat.of (↥A.unop)) =>
            (CommRingCat.Hom.hom f) x) hcomm
          change (CommRingCat.Hom.hom φ.left.unop) (algebraMap R (↥B.unop) x) =
            algebraMap R (↥A.unop) x at h
          exact h }
    let ghom : B.unop ⟶ A.unop := InducedCategory.homMk (CommAlgCat.ofHom ψ)
    refine ⟨ghom.op, ?_⟩
    apply MorphismProperty.CostructuredArrow.Hom.ext
    show (Opposite.op (CommRingCat.ofHom (CommRingCat.Hom.hom φ.left.unop)) : _) = φ.left
    rw [CommRingCat.ofHom_hom]
    exact Quiver.Hom.op_unop φ.left


/-- The R'-algebra structure on the coordinate ring of a slice object:
the unique ring map whose Spec is the structure morphism. -/
noncomputable def algMap (X : S1733Slice) : CommRingCat.of R ⟶ X.left.unop :=
  Spec.preimage X.hom

lemma Spec_map_algMap (X : S1733Slice) :
    Spec.map (algMap X) = X.hom :=
  Spec.map_preimage X.hom

lemma algMap_finite (X : S1733Slice) : RingHom.Finite (algMap X).hom := by
  have h : IsFinite (Spec.map (algMap X)) := by
    rw [Spec_map_algMap]
    exact X.prop.1
  exact (IsFinite.SpecMap_iff (f := algMap X)).mp h

lemma algMap_etale (X : S1733Slice) : RingHom.Etale (algMap X).hom := by
  have h : Etale (Spec.map (algMap X)) := by
    rw [Spec_map_algMap]
    exact X.prop.2
  exact (HasRingHomProperty.Spec_iff (P := @Etale) (Q := @RingHom.Etale)
    (φ := algMap X)).mp h

/-- The finite etale R'-algebra attached to a slice object. -/
noncomputable def sliceAlg (X : S1733Slice) : Alg :=
  letI : Algebra R (↥X.left.unop) := (algMap X).hom.toAlgebra
  letI : Module.Finite R (↥X.left.unop) :=
    RingHom.finite_algebraMap.mpr (algMap_finite X)
  letI : Algebra.Etale R (↥X.left.unop) :=
    RingHom.etale_algebraMap.mp (algMap_etale X)
  CommAlgCat.FiniteEtale.of R (↥X.left.unop)

/-- The slice object is isomorphic to the algebra object. -/
noncomputable def sliceIso (X : S1733Slice) : obj (Opposite.op (sliceAlg X)) ≅ X := by
  classical
  letI : Algebra R (↥X.left.unop) := (algMap X).hom.toAlgebra
  letI : Module.Finite R (↥X.left.unop) :=
    RingHom.finite_algebraMap.mpr (algMap_finite X)
  letI : Algebra.Etale R (↥X.left.unop) :=
    RingHom.etale_algebraMap.mp (algMap_etale X)
  refine MorphismProperty.CostructuredArrow.isoMk (Q := ⊤) (P := S1733FiniteEtale)
    (F := Scheme.Spec) (X := Base) (Iso.refl X.left) (by trivial) (by trivial) ?_
  change Scheme.Spec.map (Iso.refl X.left).hom ≫ X.hom = (obj (Opposite.op (sliceAlg X))).hom
  rw [Iso.refl_hom, Scheme.Spec.map_id, Category.id_comp]
  exact (Spec_map_algMap X).symm

theorem sliceFunctor_essSurj : sliceFunctor.EssSurj :=
  ⟨fun X => ⟨Opposite.op (sliceAlg X), ⟨sliceIso X⟩⟩⟩

instance sliceFunctor_isEquivalence : sliceFunctor.IsEquivalence where
  faithful := sliceFunctor_faithful
  full := sliceFunctor_full
  essSurj := sliceFunctor_essSurj

/-- The affine finite-etale slice is equivalent to the opposite finite etale
algebra category. -/
noncomputable def sliceEquivalence : Algᵒᵖ ≌ S1733Slice :=
  sliceFunctor.asEquivalence

end Slice

/-! ## 4. The affine quotient colimits target -/

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open LeanFormal.IUT.XiFPaper.S1792QuotientCoverActual
open LeanFormal.IUT.XiFPaper.S1733EssentiallySmallCoversActual
open LeanFormal.IUT.IUTII.Frobenioid.Example36.EtaleCoverFoundations

/-- **S1792AffineQuotientColimits**, proved for the actual S1726 base.

The proof shrinks the finite group to universe 0 (so that the general
fixed-point theorem applies), uses the algebra-side colimits of Section 1,
transports them across the slice equivalence of Section 2, and finally
transports along the equivalence of single-object categories induced by the
group equivalence. -/
theorem S1815AffineQuotientColimits : S1792AffineQuotientColimits := by
  intro G _ _
  obtain ⟨G', instGroup, instFintype, ⟨eMul⟩⟩ :=
    Finite.exists_type_univ_nonempty_mulEquiv.{1, 0} G
  letI : Group G' := instGroup
  letI : Fintype G' := instFintype
  letI : DecidableEq G' := Classical.decEq G'
  haveI hAlg : HasColimitsOfShape (SingleObj G') (Slice.Algᵒᵖ) :=
    General.hasColimitsOfShape_finiteEtaleAlg (R := Slice.R) (G := G')
  haveI hSlice : HasColimitsOfShape (SingleObj G') S1733Slice :=
    Adjunction.hasColimitsOfShape_of_equivalence (J := SingleObj G')
      Slice.sliceEquivalence.inverse
  haveI hIndex : HasColimitsOfShape (SingleObj G) S1733Slice :=
    CategoryTheory.Limits.hasColimitsOfShape_of_equivalence
      (J := SingleObj G') (J' := SingleObj G)
      (MulEquiv.toSingleObjEquiv eMul.symm)
  exact hIndex

/-! ## 5. Consistency with S1799 -/

/- S1799's affine finite-etale equivalence, imported for the same base ring.
The equivalence proved above is the affine-slice refinement of this cover
equivalence: it identifies the slice `S1733Slice` directly with the opposite
finite etale algebra category, without passing through `FiniteEtaleCover`. -/
#check @S1799AffineFiniteEtaleEquivActual.affineFiniteEtaleEquivalence

/-- The S1799 cover equivalence composed with the affine-slice equivalence.
This is the literal composition `S1733Slice ≌ (FiniteEtale R')^op ≌
FiniteEtaleCover (Spec R')`; it is recorded for consistency with S1799. -/
noncomputable def sliceCoverEquivalence :
    S1733Slice ≌ FiniteEtaleCover Slice.Base :=
  Slice.sliceEquivalence.symm.trans
    (S1799AffineFiniteEtaleEquivActual.affineFiniteEtaleEquivalence Slice.R)

/-! ## 6. Axiom audit -/

#check S1815AffineQuotientColimits
#check General.hasColimitsOfShape_finiteEtaleAlg
#check Slice.sliceEquivalence
#check Slice.sliceFunctor_isEquivalence
#check Slice.sliceFunctor_essSurj
#check Slice.sliceFunctor_full
#check Slice.sliceFunctor_faithful

#print axioms S1815AffineQuotientColimits
#print axioms General.hasColimitsOfShape_finiteEtaleAlg
#print axioms General.invariantsIsLimit
#print axioms Slice.sliceEquivalence
#print axioms Slice.sliceFunctor_isEquivalence
#print axioms Slice.sliceIso
#print axioms Slice.algMap_finite
#print axioms Slice.algMap_etale

end LeanFormal.IUT.XiFPaper.S1815AffineQuotientColimitsActual