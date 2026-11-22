/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# S1822 -- base change preserves pullbacks: BCPreservesPullbacks proved

## Target

S1769/S1794 reduced the field preservesPullbacks of
PreGaloisCategory.FiberFunctor (CommAlgCat.FiniteEtale.fiber K Kbar) to the single
statement

  BCPreservesPullbacks K : PreservesLimitsOfShape WalkingCospan
      (CommAlgCat.FiniteEtale.baseChange K (AlgebraicClosure K)).op

which is equivalent to: base change S (x)_K - on finite etale K-algebras preserves
pushouts (colimits of shape WalkingSpan).  This file proves that statement,
unconditionally, for every field K.

## Strategy (as prescribed by the task)

1. Ambient base change.  On CommAlgCat K we define bcAmb K S : CommAlgCat K --> CommAlgCat S
   by A |-> S (x)_K A (the same formula as Mathlib's
   CommAlgCat.FiniteEtale.baseChange).  The restriction of bcAmb K S to the full
   subcategory of finite etale algebras *is* FiniteEtale.baseChange K S -- this is
   definitional, see baseChange_eq_inclusion.
2. Base change is a left adjoint.  The right adjoint is restriction of scalars
   resScalars : CommAlgCat S --> CommAlgCat K (an S-algebra is a K-algebra along
   K --> S).  The hom-set equivalence is the universal property of the tensor product of
   algebras, Algebra.TensorProduct.liftEquivRight; the naturality conditions are
   tensor-product computations (TensorProduct.induction_on).  This is the
   CommAlgCat-level counterpart of Mathlib's
   Mathlib/Algebra/Category/Ring/Under/Limits.lean, where CommRingCat.Under.tensorProd
   is CommRingCat.Under.pushout up to natural isomorphism and Under.pushout is a left
   adjoint (Under.mapPushoutAdj) hence preserves all colimits; flatness is *not* needed
   for this direction (it is needed only for left exactness of tensorProd).
3. Colimits in CommAlgCat K.  A left adjoint preserves colimits
   (Adjunction.leftAdjoint_preservesColimits), so bcAmb K S preserves colimits of
   shape WalkingSpan, i.e. pushouts of algebras.
4. Pushing through the full subcategories.  S1745 proves that
   CommAlgCat.finiteEtale K is closed under colimits of shape WalkingSpan (the
   pushout of B <-- A --> C is the tensor product B (x)_A C), so the inclusion
   (CommAlgCat.finiteEtale K).iota creates, hence preserves and reflects,
   WalkingSpan-colimits.  Combined with baseChange_eq_inclusion this transfers the
   ambient preservation statement to FiniteEtale.baseChange K S.
5. WalkingSpan-colimits are WalkingCospan-limits in the opposite category
   (walkingCospanOpEquiv), which yields BCPreservesPullbacks.

## Status

BCPreservesPullbacks is proved unconditionally (BCPreservesPullbacks_holds), with no
sorry, no new axiom, and no weakened statement.  Axioms: see the audit at the end.
-/
import Mathlib.RingTheory.Etale.Finite
import Mathlib.Algebra.Category.Ring.Under.Limits
import Mathlib.CategoryTheory.Limits.Preserves.Opposites
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Pullbacks
import Mathlib.CategoryTheory.Limits.FullSubcategory
import Mathlib.CategoryTheory.Adjunction.Limits
import Mathlib.FieldTheory.AbsoluteGaloisGroup
import tmp.sheaf.xif.paper.S1745FiniteEtaleLimitsActual
import tmp.sheaf.xif.paper.S1769FiberFunctorFieldsActual

noncomputable section
open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct

namespace S1822

/-! ### 1. Ambient base change on commutative algebras -/

/-- The object S (x)_K A of CommAlgCat S, made reducible so that the coercion to Type and
the algebra structures are visible to elaboration and to instance search. -/
@[reducible] def bcObj (K S : Type) [Field K] [Field S] [Algebra K S]
    (A : CommAlgCat.{0} K) : CommAlgCat.{0} S :=
  CommAlgCat.of S (S ⊗[K] A)

/-- Base change A |-> S (x)_K A as a functor CommAlgCat K --> CommAlgCat S. -/
def bcAmb (K S : Type) [Field K] [Field S] [Algebra K S] :
    CommAlgCat.{0} K ⥤ CommAlgCat.{0} S where
  obj := bcObj K S
  map {A B} f := CommAlgCat.ofHom (Algebra.TensorProduct.map (AlgHom.id S S) f.hom)
  map_id A := by ext x; simp
  map_comp {A B C} f g := by ext x; simp

/-- The K-algebra structure on an S-algebra, along K --> S. -/
@[reducible] def towerAlg (K S : Type) [Field K] [Field S] [Algebra K S]
    (B : CommAlgCat.{0} S) : Algebra K (B : Type) :=
  RingHom.toAlgebra ((algebraMap S (B : Type)).comp (algebraMap K S))

/-- That K-algebra structure is compatible with the S-algebra structure. -/
lemma towerST (K S : Type) [Field K] [Field S] [Algebra K S] (B : CommAlgCat.{0} S) :
    letI := towerAlg K S B
    IsScalarTower K S (B : Type) := by
  letI := towerAlg K S B
  exact IsScalarTower.of_algebraMap_eq' rfl

/-- An S-algebra, regarded as a K-algebra. -/
@[reducible] def resObj (K S : Type) [Field K] [Field S] [Algebra K S]
    (B : CommAlgCat.{0} S) : CommAlgCat.{0} K :=
  letI := towerAlg K S B
  CommAlgCat.of K (B : Type)

/-- Restriction of scalars along K --> S, as a functor CommAlgCat S --> CommAlgCat K. -/
def resScalars (K S : Type) [Field K] [Field S] [Algebra K S] :
    CommAlgCat.{0} S ⥤ CommAlgCat.{0} K where
  obj := resObj K S
  map {A B} f := by
    letI := towerAlg K S A
    letI := towerAlg K S B
    refine CommAlgCat.ofHom ⟨f.hom.toRingHom, fun k => ?_⟩
    show f.hom (algebraMap K (A : Type) k) = algebraMap K (B : Type) k
    rw [show algebraMap K (A : Type) k = algebraMap S (A : Type) (algebraMap K S k) from rfl,
      show algebraMap K (B : Type) k = algebraMap S (B : Type) (algebraMap K S k) from rfl,
      f.hom.commutes]
  map_id A := by
    letI := towerAlg K S A
    apply CommAlgCat.hom_ext
    ext x
    rfl
  map_comp {A B C} f g := by
    letI := towerAlg K S A
    letI := towerAlg K S B
    letI := towerAlg K S C
    apply CommAlgCat.hom_ext
    ext x
    rfl

/-- The hom-set equivalence of the adjunction bcAmb K S -| resScalars K S, given by the
universal property of the tensor product of algebras (Algebra.TensorProduct.liftEquivRight):
an S-algebra map S (x)_K A --> B is the same thing as a K-algebra map A --> B. -/
def homEquiv (K S : Type) [Field K] [Field S] [Algebra K S]
    (A : CommAlgCat K) (B : CommAlgCat S) :
    (bcObj K S A ⟶ B) ≃ (A ⟶ resObj K S B) :=
  letI := towerAlg K S B
  letI : IsScalarTower K S ((resObj K S B) : Type) := towerST K S B
  let e := Algebra.TensorProduct.liftEquivRight (R := K) (S := S) (B := (A : Type))
    (C := ((resObj K S B) : Type))
  { toFun := fun f => CommAlgCat.ofHom (e.symm f.hom)
    invFun := fun g => CommAlgCat.ofHom (e g.hom)
    left_inv := fun f => by
      show CommAlgCat.ofHom (e (e.symm f.hom)) = f
      rw [Equiv.apply_symm_apply]
      rfl
    right_inv := fun g => by
      show CommAlgCat.ofHom (e.symm (e g.hom)) = g
      rw [Equiv.symm_apply_apply]
      rfl }

set_option backward.isDefEq.respectTransparency false in
/-- Naturality of the hom-equivalence in its first (contravariant) variable. -/
lemma homEquiv_naturality_left_symm (K S : Type) [Field K] [Field S] [Algebra K S]
    {X' X : CommAlgCat K} {Y : CommAlgCat S}
    (f : X' ⟶ X) (g : X ⟶ resObj K S Y) :
    (homEquiv K S X' Y).symm (f ≫ g)
      = CommAlgCat.ofHom (Algebra.TensorProduct.map (AlgHom.id S S) f.hom) ≫
        (homEquiv K S X Y).symm g := by
  simp only [homEquiv, Equiv.symm_mk, Equiv.coe_fn_mk]
  apply CommAlgCat.hom_ext
  apply AlgHom.ext
  intro x
  simp only [CommAlgCat.hom_comp, CommAlgCat.hom_ofHom, AlgHom.comp_apply]
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul s a => simp [Algebra.TensorProduct.lift_tmul, Algebra.TensorProduct.map_tmul]
  | add x y hx hy => simp only [map_add]; rw [hx, hy]

set_option backward.isDefEq.respectTransparency false in
/-- Naturality of the hom-equivalence in its second variable. -/
lemma homEquiv_naturality_right (K S : Type) [Field K] [Field S] [Algebra K S]
    {X : CommAlgCat K} {Y Y' : CommAlgCat S}
    (f : bcObj K S X ⟶ Y) (g : Y ⟶ Y') :
    (homEquiv K S X Y') (f ≫ g) =
      (homEquiv K S X Y) f ≫ (resScalars K S).map g := by
  simp only [homEquiv, Equiv.coe_fn_mk, resScalars]
  apply CommAlgCat.hom_ext
  apply AlgHom.ext
  intro x
  simp only [CommAlgCat.hom_comp, CommAlgCat.hom_ofHom, AlgHom.comp_apply]
  rfl

/-- **Base change on commutative algebras is left adjoint to restriction of scalars.** -/
def bcAdj (K S : Type) [Field K] [Field S] [Algebra K S] :
    bcAmb K S ⊣ resScalars K S :=
  Adjunction.mkOfHomEquiv
    { homEquiv := homEquiv K S
      homEquiv_naturality_left_symm := fun f g => homEquiv_naturality_left_symm K S f g
      homEquiv_naturality_right := fun f g => homEquiv_naturality_right K S f g }

instance bcAmb_isLeftAdjoint (K S : Type) [Field K] [Field S] [Algebra K S] :
    Functor.IsLeftAdjoint (bcAmb K S) :=
  (bcAdj K S).isLeftAdjoint

/-- **Base change preserves pushouts of commutative algebras.** -/
instance bcAmb_preservesColimits (K S : Type) [Field K] [Field S] [Algebra K S] :
    PreservesColimitsOfShape WalkingSpan (bcAmb K S) :=
  inferInstance

/-! ### 2. Transport to finite etale algebras -/

section FiniteEtale

variable (K S : Type) [Field K] [Field S] [Algebra K S]

/-- Ambient base change, restricted to finite etale algebras, is Mathlib's
CommAlgCat.FiniteEtale.baseChange.  This is a definitional equality. -/
theorem baseChange_eq_inclusion :
    (CommAlgCat.FiniteEtale.baseChange K S) ⋙ (CommAlgCat.finiteEtale S).ι
      = (CommAlgCat.finiteEtale K).ι ⋙ bcAmb K S := rfl

/-- The inclusion of finite etale K-algebras into all K-algebras preserves
WalkingSpan-colimits (pushouts): finite etale algebras are closed under them (S1745), so the
inclusion creates them. -/
instance finiteEtale_iota_preservesColimits (K : Type) [Field K] :
    PreservesColimitsOfShape WalkingSpan
      (CommAlgCat.finiteEtale K : ObjectProperty (CommAlgCat.{0} K)).ι := by
  haveI : (CommAlgCat.finiteEtale K : ObjectProperty (CommAlgCat.{0} K)).IsClosedUnderColimitsOfShape
      WalkingSpan := inferInstance
  exact preservesColimitOfShape_of_createsColimitsOfShape_and_hasColimitsOfShape _

/-- ... and reflects them. -/
instance finiteEtale_iota_reflectsColimits (K : Type) [Field K] :
    ReflectsColimitsOfShape WalkingSpan
      (CommAlgCat.finiteEtale K : ObjectProperty (CommAlgCat.{0} K)).ι := by
  haveI : (CommAlgCat.finiteEtale K : ObjectProperty (CommAlgCat.{0} K)).IsClosedUnderColimitsOfShape
      WalkingSpan := inferInstance
  haveI : CreatesColimitsOfShape WalkingSpan
      (CommAlgCat.finiteEtale K : ObjectProperty (CommAlgCat.{0} K)).ι := inferInstance
  exact reflectsColimitsOfShapeOfCreatesColimitsOfShape _

/-- **Base change on finite etale algebras preserves pushouts.**

The pushout of a span of finite etale K-algebras is their tensor product (S1745), so it
suffices to know that base change preserves pushouts in the ambient category of all
K-algebras -- the left-adjointness of bcAmb (Section 1) -- and that the inclusion of
finite etale algebras creates these colimits (S1745). -/
instance finiteEtale_baseChange_preservesColimits (K S : Type) [Field K] [Field S]
    [Algebra K S] :
    PreservesColimitsOfShape WalkingSpan
      (CommAlgCat.FiniteEtale.baseChange K S :
        CommAlgCat.FiniteEtale.{0} K ⥤ CommAlgCat.FiniteEtale.{0} S) := by
  haveI hιK : PreservesColimitsOfShape WalkingSpan
      (CommAlgCat.finiteEtale K : ObjectProperty (CommAlgCat.{0} K)).ι :=
    finiteEtale_iota_preservesColimits K
  haveI hbc : PreservesColimitsOfShape WalkingSpan (bcAmb K S) := bcAmb_preservesColimits K S
  haveI hιS : ReflectsColimitsOfShape WalkingSpan
      (CommAlgCat.finiteEtale S : ObjectProperty (CommAlgCat.{0} S)).ι :=
    finiteEtale_iota_reflectsColimits S
  refine ⟨fun {D} => ⟨fun {c} hc => ⟨?_⟩⟩⟩
  have h1 : IsColimit ((bcAmb K S).mapCocone
      ((CommAlgCat.finiteEtale K : ObjectProperty (CommAlgCat.{0} K)).ι.mapCocone c)) :=
    isColimitOfPreserves (bcAmb K S)
      (isColimitOfPreserves
        (CommAlgCat.finiteEtale K : ObjectProperty (CommAlgCat.{0} K)).ι hc)
  apply isColimitOfReflects
    (F := (CommAlgCat.finiteEtale S : ObjectProperty (CommAlgCat.{0} S)).ι)
  exact h1

end FiniteEtale

/-! ### 3. Opposite category: preservation of pullbacks -/

section Pullbacks

variable (K S : Type) [Field K] [Field S] [Algebra K S]

/-- **Base change preserves pullbacks.**  Colimits of shape WalkingSpan in FiniteEtale K are
limits of shape WalkingCospan in (FiniteEtale K)^op, and WalkingSpan is equivalent to
WalkingCospan^op, so preservation of pushouts becomes preservation of pullbacks for the
opposite functor. -/
theorem baseChange_op_preservesPullbacks :
    PreservesLimitsOfShape WalkingCospan
      (CommAlgCat.FiniteEtale.baseChange K S :
        CommAlgCat.FiniteEtale.{0} K ⥤ CommAlgCat.FiniteEtale.{0} S).op := by
  haveI h1 : PreservesColimitsOfShape WalkingSpan
      (CommAlgCat.FiniteEtale.baseChange K S :
        CommAlgCat.FiniteEtale.{0} K ⥤ CommAlgCat.FiniteEtale.{0} S) := inferInstance
  haveI h2 : PreservesColimitsOfShape (WalkingCospanᵒᵖ)
      (CommAlgCat.FiniteEtale.baseChange K S :
        CommAlgCat.FiniteEtale.{0} K ⥤ CommAlgCat.FiniteEtale.{0} S) :=
    preservesColimitsOfShape_of_equiv (F := (CommAlgCat.FiniteEtale.baseChange K S :
      CommAlgCat.FiniteEtale.{0} K ⥤ CommAlgCat.FiniteEtale.{0} S))
      walkingCospanOpEquiv.symm
  exact CategoryTheory.Limits.preservesLimitsOfShape_op WalkingCospan
    (CommAlgCat.FiniteEtale.baseChange K S :
      CommAlgCat.FiniteEtale.{0} K ⥤ CommAlgCat.FiniteEtale.{0} S)

end Pullbacks

/-! ### 4. The statement of S1769/S1794 -/

/-- Mathlib's base change functor on finite etale K-algebras, exactly as in S1769. -/
abbrev bc (K : Type) [Field K] :
    CommAlgCat.FiniteEtale.{0} K ⥤ CommAlgCat.FiniteEtale.{0} (AlgebraicClosure K) :=
  CommAlgCat.FiniteEtale.baseChange K (AlgebraicClosure K)

/-- **The first missing piece of S1769/S1794, verbatim.**  Base change along
K --> AlgebraicClosure K preserves pullbacks, equivalently preserves pushouts of finite
etale K-algebras. -/
def BCPreservesPullbacks (K : Type) [Field K] : Prop :=
  PreservesLimitsOfShape WalkingCospan (bc K).op

/-- **BCPreservesPullbacks holds**, unconditionally, for every field K. -/
theorem BCPreservesPullbacks_holds (K : Type) [Field K] : BCPreservesPullbacks K :=
  baseChange_op_preservesPullbacks K (AlgebraicClosure K)

/-! ### 5. Integration with S1769 -/

/-- S1769's first missing condition, proved outright.  This is the exact statement recorded as
`S1769.FirstMissing` / the hypothesis `hPull` of `S1769.fiberFunctorOf`. -/
theorem S1769_BCPreservesPullbacks (K : Type) [Field K] : S1769.BCPreservesPullbacks K :=
  BCPreservesPullbacks_holds K

/-! ### 6. Axiom audit -/

#print axioms S1822.bcAdj
#print axioms S1822.bcAmb_isLeftAdjoint
#print axioms S1822.bcAmb_preservesColimits
#print axioms S1822.baseChange_eq_inclusion
#print axioms S1822.finiteEtale_iota_preservesColimits
#print axioms S1822.finiteEtale_iota_reflectsColimits
#print axioms S1822.finiteEtale_baseChange_preservesColimits
#print axioms S1822.baseChange_op_preservesPullbacks
#print axioms S1822.BCPreservesPullbacks_holds
#print axioms S1822.S1769_BCPreservesPullbacks

end S1822
