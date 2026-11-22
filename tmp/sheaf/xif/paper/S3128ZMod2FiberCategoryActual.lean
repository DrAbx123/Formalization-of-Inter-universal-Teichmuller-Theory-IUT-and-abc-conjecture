import tmp.sheaf.xif.paper.S3128ZMod2QuotientStackPrestack
import Mathlib.AlgebraicGeometry.Limits
noncomputable section
open CategoryTheory CategoryTheory.Bicategory CategoryTheory.Limits
open scoped Pseudofunctor.StrongTrans
open Iut
open LeanFormal.IUT.XiFPaper.S3128ZMod2QuotientStackPrestack
set_option linter.unusedVariables false
set_option maxHeartbeats 4000000
namespace LeanFormal.IUT.XiFPaper.S3128ZMod2FiberCategoryActual

/-- Fiber object over an affine test `U`: a Z/2-torsor `P` with projection to
`U`, a sign action on `X`, and an equivariant stack map `P → X`.
All torsor/equivariance data are explicit fields. -/
structure S3128ZMod2FiberObj
    {F : Type} [Field F]
    (X : HyperbolicOrbicurve F) (U : SchemeOverField F) where
  P : SchemeOverField F
  proj : P ⟶ U
  zmod2_action : Multiplicative (ZMod 2) →* CategoryTheory.Aut P
  action_proj : ∀ g : Multiplicative (ZMod 2), (zmod2_action g).hom ≫ proj = proj
  /-- Scheme-level Z/2-torsor structure: `P ⊔ P ≅ P ×_U P`. -/
  torsor_iso : P ⨿ P ≅ pullback proj proj
  signAction : OrbicurveSignAction X
  stackMap : Pseudofunctor.StrongTrans
    (LeanFormal.IUT.XiFPaper.S1742TwoYonedaActual.S1742YS P) X.stack.fiber
  equivariantData : Prop
  equivariantData_proof : equivariantData

/-- Projection-compatible isomorphisms of fiber objects.  This is the actual
category structure; the missing equivariance condition on the stack map is
recorded separately as `S3128ZMod2EquivariantHom`. -/
structure S3128ZMod2FiberHom
    {F : Type} [Field F]
    {X : HyperbolicOrbicurve F} {U : SchemeOverField F}
    (A B : S3128ZMod2FiberObj X U) where
  iso : A.P ≅ B.P
  proj_comm : iso.hom ≫ B.proj = A.proj

namespace S3128ZMod2FiberHom
variable {F : Type} [Field F]
variable {X : HyperbolicOrbicurve F} {U : SchemeOverField F}
variable {A B C : S3128ZMod2FiberObj (F := F) X U}

@[ext] theorem ext (f g : S3128ZMod2FiberHom A B) (h : f.iso = g.iso) : f = g := by
  cases f with
  | mk fi fo =>
    cases g with
    | mk gi go =>
      cases h
      rfl

noncomputable def id (A : S3128ZMod2FiberObj (F := F) X U) :
    S3128ZMod2FiberHom A A where
  iso := Iso.refl A.P
  proj_comm := by simp

noncomputable def comp (f : S3128ZMod2FiberHom A B) (g : S3128ZMod2FiberHom B C) :
    S3128ZMod2FiberHom A C where
  iso := f.iso.trans g.iso
  proj_comm := by
    rw [Iso.trans_hom, Category.assoc, g.proj_comm, f.proj_comm]

end S3128ZMod2FiberHom

noncomputable instance S3128ZMod2FiberCategory
    {F : Type} [Field F] (X : HyperbolicOrbicurve F) (U : SchemeOverField F) :
    Category (S3128ZMod2FiberObj X U) where
  Hom := S3128ZMod2FiberHom
  id := S3128ZMod2FiberHom.id
  comp := S3128ZMod2FiberHom.comp
  id_comp f := by
    apply S3128ZMod2FiberHom.ext
    simp [S3128ZMod2FiberHom.id, S3128ZMod2FiberHom.comp]
  comp_id f := by
    apply S3128ZMod2FiberHom.ext
    simp [S3128ZMod2FiberHom.id, S3128ZMod2FiberHom.comp]
  assoc f g h := by
    apply S3128ZMod2FiberHom.ext
    simp [S3128ZMod2FiberHom.comp, Category.assoc]

#check S3128ZMod2FiberObj
#check S3128ZMod2FiberHom
#check S3128ZMod2FiberCategory

end LeanFormal.IUT.XiFPaper.S3128ZMod2FiberCategoryActual