import tmp.sheaf.xif.paper.S3128SchemeCoproductBaseChangeActual
import Mathlib.CategoryTheory.Limits.Shapes.Products
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Iut
open LeanFormal.IUT.XiFPaper.S3128ZMod2FiberCategoryActual
open LeanFormal.IUT.XiFPaper.S3128SchemeCoproductBaseChangeActual
set_option linter.unusedVariables false
namespace LeanFormal.IUT.XiFPaper.S3128CoproductSimplificationActual
variable {F : Type} [Field F] {X : HyperbolicOrbicurve F}
variable {U U' : SchemeOverField F} (f : U' ⟶ U)
variable (A : S3128ZMod2FiberObj (F := F) X U)

abbrev S3128Q : Scheme :=
  pullback (Over.Hom.left A.proj) (Over.Hom.left f)

/-- Coproduct over `Unit` is the single factor. -/
noncomputable def S3128UnitCoproductIso :
    (∐ (fun _ : Unit => Over.left U')) ≅ Over.left U' :=
  coproductUniqueIso _

/-- Reindex `Bool × Unit` to `Bool`, hence the two-copy coproduct. -/
noncomputable def S3128BoolUnitCoproductIso :
    (∐ (fun _ : Bool × Unit => S3128Q f A)) ≅
      (∐ (fun _ : Bool => S3128Q f A)) :=
  Sigma.whiskerEquiv
    (J := Bool × Unit) (K := Bool)
    (f := fun _ : Bool × Unit => S3128Q f A)
    (g := fun _ : Bool => S3128Q f A)
    (Equiv.prodUnique Bool Unit)
    (fun _ : Bool × Unit => Iso.refl (S3128Q f A))


/-- Bool-indexed coproduct is the binary coproduct. -/
noncomputable def S3128BoolBinaryCoproductIso :
    (∐ (fun _ : Bool => S3128Q f A)) ≅
      (S3128Q f A ⨿ S3128Q f A) where
  hom := Sigma.desc (fun b : Bool =>
    if b then coprod.inl else coprod.inr)
  inv := coprod.desc
    (Sigma.ι (fun _ : Bool => S3128Q f A) true)
    (Sigma.ι (fun _ : Bool => S3128Q f A) false)
  hom_inv_id := by
    apply Sigma.hom_ext
    intro b
    cases b
    · rw [← Category.assoc, Sigma.ι_desc]
      simp only [Bool.false_eq_true, if_false]
      rw [coprod.inr_desc]
      simp
    · rw [← Category.assoc, Sigma.ι_desc]
      simp only [if_true]
      rw [coprod.inl_desc]
      simp
  inv_hom_id := by
    apply coprod.hom_ext
    · simp [Sigma.ι_desc]
    · simp [Sigma.ι_desc]

noncomputable def S3128WalkingPairBinaryIso (Q : Scheme) :
    (∐ (fun i : WalkingPair =>
      match i with
      | WalkingPair.left => Q
      | WalkingPair.right => Q)) ≅ (Q ⨿ Q) where
  hom := Sigma.desc (fun i : WalkingPair =>
    match i with
    | WalkingPair.left => coprod.inl
    | WalkingPair.right => coprod.inr)
  inv := coprod.desc
    (Sigma.ι (fun i : WalkingPair =>
      match i with
      | WalkingPair.left => Q
      | WalkingPair.right => Q) WalkingPair.left)
    (Sigma.ι (fun i : WalkingPair =>
      match i with
      | WalkingPair.left => Q
      | WalkingPair.right => Q) WalkingPair.right)
  hom_inv_id := by
    apply Sigma.hom_ext
    intro i
    cases i
    · rw [← Category.assoc, Sigma.ι_desc]
      simp [coprod.inl_desc]
    · rw [← Category.assoc, Sigma.ι_desc]
      simp [coprod.inr_desc]
  inv_hom_id := by
    apply coprod.hom_ext <;> simp [Sigma.ι_desc]

#check S3128UnitCoproductIso
#check S3128BoolUnitCoproductIso
#print axioms S3128BoolUnitCoproductIso
#check S3128BoolBinaryCoproductIso
#print axioms S3128BoolBinaryCoproductIso

end LeanFormal.IUT.XiFPaper.S3128CoproductSimplificationActual