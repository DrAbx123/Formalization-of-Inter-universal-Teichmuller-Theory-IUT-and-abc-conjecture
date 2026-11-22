import Mathlib.AlgebraicGeometry.Scheme
import Mathlib.Algebra.Ring.Action.Group
import Mathlib.CategoryTheory.Action.Basic
import tmp.sheaf.xif.paper.S3128AffineQuotientActual

noncomputable section
open CategoryTheory AlgebraicGeometry

namespace LeanFormal.IUT.XiFPaper.S3128SpecActionActual

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

variable {G : Type} [Group G] {A : Type} [CommRing A] [MulSemiringAction G A]

/-- The automorphism of Spec A induced by a group element. -/
noncomputable def S3128SpecAut (g : G) : Aut (Spec (CommRingCat.of A)) :=
  asIso (Spec.map (RingEquiv.toCommRingCatIso
    (MulSemiringAction.toRingEquiv G A g)).hom)

theorem S3128_toCommRingCatIso_one :
    RingEquiv.toCommRingCatIso (1 : A ≃+* A) = Iso.refl _ := by
  rfl

theorem S3128_toCommRingCatIso_mul (e f : A ≃+* A) :
    RingEquiv.toCommRingCatIso (e * f) =
      RingEquiv.toCommRingCatIso f ≪≫ RingEquiv.toCommRingCatIso e := by
  rfl

/-- The anti-action homomorphism Gᵐᵒᵖ → Aut (Spec A). -/
noncomputable def S3128SpecAutHom :
    Gᵐᵒᵖ →* Aut (Spec (CommRingCat.of A)) where
  toFun := fun x => S3128SpecAut (MulOpposite.unop x)
  map_one' := by
    change S3128SpecAut (MulOpposite.unop (1 : Gᵐᵒᵖ)) = 1
    rw [MulOpposite.unop_one]
    apply Aut.ext
    dsimp [S3128SpecAut]
    rw [show (MulSemiringAction.toRingEquiv G A) 1 = 1 from map_one _,
      S3128_toCommRingCatIso_one]
    change Spec.map (Iso.refl (CommRingCat.of A)).hom =
      𝟙 (Spec (CommRingCat.of A))
    simp [Iso.refl_hom, Spec.map_id]
  map_mul' := by
    intro x y
    change S3128SpecAut (MulOpposite.unop (x * y)) =
      S3128SpecAut (MulOpposite.unop x) *
        S3128SpecAut (MulOpposite.unop y)
    rw [MulOpposite.unop_mul]
    apply Aut.ext
    dsimp [S3128SpecAut]
    rw [show (MulSemiringAction.toRingEquiv G A)
        (MulOpposite.unop y * MulOpposite.unop x) =
        (MulSemiringAction.toRingEquiv G A) (MulOpposite.unop y) *
          (MulSemiringAction.toRingEquiv G A) (MulOpposite.unop x)
        from map_mul _ _ _,
      S3128_toCommRingCatIso_mul, Iso.trans_hom, Spec.map_comp,
      Aut.Aut_mul_def, Iso.trans_hom]
    simp

/-- The quotient map Spec A → Spec (A^G). -/
noncomputable def S3128SpecQuotientMap :
    Spec (CommRingCat.of A) ⟶
      Spec (CommRingCat.of (LeanFormal.IUT.XiFPaper.S3128AffineQuotientActual.S3128FixedSubring G A)) :=
  Spec.map (CommRingCat.ofHom
    (LeanFormal.IUT.XiFPaper.S3128AffineQuotientActual.S3128FixedSubring G A).subtype)

/-- The action of Gᵐᵒᵖ on Spec A induced contravariantly by the action on A. -/
noncomputable def S3128SpecAction : Action Scheme Gᵐᵒᵖ where
  V := Spec (CommRingCat.of A)
  ρ := (Aut.toEnd (Spec (CommRingCat.of A))).comp
    (S3128SpecAutHom (G := G) (A := A))

#check S3128SpecAut
#check S3128SpecAutHom
#check S3128SpecAction
#check S3128SpecQuotientMap

end LeanFormal.IUT.XiFPaper.S3128SpecActionActual
end