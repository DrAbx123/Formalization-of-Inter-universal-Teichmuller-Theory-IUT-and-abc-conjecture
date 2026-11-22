import tmp.sheaf.xif.paper.S3128OfHHelpersActual
import Mathlib.CategoryTheory.Comma.Over.Basic
open CategoryTheory
open Iut
noncomputable section
namespace LeanFormal.IUT.XiFPaper.S3128CanonicalHEndActual
variable {F : Type} [Field F] {X : HyperbolicOrbicurve F}
variable {U : SchemeOverField F}

noncomputable def S3128CanonicalMapIdIso
    (V : (Over U)ᵒᵖ) :
    (Over.map (𝟙 U)).op.obj V ≅ V :=
  (Iso.op ((Over.mapId U).app V.unop)).symm

structure S3128CanonicalHEnd (U : SchemeOverField F) where
  H : Over U ⥤ Over U
  hH : ∀ V : (Over U)ᵒᵖ, H.op.obj V ≅ V
  canonical_id :
    H = Over.map (𝟙 U) →
      HEq hH (fun V => S3128CanonicalMapIdIso (U := U) V)
  natural :
    ∀ {V W : (Over U)ᵒᵖ} (f : V ⟶ W),
      H.op.map f ≫ (hH W).hom = (hH V).hom ≫ f
  canonical_comp :
    ∀ (H₁ H₂ : Over U ⥤ Over U)
      (e : H = H₁ ⋙ H₂)
      (hH₁ : ∀ V : (Over U)ᵒᵖ, H₁.op.obj V ≅ V)
      (hH₂ : ∀ V : (Over U)ᵒᵖ, H₂.op.obj V ≅ V),
      HEq hH
        (fun V =>
          (hH₂ (H₁.op.obj V)).trans (hH₁ V))

noncomputable def S3128CanonicalHEnd.toNatIso
    (A : S3128CanonicalHEnd U) :
    A.H.op ≅ 𝟭 ((Over U)ᵒᵖ) :=
  NatIso.ofComponents A.hH A.natural

#check S3128CanonicalHEnd
#check S3128CanonicalHEnd.toNatIso
#check S3128CanonicalMapIdIso
end LeanFormal.IUT.XiFPaper.S3128CanonicalHEndActual