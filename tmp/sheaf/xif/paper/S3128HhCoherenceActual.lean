import tmp.sheaf.xif.paper.S3128OfHObjectActual
noncomputable section
open CategoryTheory
open Iut
open LeanFormal.IUT.XiFPaper.S3128QuotientSheafObjActual
open LeanFormal.IUT.XiFPaper.S3128QuotientSheafStrongActual
open LeanFormal.IUT.XiFPaper.S3128OfHMapActual
open LeanFormal.IUT.XiFPaper.S3128OfHObjectActual
namespace LeanFormal.IUT.XiFPaper.S3128HhCoherenceActual
variable {F : Type} [Field F] {X : HyperbolicOrbicurve F} {U : SchemeOverField F}
variable (H : Over U ⥤ Over U)
variable (hH : ∀ V : (Over U)ᵒᵖ, H.op.obj V ≅ V)

/-- hH 的自然性：H.op 与恒等函子之间的逐点同构应当是自然同构。 -/
def S3128HhNaturalityTarget : Prop :=
  ∀ {V W : (Over U)ᵒᵖ} (f : V ⟶ W),
    H.op.map f ≫ (hH W).hom = (hH V).hom ≫ f

#check S3128HhNaturalityTarget
end LeanFormal.IUT.XiFPaper.S3128HhCoherenceActual
end
