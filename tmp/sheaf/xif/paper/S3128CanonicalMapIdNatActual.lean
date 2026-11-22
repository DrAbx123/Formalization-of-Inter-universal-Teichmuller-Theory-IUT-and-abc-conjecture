import tmp.sheaf.xif.paper.S3128CanonicalHEndActual
open CategoryTheory
open Iut
open LeanFormal.IUT.XiFPaper.S3128CanonicalHEndActual
noncomputable section
namespace LeanFormal.IUT.XiFPaper.S3128CanonicalMapIdNatActual
variable {F : Type} [Field F] {X : HyperbolicOrbicurve F} {U : SchemeOverField F}

noncomputable def S3128CanonicalMapIdNatIso :
    (Over.map (𝟙 U)).op ≅ 𝟭 ((Over U)ᵒᵖ) :=
  (NatIso.op (Over.mapId U)).symm ≪≫
    Functor.opId (Over U)

theorem S3128CanonicalMapIdNatIso_app
    (V : (Over U)ᵒᵖ) :
    (S3128CanonicalMapIdNatIso (F := F) (U := U)).app V =
      S3128CanonicalMapIdIso (F := F) (U := U) V :=
  rfl

#check S3128CanonicalMapIdNatIso
#check S3128CanonicalMapIdNatIso_app
end LeanFormal.IUT.XiFPaper.S3128CanonicalMapIdNatActual