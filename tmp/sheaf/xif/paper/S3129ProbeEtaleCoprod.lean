import Mathlib.AlgebraicGeometry.Morphisms.Etale
import Mathlib.AlgebraicGeometry.Morphisms.AffineAnd
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace LeanFormal.IUT.XiFPaper.S3129ProbeEtaleCoprod
example : HasAffineProperty @Etale (affineAnd RingHom.Etale) := inferInstance
example {U V X : Scheme.{0}} (f : U ⟶ X) (g : V ⟶ X) [Etale f] [Etale g] :
    Etale (coprod.desc f g) := by
  refine HasAffineProperty.coprodDesc_affineAnd (P := @Etale)
    (Q := RingHom.Etale) inferInstance RingHom.Etale.respectsIso ?_ f g ‹_› ‹_›
  intro R S T _ _ _ f g hf hg
  algebraize [f, g]
  exact inferInstance
end LeanFormal.IUT.XiFPaper.S3129ProbeEtaleCoprod
end