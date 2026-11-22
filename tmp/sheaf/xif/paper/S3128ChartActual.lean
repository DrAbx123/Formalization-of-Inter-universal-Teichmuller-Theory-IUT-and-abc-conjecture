import Mathlib.AlgebraicGeometry.AffineScheme
import Mathlib.AlgebraicGeometry.Cover.Open

noncomputable section
open CategoryTheory AlgebraicGeometry

namespace LeanFormal.IUT.XiFPaper.S3128ChartActual

variable (T : Scheme)

/-- The ring of global sections of an affine chart. -/
noncomputable abbrev S3128ChartB (j : T.affineCover.I₀) : CommRingCat :=
  Γ(T.affineCover.X j, ⊤)

/-- The affine chart as Spec of its global sections. -/
noncomputable def S3128ChartIso (j : T.affineCover.I₀) :
    T.affineCover.X j ≅ Spec (S3128ChartB T j) :=
  Scheme.isoSpec (T.affineCover.X j)

variable {A : Type} [CommRing A]

/-- The chart cocone map. -/
noncomputable def S3128ChartCoconeMap
    (u : Spec (CommRingCat.of A) ⟶ T) (j : T.affineCover.I₀) :
    Spec (CommRingCat.of A) ⟶ Spec (S3128ChartB T j) :=
  u ≫ T.affineCover.f j ≫ (S3128ChartIso T j).hom

#check S3128ChartB
#check S3128ChartIso
#check S3128ChartCoconeMap

end LeanFormal.IUT.XiFPaper.S3128ChartActual
end