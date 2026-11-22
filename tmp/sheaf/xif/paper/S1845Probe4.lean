import tmp.sheaf.xif.paper.S1831StrongSquareGeometricActual
import Mathlib.AlgebraicGeometry.Limits

noncomputable section
open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry
open Iut
open LeanFormal.IUT.XiFPaper.S1726OrbicurveFPrimeActual

abbrev F := S1726K
abbrev T : SchemeOverField F := S1726AffineOver
abbrev P : SchemeOverField F := Over.mk (Limits.coprod.desc T.hom T.hom)
noncomputable def fold : P ⟶ T := Over.homMk (show Over.left P ⟶ Over.left T from Limits.coprod.desc (𝟙 T.left) (𝟙 T.left)) (by
  show Limits.coprod.desc (𝟙 T.left) (𝟙 T.left) ≫ Over.hom T = Over.hom P
  rw [show Over.hom P = Limits.coprod.desc (Over.hom T) (Over.hom T) from rfl]
  rw [Limits.coprod.desc_comp]
  simp)
#check fold
