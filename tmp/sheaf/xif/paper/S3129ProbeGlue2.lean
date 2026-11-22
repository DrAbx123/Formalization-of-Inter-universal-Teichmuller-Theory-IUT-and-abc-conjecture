import Mathlib.AlgebraicGeometry.Gluing
open CategoryTheory AlgebraicGeometry
#check AlgebraicGeometry.Scheme.glueMorphisms
#check AlgebraicGeometry.Scheme.OpenCover.glueMorphisms
#check AlgebraicGeometry.Scheme.ι_glueMorphisms
#check Scheme.affineCover
#check (Scheme.affineCover (Spec (CommRingCat.of (ULift.{1} Nat))))
