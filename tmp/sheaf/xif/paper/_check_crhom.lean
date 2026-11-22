import Mathlib.AlgebraicGeometry.AffineScheme
open AlgebraicGeometry CategoryTheory
variable (R S : Type) [CommRing R] [CommRing S]
#check (fun (f : CommRingCat.of R ⟶ CommRingCat.of S) => f.hom)
#check (fun (f : CommRingCat.of R ⟶ CommRingCat.of S) => (f.hom : R →+* S))