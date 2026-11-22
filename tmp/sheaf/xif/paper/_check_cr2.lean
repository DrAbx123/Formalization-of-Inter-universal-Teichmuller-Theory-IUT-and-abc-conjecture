import Mathlib.AlgebraicGeometry.AffineScheme
#check CommRingCat.ofHom
#check (fun (f : CommRingCat.of (Rat) ⟶ CommRingCat.of (Rat)) => (ConcreteCategory.hom f : Rat -> Rat))
#check (fun (f : CommRingCat.of (Rat) ⟶ CommRingCat.of (Rat)) => (ConcreteCategory.hom f : Rat →+* Rat))
#print CommRingCat