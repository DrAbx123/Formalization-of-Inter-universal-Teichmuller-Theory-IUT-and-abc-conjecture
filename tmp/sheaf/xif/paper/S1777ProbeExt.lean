import Mathlib.RingTheory.Etale.Finite
import Mathlib.RingTheory.RingHom.Finite
import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Mathlib.AlgebraicGeometry.Morphisms.Etale
import Mathlib.AlgebraicGeometry.GammaSpecAdjunction
import Mathlib.AlgebraicGeometry.AffineScheme

noncomputable section
set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry

namespace Gen2

#check @MorphismProperty.Comma.ext
#check @CategoryTheory.Comma.ext
#check @CostructuredArrow.ext
#check @MorphismProperty.Comma.ext_iff
#check @CategoryTheory.Comma.ext_iff
#check @CommRingCat.of_eq
#check @CommRingCat.ofHom_hom

variable {R : Type} [CommRing R]

example (X : CommRingCat) : CommRingCat.of (↥X) = X := by
  cases X
  rfl

end Gen2
