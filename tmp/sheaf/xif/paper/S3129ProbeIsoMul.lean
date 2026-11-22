import Mathlib.AlgebraicGeometry.Scheme
import Mathlib.Algebra.Ring.Action.Group
open CategoryTheory AlgebraicGeometry
variable (A : Type) [CommRing A] (e f : A ≃+* A)
example : RingEquiv.toCommRingCatIso (e * f) = RingEquiv.toCommRingCatIso e ≪≫ RingEquiv.toCommRingCatIso f := by rfl
example : RingEquiv.toCommRingCatIso (e * f) = RingEquiv.toCommRingCatIso f ≪≫ RingEquiv.toCommRingCatIso e := by rfl
example : (e * f) = e.trans f := by rfl
example : (e * f) = f.trans e := by rfl
