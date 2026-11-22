import Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Degree
open scoped nonZeroDivisors
open Equiv
namespace S1372
universe u
variable {R : Type u} [CommRing R] (W : ℤ → R)
section transf
variable (a b c d : ℤ)
def HaveSameParity₄ : Prop := a.negOnePow = b.negOnePow
#check HaveSameParity₄
namespace HaveSameParity₄
open Int Equiv
variable {W a b c d} (same : HaveSameParity₄ a b c d)
#check same
#check same.1
end HaveSameParity₄
end transf
end S1372
