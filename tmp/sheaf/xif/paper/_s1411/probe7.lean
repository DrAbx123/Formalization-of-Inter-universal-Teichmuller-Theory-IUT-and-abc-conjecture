import Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Degree

open Polynomial WeierstrassCurve

universe u

#check @normEDS
#check @WeierstrassCurve.ψ
#check @WeierstrassCurve.ψ₂
#check @WeierstrassCurve.preΨ₄
#check @WeierstrassCurve.Ψ₃

example {R : Type u} [CommRing R] (W : WeierstrassCurve R) :
    W.ψ = normEDS W.ψ₂ (Polynomial.C W.Ψ₃) (Polynomial.C W.preΨ₄) := rfl

example {R : Type u} [CommRing R] (W : WeierstrassCurve R) :
    W.ψ = (normEDS W.ψ₂ (Polynomial.C W.Ψ₃ : R[X][Y]) (Polynomial.C W.preΨ₄ : R[X][Y]) :
      ℤ → R[X][Y]) := rfl
