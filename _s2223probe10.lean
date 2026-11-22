
import Mathlib.Algebra.CubicDiscriminant
import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import LeanFormal.IUT.ABCBridge.Galois.EllipticDivisionPolynomialEvaluation

noncomputable section
open WeierstrassCurve
open Polynomial

namespace S2223Probe

variable {F : Type*} [Field F] [CharZero F]

noncomputable local instance decEqAlgClosure : DecidableEq (AlgebraicClosure F) := Classical.decEq _

example (W : WeierstrassCurve F) :
    ((W.twoTorsionPolynomial).map (algebraMap F (AlgebraicClosure F))).a = 4 := by
  simp only [Cubic.map, WeierstrassCurve.twoTorsionPolynomial]
  exact map_ofNat (algebraMap F (AlgebraicClosure F)) 4

end S2223Probe
end
