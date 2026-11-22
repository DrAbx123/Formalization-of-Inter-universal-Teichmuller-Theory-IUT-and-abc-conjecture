import tmp.sheaf.xif.paper.S1720SourceArithmeticActual

/-!
# S1721: base change of the rational 2*3-torsion

The S1720 paper input records the exact missing proposition
S1720Torsion23BaseChangeMissing: Torsion23Rational passes from a curve over
an algebraic extension field K to its base change.  This file proves it.

The proof uses the actual algebraic closure of K and a k-algebra
homomorphism sigma from AlgebraicClosure K to AlgebraicClosure k, obtained
from IsAlgClosed.lift.  A 6-torsion point P over AlgebraicClosure K is
pushed to AlgebraicClosure k by sigma; the rationality hypothesis for X
produces a k-point Q, and the naturality of Affine.Point.baseChange plus
injectivity of sigma gives P = baseChange Q.  No datum is postulated and no
point is chosen by hand.

The final section instantiates the general theorem at the actual S1720
field and curve, closing S1720Torsion23Missing as well.
-/

set_option backward.isDefEq.respectTransparency false

noncomputable section

open WeierstrassCurve WeierstrassCurve.Affine
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S1720SourceArithmeticActual

namespace LeanFormal.IUT.XiFPaper.S1721TorsionBaseChangeActual

variable {k K : Type} [Field k] [Field K] [Algebra k K]

/-- Tower compatibility of point base change with an intermediate field. -/
theorem point_baseChange_tower
    {L : Type} [Field L] [Algebra K L] [Algebra k L] [IsScalarTower k K L]
    [DecidableEq k] [DecidableEq K] [DecidableEq L]
    (W : WeierstrassCurve k) (Q : W.toAffine.Point) :
    Affine.Point.baseChange (W' := W) K L
        (Affine.Point.baseChange (W' := W) k K Q) =
      Affine.Point.baseChange (W' := W) k L Q := by
  change Affine.Point.map (W' := W) (IsScalarTower.toAlgHom k K L)
      (Affine.Point.map (W' := W) (Algebra.ofId k K) Q) =
    Affine.Point.map (W' := W) (Algebra.ofId k L) Q
  rw [Affine.Point.map_map]
  rw [show (IsScalarTower.toAlgHom k K L).comp (Algebra.ofId k K) =
      Algebra.ofId k L from by ext]

/-- The baseChange map computed with the intermediate curve W/K agrees with
the one computed with the original curve W.  The two curves are definitionally
equal after the tower of field maps is exposed. -/
theorem baseChange_intermediate_curve
    [DecidableEq k] [DecidableEq K] [DecidableEq (AlgebraicClosure K)]
    (W : WeierstrassCurve k) (Q : (W⁄K).Point) :
    Affine.Point.baseChange (W' := W⁄K) K (AlgebraicClosure K) Q =
      Affine.Point.baseChange (W' := W) K (AlgebraicClosure K) Q := by
  classical
  cases Q with
  | zero => rfl
  | some x y h => rfl

/-- Torsion23Rational is stable under base change along an algebraic field
extension.  This is the actual general statement recorded in S1720 as
S1720Torsion23BaseChangeMissing. -/
theorem S1721Torsion23Rational_baseChange
    [Algebra.IsAlgebraic k K]
    (X : PuncturedEllipticCurve k)
    (h : PuncturedEllipticCurve.Torsion23Rational X) :
    PuncturedEllipticCurve.Torsion23Rational (X.baseChange K) := by
  classical
  let W := X.curve.toAffine
  intro P hP
  change (W⁄(AlgebraicClosure K)).Point at P
  let sigma : AlgebraicClosure K →ₐ[k] AlgebraicClosure k := IsAlgClosed.lift
  let P1 : (W⁄(AlgebraicClosure k)).Point := Affine.Point.map (W' := W) sigma P
  have hP1 : (6 : ℕ) • P1 = 0 := by
    dsimp only [P1]
    rw [← AddMonoidHom.map_nsmul, hP, AddMonoidHom.map_zero]
  obtain ⟨Q, hQ⟩ := h P1 hP1
  refine ⟨Affine.Point.baseChange (W' := W) k K Q, ?_⟩
  apply Affine.Point.map_injective (W' := W) (f := sigma)
  change Affine.Point.map (W' := W) sigma
      (Affine.Point.baseChange (W' := W⁄K) K (AlgebraicClosure K)
        (Affine.Point.baseChange (W' := W) k K Q)) =
    Affine.Point.map (W' := W) sigma P
  rw [baseChange_intermediate_curve]
  rw [point_baseChange_tower (K := K) (L := AlgebraicClosure K) W Q]
  rw [Affine.Point.map_baseChange (W' := W) (f := sigma) Q]
  rw [hQ]

/-- The exact S1720 missing proposition, now proved. -/
theorem S1721S1720Torsion23BaseChangeMissing :
    S1720Torsion23BaseChangeMissing := by
  intro k K _ _ _ _ X h
  exact S1721Torsion23Rational_baseChange X h

/-- The literal paper condition (b) for the actual S1720 field and curve. -/
theorem S1721S1720Torsion23Missing :
    S1720Torsion23Missing :=
  S1720Torsion23Missing_of_baseChange S1721S1720Torsion23BaseChangeMissing

#print axioms S1721Torsion23Rational_baseChange
#print axioms S1721S1720Torsion23BaseChangeMissing
#print axioms S1721S1720Torsion23Missing

end LeanFormal.IUT.XiFPaper.S1721TorsionBaseChangeActual
