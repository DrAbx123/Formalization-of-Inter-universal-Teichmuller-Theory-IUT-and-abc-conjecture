import tmp.sheaf.xif.paper.S2813E37TwoFPointsActual

noncomputable section
open WeierstrassCurve LeanFormal.IUT CategoryTheory AlgebraicGeometry
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 8000000

namespace LeanFormal.IUT.XiFPaper.S2814E37ChartPointsActual

open LeanFormal.IUT.XiFPaper.S2801D6FaithfulActual
open LeanFormal.IUT.IUTII.Frobenioid.Example36
open LeanFormal.IUT.XiFPaper.S2813E37TwoFPointsActual

universe u

variable (K : Type u) [Field K] [DecidableEq K]

noncomputable def E37EvalAt (x y : K) : MvPolynomial (Fin 2) K →+* K :=
  MvPolynomial.eval ![x, y]

theorem E37EvalAt_relation (x y : K)
    (h : y ^ 2 + y = x ^ 3 - x) :
    E37EvalAt K x y (S2801E37Polynomial K) = 0 := by
  simp only [E37EvalAt, S2801E37Polynomial, S2801E37Curve,
    weierstrassAffinePolynomial]
  simp [Matrix.cons_val_zero, Matrix.cons_val_one]
  linear_combination h

noncomputable def E37ChartZPoint (x y : K)
    (h : y ^ 2 + y = x ^ 3 - x) :
    S2801E37CoordinateRing K →+* K :=
  Ideal.Quotient.lift (S2801E37Ideal K) (E37EvalAt K x y) (by
    have hle : S2801E37Ideal K ≤ RingHom.ker (E37EvalAt K x y) := by
      rw [S2801E37Ideal, Ideal.span_le]
      intro b hb
      rw [Set.mem_singleton_iff] at hb
      subst hb
      change E37EvalAt K x y (S2801E37Polynomial K) = 0
      exact E37EvalAt_relation K x y h
    intro a ha
    exact RingHom.mem_ker.mp (hle ha))

theorem E37ChartZPoint_X (x y : K) (h : y ^ 2 + y = x ^ 3 - x) :
    E37ChartZPoint K x y h (S2801E37X K) = x := by
  simp [E37ChartZPoint, E37EvalAt, S2801E37X, Ideal.Quotient.lift_mk]

theorem E37ChartZPoint_Y (x y : K) (h : y ^ 2 + y = x ^ 3 - x) :
    E37ChartZPoint K x y h (S2801E37Y K) = y := by
  simp [E37ChartZPoint, E37EvalAt, S2801E37Y, Ideal.Quotient.lift_mk]

#check E37ChartZPoint

noncomputable def E37ChartZSchemePoint (x y : K)
    (h : y ^ 2 + y = x ^ 3 - x) :
    (S2813Base K).left ⟶ S2801E37AffineScheme K :=
  Spec.map (CommRingCat.ofHom (E37ChartZPoint K x y h))

#check E37ChartZSchemePoint

#check E37ChartZPoint_X
#check E37ChartZPoint_Y
#print axioms E37ChartZPoint

end LeanFormal.IUT.XiFPaper.S2814E37ChartPointsActual
end
