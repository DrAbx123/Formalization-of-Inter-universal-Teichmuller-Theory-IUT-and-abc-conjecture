import tmp.sheaf.xif.paper.S2814E37ChartPointsActual

noncomputable section
open WeierstrassCurve LeanFormal.IUT CategoryTheory AlgebraicGeometry
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 8000000

namespace LeanFormal.IUT.XiFPaper.S2814bE37ChartZOverActual

open LeanFormal.IUT.XiFPaper.S2801D6FaithfulActual
open LeanFormal.IUT.XiFPaper.S2813E37TwoFPointsActual
open LeanFormal.IUT.XiFPaper.S2814E37ChartPointsActual

universe u
variable (K : Type u) [Field K] [DecidableEq K]
variable (x y : K) (h : y ^ 2 + y = x ^ 3 - x)

theorem E37ChartZPoint_comp_algebraMap :
    (E37ChartZPoint K x y h).comp
      (algebraMap K (S2801E37CoordinateRing K)) = RingHom.id K := by
  ext c
  simp only [RingHom.comp_apply, RingHom.id_apply]
  change (E37ChartZPoint K x y h)
    ((Ideal.Quotient.mk (S2801E37Ideal K)) (MvPolynomial.C c)) = c
  unfold E37ChartZPoint
  rw [Ideal.Quotient.lift_mk]
  simp [E37EvalAt]

#check E37ChartZPoint_comp_algebraMap
#print axioms E37ChartZPoint_comp_algebraMap

end LeanFormal.IUT.XiFPaper.S2814bE37ChartZOverActual
end
