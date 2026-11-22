import tmp.sheaf.xif.paper.Mzk1G1PsiAffineOverlapActual
import tmp.sheaf.xif.paper.Mzk1G1FermatOverlapActual
import Mathlib.Tactic

noncomputable section
open AlgebraicGeometry Polynomial
namespace LeanFormal.IUT.XiFPaper.Mzk1G1PsiProductIdentityActual
open LeanFormal.IUT.XiFPaper.Mzk1G1FermatAffineChartActual
open LeanFormal.IUT.XiFPaper.Mzk1G1FermatSecondChartActual
open LeanFormal.IUT.XiFPaper.Mzk1G1FermatOverlapActual
open LeanFormal.IUT.XiFPaper.Mzk1G1PsiChartMapsActual
open LeanFormal.IUT.XiFPaper.Mzk1G1PsiAffineOverlapActual

variable (n : Nat)

/-- The substitution psi fixes rational constants. -/
theorem psiAux_C (t : ℚ) :
    psiAux n (MvPolynomial.C t) = algebraMap ℚ (OverlapInf n) t := by
  rw [psiAux_def, MvPolynomial.eval₂Hom_C]
  exact (RingHom.congr_fun (IsScalarTower.algebraMap_eq ℚ (ChartInfRing n) (OverlapInf n)) t).symm

theorem psi_algebraMap (t : ℚ) :
    psi n (algebraMap ℚ (R n) t) = algebraMap ℚ (OverlapInf n) t := by
  rw [algebraMap_rat_chart0, psi_mk]
  exact psiAux_C n t

/-- psi sends the x-coordinate to iu1. -/
theorem psi_chartX : psi n (chartX n) = iu1 n := by
  show psi n (Ideal.Quotient.mk (ideal0 n) (MvPolynomial.X 0)) = iu1 n
  rw [psi_mk, psiAux_zero]

/-- Each linear factor transports to a unit multiple. -/
theorem psi_linear_factor (t : ℚ) :
    psi n (chartX n - algebraMap ℚ (R n) t) =
      iu1 n * (1 - algebraMap ℚ (OverlapInf n) t * u1 n) := by
  rw [map_sub, psi_chartX n, psi_algebraMap n t]
  rw [show iu1 n * (1 - algebraMap ℚ (OverlapInf n) t * u1 n) =
      iu1 n - algebraMap ℚ (OverlapInf n) t from by
    rw [mul_sub, mul_one,
      show iu1 n * (algebraMap ℚ (OverlapInf n) t * u1 n) = algebraMap ℚ (OverlapInf n) t from by
        rw [← mul_assoc, mul_comm (iu1 n) (algebraMap ℚ (OverlapInf n) t), mul_assoc,
          iu1_mul_u1, mul_one]]]

/-- The localization of q is the product of the (1 - t*r) factors. -/
theorem algMap_psiChartInfDenom (T : Finset ℚ) :
    algebraMap (R2 n) (OverlapInf n) (psiChartInfDenom n T) =
      ∏ t ∈ T, (1 - algebraMap ℚ (OverlapInf n) t * u1 n) := by
  rw [psiChartInfDenom, map_prod]
  refine Finset.prod_congr rfl ?_
  intro t ht
  rw [map_sub, map_one, map_mul]
  rw [show (algebraMap (R2 n) (OverlapInf n)) (algebraMap ℚ (R2 n) t) =
    algebraMap ℚ (OverlapInf n) t from
    (RingHom.congr_fun (IsScalarTower.algebraMap_eq ℚ (R2 n) (OverlapInf n)) t).symm]
  rw [show (algebraMap (R2 n) (OverlapInf n)) (chartR n) = u1 n from rfl]

/-- THE PRODUCT IDENTITY: psi(product of (x - t)) = iu1^|T| * algebraMap of q. -/
theorem psi_psiChart0Coord (T : Finset ℚ) :
    psi n (psiChart0Coord n T) =
      iu1 n ^ T.card * algebraMap (R2 n) (OverlapInf n) (psiChartInfDenom n T) := by
  rw [psiChart0Coord, map_prod]
  rw [Finset.prod_congr rfl (fun t ht => psi_linear_factor n t)]
  rw [Finset.prod_mul_distrib, Finset.prod_const, ← algMap_psiChartInfDenom n T]

#print axioms psi_algebraMap
#print axioms psi_psiChart0Coord
end LeanFormal.IUT.XiFPaper.Mzk1G1PsiProductIdentityActual
