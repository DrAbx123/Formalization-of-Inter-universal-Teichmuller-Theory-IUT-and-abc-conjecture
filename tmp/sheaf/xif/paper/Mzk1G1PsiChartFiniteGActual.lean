import tmp.sheaf.xif.paper.Mzk1G1FermatChartFiniteActual
import tmp.sheaf.xif.paper.Mzk1G1PsiChartMapsActual
import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
import Mathlib.Tactic

/-!
# R n finite over Q[g] (g = psiChart0Coord): first pieces

Adapted from grace's Mzk1G1FermatChartFiniteActual (which proves R n finite over Q[lambda],
lambda = x0^n).  Here t maps to g = psiChart0Coord (a product of linear factors in x0):
  gHom : Q[t] ->+* R n,  X |-> g
  gAlgebra : Algebra Q[t] R n
The monic relation for x0 over Q[t] is  prod (X - t_i) - T  (degree |T| >= 1), which will
give IsIntegral Q[t] (x0 n) and then Module.Finite Q[t] (R n) by grace's pattern
(Algebra.IsIntegral.finite with Algebra.FiniteType from adjoin {x0, y1} = top).
-/

noncomputable section
open Polynomial
namespace LeanFormal.IUT.XiFPaper.Mzk1G1PsiChartFiniteGActual
open LeanFormal.IUT.XiFPaper.Mzk1G1FermatAffineChartActual
open LeanFormal.IUT.XiFPaper.Mzk1G1PsiChartMapsActual

variable (n : Nat) (T : Finset ℚ)

/-- The algebra map Q[t] -> R n sending t to the protected product g. -/
noncomputable def gHom : Polynomial ℚ →+* R n :=
  Polynomial.eval₂RingHom (algebraMap ℚ (R n)) (psiChart0Coord n T)

/- The Q[t]-algebra structure on R n via g is declared as a definition (not a global
instance) because T cannot be inferred by typeclass synthesis; proofs that need it use
letI := gAlgebra n T. -/
noncomputable def gAlgebra : Algebra (Polynomial ℚ) (R n) :=
  (gHom n T).toAlgebra

theorem gHom_X : (gHom n T) Polynomial.X = psiChart0Coord n T := by
  simp [gHom]

/-- The monic polynomial over Q[t] whose value at x0 is zero:
prod (X - t_i) - T, of degree |T| (>= 1 when T is nonempty). -/
noncomputable def gMonicPoly : Polynomial (Polynomial ℚ) :=
  (∏ t ∈ T, (Polynomial.X - Polynomial.C (Polynomial.C t : Polynomial ℚ))) -
    Polynomial.C Polynomial.X

theorem gMonicPoly_monic (hT : T.Nonempty) : (gMonicPoly T).Monic := by
  have hprod : (∏ t ∈ T, (Polynomial.X - Polynomial.C (Polynomial.C t : Polynomial ℚ) :
      Polynomial (Polynomial ℚ))).Monic :=
    Polynomial.monic_prod_of_monic _ _ fun t _ => Polynomial.monic_X_sub_C _
  have hdeg : (Polynomial.C (Polynomial.X : Polynomial ℚ) :
      Polynomial (Polynomial ℚ)).natDegree <
      (∏ t ∈ T, (Polynomial.X - Polynomial.C (Polynomial.C t : Polynomial ℚ) :
        Polynomial (Polynomial ℚ))).natDegree := by
    rw [Polynomial.natDegree_C,
      Polynomial.natDegree_prod_of_monic _ _ fun t _ => Polynomial.monic_X_sub_C _]
    simp only [Polynomial.natDegree_X_sub_C, Finset.sum_const, smul_eq_mul, mul_one]
    exact Finset.card_pos.mpr hT
  have hne : (Polynomial.C (Polynomial.X : Polynomial ℚ) : Polynomial (Polynomial ℚ)) ≠ 0 :=
    Polynomial.C_ne_zero.mpr Polynomial.X_ne_zero
  have hdeg' : (Polynomial.C (Polynomial.X : Polynomial ℚ) : Polynomial (Polynomial ℚ)).degree <
      (∏ t ∈ T, (Polynomial.X - Polynomial.C (Polynomial.C t : Polynomial ℚ) :
        Polynomial (Polynomial ℚ))).degree := by
    rw [Polynomial.degree_eq_natDegree hne, Polynomial.degree_eq_natDegree hprod.ne_zero]
    exact_mod_cast hdeg
  exact hprod.sub_of_left hdeg'

#print axioms gHom_X
#print axioms gMonicPoly_monic
end LeanFormal.IUT.XiFPaper.Mzk1G1PsiChartFiniteGActual
