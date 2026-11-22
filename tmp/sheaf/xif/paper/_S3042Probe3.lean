import Mathlib.Algebra.MvPolynomial.Equiv
open MvPolynomial
#check MvPolynomial.uniqueAlgEquiv_apply
#check MvPolynomial.uniqueAlgEquiv_X
#check MvPolynomial.uniqueAlgEquiv_C
#check MvPolynomial.uniqueAlgEquiv_monomial
#check Polynomial.map_X
#check Polynomial.map_C
#check Polynomial.map_map
example : (MvPolynomial.uniqueAlgEquiv ℚ (Fin 1)) (MvPolynomial.X 0) = Polynomial.X := by simp
