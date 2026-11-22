import tmp.sheaf.xif.paper.Mzk1G1PsiHPolyActual
import tmp.sheaf.xif.paper.Mzk1G1PsiFiberFiniteActual
import tmp.sheaf.xif.paper.Mzk1G1PsiQuotientFiniteActual
import Mathlib.Tactic

noncomputable section
namespace ProbeC2

open Polynomial
open LeanFormal.IUT.XiFPaper.Mzk1G1PsiHPolyActual
open LeanFormal.IUT.XiFPaper.Mzk1G1PsiFiberFiniteActual
open LeanFormal.IUT.XiFPaper.Mzk1G1PsiQuotientFiniteActual

#synth IsScalarTower ℚ (Polynomial ℚ) (Localization.Away (Polynomial.X : Polynomial ℚ))
#check @Polynomial.finset_sum_coeff
#check @Polynomial.coeff_C_mul
#check @Polynomial.coeff_X_pow
#check @Polynomial.le_natDegree_of_mem_supp
#check @Polynomial.leadingCoeff_ne_zero
#check @Polynomial.leadingCoeff_eq_zero
#check @Polynomial.mem_support_iff
#check @Polynomial.not_mem_support_iff
#check @Polynomial.monic_X_pow
#check @Polynomial.Monic.ne_zero
#check @IsLocalization.Away.algebraMap_isUnit
#check @IsLocalization.Away.mul_invSelf
#check @IsUnit.unit_spec
#check @inv_eq_of_mul_eq_one_right
#check @inv_eq_of_mul_eq_one_left
#check @IsLocalization.map_under
#check @Ideal.mem_comap
#check @PrimeSpectrum.comap
#check @Set.Finite.subset
#check @Set.Finite.image
#check @Polynomial.C_eq_algebraMap
#check @IsScalarTower.algebraMap_apply

end ProbeC2
