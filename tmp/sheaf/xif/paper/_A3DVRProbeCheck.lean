import Mathlib

noncomputable section
open Polynomial
namespace A3Probe

#check @IsDiscreteValuationRing.exists_irreducible
#check @IsDiscreteValuationRing.eq_unit_mul_pow_irreducible
#check @Algebra.algebraMapSubmonoid
#check @Localization.tensorRightAlgEquiv
#check @Algebra.Etale.baseChange
#check @Algebra.FormallyUnramified.isReduced_of_field
#check @isUnit_of_mem_nonZeroDivisors
#check @IsLocalization.of_le
#check @IsIntegralClosure.isIntegral_iff
#check @isIntegral_trans
#check @IsIntegral.tower_top
#check @IsIntegral.map
#check @IsFractionRing.isFractionRing_of_isLocalization
#check @IsLocalization.isFractionRing_of_isDomain_of_isLocalization
#check @isIntegrallyClosed_iff_isIntegrallyClosedIn
#check @isIntegrallyClosed_iff
#check @isIntegrallyClosedIn_iff
#check @IsLocalization.mk'_surjective
#check @IsLocalization.eq_iff_exists
#check @IsLocalization.map_units
#check @IsLocalization.injective
#check @Submonoid.map
#check @map_mem_nonZeroDivisors
#check @IsLocalization.map_mem_nonZeroDivisors
#check @Ideal.Quotient.algebraMap_eq
#check @Algebra.FormallyUnramified.isReduced

end A3Probe
