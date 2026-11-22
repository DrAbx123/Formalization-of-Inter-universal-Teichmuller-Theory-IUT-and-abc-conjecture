import Mathlib.RingTheory.Etale.Finite
import Mathlib.RingTheory.Artinian.Module
import Mathlib.RingTheory.Idempotents
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.Algebra.Algebra.Prod
import Mathlib.Algebra.Category.CommAlgCat.Basic

open CategoryTheory CategoryTheory.Limits

#check Ideal
#check ComplementedLattice.exists_isCompl
#check Submodule.exists_isCompl
#check AlgEquiv.ofRingEquiv
#check AlgEquiv.ofBijective
#check Ideal.quotientKerAlgEquivOfSurjective
#check Ideal.quotientInfEquivQuotientProd
#check Ideal.isCoprime_iff_sup_eq
#check AlgEquiv.quotientBot
#check AlgEquiv.prodCongr
#check AlgHom.prod
#check AlgHom.fst
#check RingHom.ker
#check IsArtinianRing.isSemisimpleRing_of_isReduced
#check Algebra.FormallyUnramified.isReduced_of_field
#check Algebra.FormallyUnramified.finite_of_free
#check isArtinian_of_tower
#check Ideal.quotientEquivAlgOfEq
#check Ideal.Quotient.mkₐ
