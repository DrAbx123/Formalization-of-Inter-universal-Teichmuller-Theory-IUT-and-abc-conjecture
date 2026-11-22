import tmp.sheaf.xif.paper.S1779CorrectFiniteEtaleTargetActual
import Mathlib.RingTheory.Ideal.IdempotentFG
import Mathlib.RingTheory.Flat.EquationalCriterion
import Mathlib.RingTheory.Finiteness.ModuleFinitePresentation
import Mathlib.Algebra.Module.Projective

open CategoryTheory
open scoped TensorProduct

#check AlgEquiv.prodQuotientOfIsIdempotentElem
#check Ideal.quotientKerAlgEquivOfSurjective
#check Ideal.quotientKerAlgEquivOfSurjective_mk
#check Ideal.quotientEquivAlgOfEq
#check Module.Finite.quotient
#check Algebra.FinitePresentation.quotient
#check Module.projective_lifting_property
#check LinearMap.fg_range
#check Module.FinitePresentation.of_finite_of_finitePresentation
#check Module.Flat.projective_of_finitePresentation
#check Ideal.isIdempotentElem_iff_of_fg
#check CommRingCat.epi_iff_epi
#check RingHom.surjective_of_epi_of_finite
#check RingHom.finite_algebraMap
#check Module.Finite.of_restrictScalars_finite
#check Algebra.Etale.of_restrictScalars
#check Algebra.FormallyEtale.of_restrictScalars
#check Algebra.FormallyEtale.iff_of_surjective
