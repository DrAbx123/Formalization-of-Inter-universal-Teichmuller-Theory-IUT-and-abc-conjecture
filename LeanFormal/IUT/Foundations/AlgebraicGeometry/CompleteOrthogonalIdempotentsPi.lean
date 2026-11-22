import Mathlib.RingTheory.Idempotents
import Mathlib.Algebra.Algebra.Pi
import Mathlib.Tactic

set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
open scoped BigOperators

namespace CompleteOrthogonalIdempotentsPi

universe u v
variable {R A : Type u} [CommRing R] [CommRing A] [Algebra R A]
  {ι : Type v} [Fintype ι] [DecidableEq ι]

/-- Complete orthogonal idempotents in R give an R-algebra product decomposition
of any R-algebra A, with components A/(1-e_i)A. -/
noncomputable def completeOrthogonalIdempotentsAlgEquiv
    (e : ι → R) (he : CompleteOrthogonalIdempotents e) :
    A ≃ₐ[R] (∀ i, A ⧸ Ideal.span ({1 - algebraMap R A (e i)} : Set A)) := by
  classical
  let e' : ι → A := fun i => algebraMap R A (e i)
  have he' : CompleteOrthogonalIdempotents e' := he.map (algebraMap R A)
  let f : A →+* (∀ i, A ⧸ Ideal.span ({1 - e' i} : Set A)) :=
    RingHom.pi fun i => Ideal.Quotient.mk (Ideal.span ({1 - e' i} : Set A))
  let r : A ≃+* (∀ i, A ⧸ Ideal.span ({1 - e' i} : Set A)) :=
    RingEquiv.ofBijective f he'.bijective_pi
  refine AlgEquiv.ofRingEquiv (f := r) ?_
  intro x
  ext i
  rfl

end CompleteOrthogonalIdempotentsPi
