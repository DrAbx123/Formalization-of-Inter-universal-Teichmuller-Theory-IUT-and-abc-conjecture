import Mathlib.AlgebraicGeometry.Sites.Etale
import Mathlib.AlgebraicGeometry.Limits
import Mathlib.CategoryTheory.Sites.Over

open CategoryTheory AlgebraicGeometry

namespace ProbeBot5

#check @AlgebraicGeometry.Scheme.emptyTo
#print AlgebraicGeometry.Scheme.emptyTo
#check @Precoverage.instInf
#check @Precoverage.mem_inf
#check @AlgebraicGeometry.Scheme.jointlySurjectivePrecoverage

example (X : AlgebraicGeometry.Scheme.{0}) [IsEmpty X] :
    (⊥ : Sieve X) ∈ AlgebraicGeometry.Scheme.etaleTopology X := by
  change (⊥ : Sieve X) ∈ (AlgebraicGeometry.Scheme.precoverage @Etale).toGrothendieck X
  apply Precoverage.generate_mem_toGrothendieck
  change (⊥ : Presieve X) ∈ AlgebraicGeometry.Scheme.jointlySurjectivePrecoverage X ⊓
    (MorphismProperty.precoverage @Etale) X
  constructor
  · rw [CategoryTheory.Presieve.mem_comap_jointlySurjectivePrecoverage_iff]
    intro x
    exact isEmptyElim x
  · exact MorphismProperty.bot_mem_precoverage X

end ProbeBot5
