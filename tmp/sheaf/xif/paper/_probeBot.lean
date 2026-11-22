import Mathlib.AlgebraicGeometry.Sites.Etale
import Mathlib.AlgebraicGeometry.Sites.Proetale
import Mathlib.CategoryTheory.Sites.Subcanonical

open CategoryTheory AlgebraicGeometry

namespace ProbeBot

example (X : AlgebraicGeometry.Scheme.{0}) : (⊥ : Sieve X) ∈ AlgebraicGeometry.Scheme.etaleTopology X := by
  rw [AlgebraicGeometry.Scheme.etaleTopology]
  apply Precoverage.generate_mem_toGrothendieck
  exact MorphismProperty.bot_mem_precoverage X

end ProbeBot
