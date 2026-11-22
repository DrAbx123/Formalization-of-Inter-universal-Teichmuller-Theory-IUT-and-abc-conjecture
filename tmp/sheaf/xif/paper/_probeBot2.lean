import Mathlib.AlgebraicGeometry.Sites.Etale
import Mathlib.AlgebraicGeometry.Sites.Proetale
import Mathlib.CategoryTheory.Sites.Subcanonical

open CategoryTheory AlgebraicGeometry

namespace ProbeBot

example (X : AlgebraicGeometry.Scheme.{0}) : Sieve.generate (⊥ : Presieve X) = ⊥ := by
  ext Y f
  simp [Sieve.generate]

example (X : AlgebraicGeometry.Scheme.{0}) : (⊥ : Sieve X) ∈ AlgebraicGeometry.Scheme.etaleTopology X := by
  change (⊥ : Sieve X) ∈ (MorphismProperty.coverage @Etale).toGrothendieck X
  rw [Coverage.mem_toGrothendieck]
  have h : (⊥ : Presieve X) ∈ (MorphismProperty.coverage @Etale).coverings X :=
    MorphismProperty.bot_mem_precoverage X
  have h2 := Coverage.Saturate.of X (⊥ : Presieve X) h
  simpa using h2

end ProbeBot
