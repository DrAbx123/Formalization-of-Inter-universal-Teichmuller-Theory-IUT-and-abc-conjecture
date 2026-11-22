import Mathlib.AlgebraicGeometry.Sites.Etale
import Mathlib.CategoryTheory.Sites.MorphismProperty
open CategoryTheory AlgebraicGeometry
noncomputable section
namespace P2234
#check MorphismProperty.bot_mem_precoverage
#check Precoverage.generate_mem_toGrothendieck
#check AlgebraicGeometry.Scheme.etaleTopology
#check AlgebraicGeometry.Scheme.etalePrecoverage
example (X : AlgebraicGeometry.Scheme) : (⊥ : Sieve X) ∈ AlgebraicGeometry.Scheme.etaleTopology X := by
  rw [AlgebraicGeometry.Scheme.etaleTopology]
  -- unfold grothendieckTopology coverage? 
  sorry
end P2234
end
