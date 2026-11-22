import Mathlib.RingTheory.Etale.Finite
import Mathlib.CategoryTheory.Galois.Basic
import Mathlib.FieldTheory.AbsoluteGaloisGroup

noncomputable section
open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct

namespace S1769Probe

abbrev A : CommAlgCat.FiniteEtale.{0} ℚ := CommAlgCat.FiniteEtale.of ℚ (ℚ × ℚ)
abbrev B : CommAlgCat.FiniteEtale.{0} ℚ := CommAlgCat.FiniteEtale.of ℚ ℚ

def proj : A ⟶ B := CommAlgCat.FiniteEtale.ofHom (AlgHom.fst ℚ ℚ ℚ)

example : Mono proj := by infer_instance

example : Subsingleton (B ⟶ B) := by infer_instance

#check @AlgHom.fst

end S1769Probe