import Mathlib.RingTheory.Etale.Finite
import Mathlib.CategoryTheory.Galois.Basic
import Mathlib.FieldTheory.AbsoluteGaloisGroup

noncomputable section
open CategoryTheory CategoryTheory.Limits

namespace S1769Probe

abbrev A : CommAlgCat.FiniteEtale.{0} ℚ := CommAlgCat.FiniteEtale.of ℚ (Fin 2 → ℚ)
abbrev B : CommAlgCat.FiniteEtale.{0} ℚ := CommAlgCat.FiniteEtale.of ℚ ℚ

def proj : A ⟶ B := CommAlgCat.FiniteEtale.ofHom (Pi.evalAlgHom ℚ (fun _ : Fin 2 => ℚ) 0)

instance selfInitial' (X : CommAlgCat.FiniteEtale.{0} ℚ) : Unique (B ⟶ X) where
  default := CommAlgCat.FiniteEtale.ofHom (Algebra.ofId ℚ X.obj)
  uniq f := by
    apply InducedCategory.hom_ext
    ext

example : Mono proj := by
  refine ⟨?_, ?_⟩
  · trace_state
    sorry
  · sorry

end S1769Probe