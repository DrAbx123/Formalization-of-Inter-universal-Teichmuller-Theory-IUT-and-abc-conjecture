import Mathlib.RingTheory.Etale.Finite
import Mathlib.CategoryTheory.Galois.Basic
import Mathlib.FieldTheory.AbsoluteGaloisGroup
import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory

noncomputable section
open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct

namespace S1769Probe

abbrev C : Type 1 := (CommAlgCat.FiniteEtale.{0} ℚ)ᵒᵖ
abbrev F : C ⥤ FintypeCat.{0} := CommAlgCat.FiniteEtale.fiber ℚ (AlgebraicClosure ℚ)

abbrev A : CommAlgCat.FiniteEtale.{0} ℚ := CommAlgCat.FiniteEtale.of ℚ (Fin 2 → ℚ)
abbrev B : CommAlgCat.FiniteEtale.{0} ℚ := CommAlgCat.FiniteEtale.of ℚ ℚ

def proj : A ⟶ B := CommAlgCat.FiniteEtale.ofHom (Pi.evalAlgHom ℚ (fun _ : Fin 2 => ℚ) 0)

instance selfInitial' (X : CommAlgCat.FiniteEtale.{0} ℚ) : Unique (B ⟶ X) where
  default := CommAlgCat.FiniteEtale.ofHom (Algebra.ofId ℚ X.obj)
  uniq f := by
    apply InducedCategory.hom_ext
    ext

theorem mono_proj : Mono proj := by
  refine ⟨fun {X} g h _ => ?_⟩
  exact Subsingleton.elim g h

def coord (i : Fin 2) : (Fin 2 → ℚ) →ₐ[ℚ] AlgebraicClosure ℚ where
  toFun x := algebraMap ℚ (AlgebraicClosure ℚ) (x i)
  map_one' := by simp
  map_mul' x y := by simp
  map_zero' := by simp
  map_add' x y := by simp
  commutes' q := by simp

def y0 : (F.obj (Opposite.op A)) := coord 0
def y1 : (F.obj (Opposite.op A)) := coord 1

theorem y0_ne_y1 : y0 ≠ y1 := by
  intro h
  have h2 := congrArg (fun (f : (Fin 2 → ℚ) →ₐ[ℚ] AlgebraicClosure ℚ) => f (Pi.single 0 1)) h
  simp [y0, y1, coord] at h2

example : Subsingleton (F.obj (Opposite.op B) : Type) := by
  change Subsingleton (ℚ →ₐ[ℚ] AlgebraicClosure ℚ)
  infer_instance

end S1769Probe