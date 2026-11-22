import tmp.sheaf.xif.paper.S1543CorrectedGaussianArithmeticActual
import tmp.sheaf.xif.paper.S1544LTorsionKernelFieldActual
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic

/-! # S1545: corrected K from the actual l-torsion kernel field -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT.XiFPaper.S1545CorrectedGaussianKLiftActual
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S1280SourceDefinition31Actual
open LeanFormal.IUT.XiFPaper.S1543CorrectedGaussianArithmeticActual
open LeanFormal.IUT.XiFPaper.S1544LTorsionKernelFieldActual

variable {l : PrimeGeFive}

/-- The actual corrected K: the l-torsion kernel field of the Gaussian curve. -/
abbrev S1545K (b : GaussianTorsionBasis l) : Type :=
  gaussianKernelField (l := l) b

/-- NumberField instance for the finite kernel field, from finiteness over F. -/
local instance s1545NumberField (b : GaussianTorsionBasis l) :
    NumberField (S1545K (l := l) b) :=
  NumberField.of_module_finite (S1543Base l).F (S1545K (l := l) b)

/-- A nontrivial SL2 image forces the kernel field not to be bottom. -/
theorem kernelField_ne_bot_of_imageContainsSL2
    (b : GaussianTorsionBasis l)
    (hlarge : Subgroup.map Matrix.SpecialLinearGroup.toGL
      (⊤ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) (ZMod l.value))) ≤
      (gaussianLTorsionRepresentation (l := l) b).range) :
    gaussianKernelField (l := l) b ≠ ⊥ := by
  intro hbot
  have hfix : (gaussianKernelField (l := l) b).fixingSubgroup = ⊤ := by
    rw [hbot]
    exact IntermediateField.fixingSubgroup_bot
  have hker : (gaussianLTorsionRepresentation (l := l) b).ker = ⊤ := by
    rw [← gaussianKernelField_fixingSubgroup (l := l) b]
    exact hfix
  have hrep : gaussianLTorsionRepresentation (l := l) b = 1 :=
    MonoidHom.ker_eq_top_iff.mp hker
  have hrange : (gaussianLTorsionRepresentation (l := l) b).range = ⊥ :=
    MonoidHom.range_eq_bot_iff.mpr hrep
  have hle : Subgroup.map Matrix.SpecialLinearGroup.toGL
      (⊤ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) (ZMod l.value))) ≤
      (⊥ : Subgroup (Matrix.GeneralLinearGroup (Fin 2) (ZMod l.value))) := by
    rw [← hrange]
    exact hlarge
  let g : Matrix.SpecialLinearGroup (Fin 2) (ZMod l.value) :=
    ⟨!![1, 1; 0, 1], by simp [Matrix.det_fin_two]⟩
  have hg : Matrix.SpecialLinearGroup.toGL g ∈
      Subgroup.map Matrix.SpecialLinearGroup.toGL
        (⊤ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) (ZMod l.value))) :=
    Subgroup.mem_map_of_mem Matrix.SpecialLinearGroup.toGL (Subgroup.mem_top g)
  have hgbot : Matrix.SpecialLinearGroup.toGL g ∈
      (⊥ : Subgroup (Matrix.GeneralLinearGroup (Fin 2) (ZMod l.value))) := hle hg
  have hgone : Matrix.SpecialLinearGroup.toGL g = 1 := Subgroup.mem_bot.mp hgbot
  have hg1 : g = 1 := Matrix.SpecialLinearGroup.toGL_injective (by simpa using hgone)
  have hentry : g 0 1 =
      (1 : Matrix.SpecialLinearGroup (Fin 2) (ZMod l.value)) 0 1 :=
    congrArg (fun x => x 0 1) hg1
  simp [g] at hentry
  haveI : Fact (Nat.Prime l.value) := l.factPrime
  exact (one_ne_zero : (1 : ZMod l.value) ≠ 0) hentry

/-- Nontriviality of the corrected extension: finrank is not one. -/
theorem finrank_ne_one_of_imageContainsSL2
    (b : GaussianTorsionBasis l)
    (hlarge : Subgroup.map Matrix.SpecialLinearGroup.toGL
      (⊤ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) (ZMod l.value))) ≤
      (gaussianLTorsionRepresentation (l := l) b).range) :
    Module.finrank (S1543Base l).F (S1545K (l := l) b) ≠ 1 := by
  intro h1
  exact kernelField_ne_bot_of_imageContainsSL2 (l := l) b hlarge
    (IntermediateField.finrank_eq_one_iff.mp h1)

/-- Finrank lower bound 2 for the nontrivial kernel field. -/
theorem finrank_ge_two_of_imageContainsSL2
    (b : GaussianTorsionBasis l)
    (hlarge : Subgroup.map Matrix.SpecialLinearGroup.toGL
      (⊤ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) (ZMod l.value))) ≤
      (gaussianLTorsionRepresentation (l := l) b).range) :
    2 ≤ Module.finrank (S1543Base l).F (S1545K (l := l) b) := by
  have hpos : 0 < Module.finrank (S1543Base l).F (S1545K (l := l) b) :=
    Module.finrank_pos
  have hne := finrank_ne_one_of_imageContainsSL2 (l := l) b hlarge
  omega

/-- Fill S1543CorrectedK with the actual kernel field. -/
noncomputable def s1545CorrectedK
    (b : GaussianTorsionBasis l)
    (hlarge : Subgroup.map Matrix.SpecialLinearGroup.toGL
      (⊤ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) (ZMod l.value))) ≤
      (gaussianLTorsionRepresentation (l := l) b).range) :
    S1543CorrectedK l where
  K := S1545K (l := l) b
  nontrivial := finrank_ne_one_of_imageContainsSL2 (l := l) b hlarge

end LeanFormal.IUT.XiFPaper.S1545CorrectedGaussianKLiftActual
end