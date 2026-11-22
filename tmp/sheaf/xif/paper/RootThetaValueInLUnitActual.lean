import tmp.sheaf.xif.paper.PaperRootCompletionTensorActual
import tmp.sheaf.xif.paper.PaperC3ThetaRootActual

/-! # Root theta value in L: nonzero/unit API and max label -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT.XiFPaper.RootThetaValueInLUnitActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.PaperRootCompletionTensorActual
open LeanFormal.IUT.XiFPaper.PaperThetaRootObstructionActual
open LeanFormal.IUT.XiFPaper.PaperC3ThetaRootActual

universe u

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable (b : Bad (nativePlaceSelection T))

/-- The root element in the ambient is nonzero. -/
theorem rootNormedElement_ne_zero : rootNormedElement T b ≠ 0 := by
  intro h
  exact (Units.ne_zero (sourceRoot T b)) (by simpa [rootNormedElement] using h)

/-- Positive powers of the root are nonzero. -/
theorem rootNormedElement_pow_ne_zero (n : Nat) :
    (rootNormedElement T b) ^ n ≠ 0 :=
  pow_ne_zero n (rootNormedElement_ne_zero T b)

/-- Integer powers of the root are nonzero. -/
theorem rootNormedElement_zpow_ne_zero (n : Int) :
    (rootNormedElement T b) ^ n ≠ 0 :=
  zpow_ne_zero n (rootNormedElement_ne_zero T b)

/-- Root theta value in the ambient is nonzero. -/
theorem rootNormedThetaValue_ne_zero (j : SignedLabel l.value) :
    rootNormedThetaValue T b j ≠ 0 :=
  rootNormedElement_zpow_ne_zero T b (gaussExponent j.1)

/-- Root theta value in L is nonzero. -/
theorem rootNormedThetaValueInL_ne_zero (j : SignedLabel l.value) :
    (rootNormedThetaValueInL T b j : rootNormedExtension T b) ≠ 0 := by
  intro h
  have hval : rootNormedThetaValue T b j = 0 := by
    have h' := congrArg (fun z : rootNormedExtension T b =>
      (z : rootNormedAmbient T b)) h
    simpa [rootNormedThetaValueInL] using h'
  exact rootNormedThetaValue_ne_zero T b j hval

/-- Norm positivity of the root theta value in L. -/
theorem rootNormedThetaValueInL_norm_pos (j : SignedLabel l.value) :
    0 < ‖(rootNormedThetaValueInL T b j : rootNormedExtension T b)‖ :=
  norm_pos_iff.mpr (rootNormedThetaValueInL_ne_zero T b j)

/-- Fintype of positive paper theta labels. -/
noncomputable instance thetaLabelFintype : Fintype (ThetaLabel (l := l)) :=
  inferInstance

/-- A distinguished positive theta label. -/
noncomputable def thetaLabelOne : ThetaLabel (l := l) :=
  ⟨(⟨(1 : Int), by
      have h5 := l.ge_five
      have hl : 1 ≤ lStar l.value := by
        rw [show lStar l.value = (l.value - 1) / 2 from rfl]
        rw [Nat.le_div_iff_mul_le (by norm_num : 0 < 2)]
        omega
      rw [Set.mem_Icc]
      constructor <;> omega⟩ : SignedLabel l.value), by norm_num⟩

/-- Nonempty positive theta labels. -/
theorem thetaLabel_nonempty : Nonempty (ThetaLabel (l := l)) :=
  ⟨thetaLabelOne (l := l)⟩

/-- A theta label with maximal root theta norm. -/
noncomputable def maxThetaLabel : ThetaLabel (l := l) :=
  Classical.choose (Finset.exists_max_image
    (Finset.univ : Finset (ThetaLabel (l := l)))
    (fun j => ‖(rootNormedThetaValueInL T b
      (thetaLabelToSigned (l := l) j) : rootNormedExtension T b)‖)
    ⟨thetaLabelOne (l := l), by simp⟩)

/-- Maximality of the chosen theta label. -/
theorem maxThetaLabel_spec (j : ThetaLabel (l := l)) :
    ‖(rootNormedThetaValueInL T b (thetaLabelToSigned (l := l) j) :
        rootNormedExtension T b)‖ ≤
      ‖(rootNormedThetaValueInL T b
        (thetaLabelToSigned (l := l) (maxThetaLabel (l := l) T b)) :
        rootNormedExtension T b)‖ := by
  exact (Classical.choose_spec (Finset.exists_max_image
    (Finset.univ : Finset (ThetaLabel (l := l)))
    (fun j => ‖(rootNormedThetaValueInL T b
      (thetaLabelToSigned (l := l) j) : rootNormedExtension T b)‖)
    ⟨thetaLabelOne (l := l), by simp⟩)).2 j (by simp)

end LeanFormal.IUT.XiFPaper.RootThetaValueInLUnitActual

end