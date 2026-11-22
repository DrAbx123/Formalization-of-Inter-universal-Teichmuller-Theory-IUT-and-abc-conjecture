import tmp.sheaf.xif.paper.ArithmeticLineBundleActual
import LeanFormal.IUT.IUTIII.Corollary312.StepXI.HolomorphicHull.SourceHullCompactnessReduction

noncomputable section
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT.XiFPaper.S2755LineBundleIQHullDesign

open LeanFormal.IUT
open LeanFormal.IUT.XiFPaperArithmeticLineBundle

universe u

variable {l : PrimeGeFive} (A : InitialThetaArithmeticData l)

/-- The explicit **surrogate** discrete log-volume: `1` for a nonempty set, `0`
for the empty set.  This is a real (ENNReal-valued, monotone) log-volume on an
arbitrary carrier, but it is NOT the paper Haar/source log-volume. -/
noncomputable def S2755IndicatorVolume (X : Type u) (S : Set X) : ENNReal := by
  classical
  exact if S.Nonempty then 1 else 0

theorem S2755IndicatorVolume_mono {X : Type u} {S T : Set X} (hST : S ⊆ T) :
    S2755IndicatorVolume X S ≤ S2755IndicatorVolume X T := by
  classical
  unfold S2755IndicatorVolume
  split_ifs with hS hT
  · exact le_rfl
  · exact absurd (hS.mono hST) hT
  · simp
  · exact le_rfl

theorem S2755IndicatorVolume_nonempty {X : Type u} {S : Set X}
    (hS : S.Nonempty) : S2755IndicatorVolume X S = 1 := by
  classical
  simp [S2755IndicatorVolume, hS]

/-- Counting/indicator surrogate interface on the line-bundle carrier.  It is an
actual `IQHullLogVolumeInterface`, but only a surrogate: the log-volume is the
0/1 indicator, not the source/Haar log-volume, and the hull is the singleton
point, not a paper theta hull. -/
noncomputable def S2755LineBundleIndicatorInterface
    (J : SourceLineBundle (A := A)) :
    IQHullLogVolumeInterface (SourceLineBundle (A := A)) where
  imageSet := {J}
  hull := {J}
  imageSet_subset_hull := subset_rfl
  logVolume := S2755IndicatorVolume (SourceLineBundle (A := A))
  logVolume_mono := by
    intro S T hST
    exact S2755IndicatorVolume_mono hST
  unitRegion := {1}
  scaleShift := fun x => J * x
  hull_subset_scaleShift := by
    intro x hx
    have hxJ : x = J := by simpa using hx
    subst hxJ
    exact ⟨1, by simp, by simp⟩
  unitRegion_logVolume_lt_top := by
    rw [S2755IndicatorVolume_nonempty (by exact ⟨1, by simp⟩)]
    exact ENNReal.one_lt_top
  scaleShift_unitRegion_logVolume_le := by
    rw [S2755IndicatorVolume_nonempty (by exact ⟨J, by simp⟩)]
    rw [S2755IndicatorVolume_nonempty (by exact ⟨(1 : SourceLineBundle (A := A)), by simp⟩)]

/-- The surrogate interface is actual, but it is explicitly NOT the paper
log-volume interface: the log-volume is the indicator `1/0`, so no Haar/source
log-volume identity is claimed. -/
theorem S2755LineBundleIndicatorInterface_isSurrogate
    (J : SourceLineBundle (A := A)) :
    (S2755LineBundleIndicatorInterface A J).logVolume =
      S2755IndicatorVolume (SourceLineBundle (A := A)) := rfl

#check S2755IndicatorVolume
#check S2755IndicatorVolume_mono
#check S2755LineBundleIndicatorInterface
#check S2755LineBundleIndicatorInterface_isSurrogate
#print axioms S2755LineBundleIndicatorInterface

end LeanFormal.IUT.XiFPaper.S2755LineBundleIQHullDesign
end
