import LeanFormal.IUT.IUTIII.Theorem311.SourceK1K2CardReduction
import LeanFormal.IUT.IUTIII.Theorem311.SourceK1K2VolumeTranslationLaw

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

noncomputable section

/-!
# Mzk1K1K2RayVolumePackagesActual — A479 real packages (K1/K2 univRay + volume laws)

New conclusions combining the donors of
\`SourceK1K2CardReduction.lean\` (:75/:78) and
\`SourceK1K2VolumeTranslationLaw.lean\` (:79/:90):

1. \`univRay_package\`: unboundedness and ray-separation of the universal
   real ray hold jointly;
2. \`volume_translation_chain\`: volume-translation data implies both the
   fiber-factor law and the class law, and the fiber-factor/class equivalence
   holds — three conclusions jointly.

No sorry/axioms; no closure claim.
-/

namespace LeanFormal.IUT.XiFPaper.Mzk1K1K2RayVolumePackagesActual

open LeanFormal.IUT
open LeanFormal.IUT.K1K2Realization

/-- Joint universal-ray package (up-unbounded + ray separation). -/
theorem univRay_package :
    (∀ x : Real, ∃ y ∈ (Set.univ : Set Real), x ≤ y) ∧
      (∀ x y : Real,
        (Set.univ : Set Real) ∩ Set.Ici x =
          (Set.univ : Set Real) ∩ Set.Ici y → x = y) :=
  ⟨upUnbounded_univ, raySeparation_univ⟩

/-- Joint K1/K2 volume-laws chain from volume-translation data. -/
theorem volume_translation_chain {ι : Type*} (volume : ι → Real) (F : Nat → ι → ι)
    (h : K1K2Realization.VolumeTranslationData volume F) :
    K1K2Realization.VolumeFiberFactorLaw volume F ∧
      K1K2Realization.VolumeClassLaw volume F ∧
      (K1K2Realization.VolumeFiberFactorLaw volume F ↔
        K1K2Realization.VolumeClassLaw volume F) :=
  ⟨(K1K2Realization.volumeFiberFactorLaw_iff_volumeClassLaw volume F).mpr
      (K1K2Realization.volumeClassLaw_of_volumeTranslationData volume F h),
   K1K2Realization.volumeClassLaw_of_volumeTranslationData volume F h,
   K1K2Realization.volumeFiberFactorLaw_iff_volumeClassLaw volume F⟩

#check univRay_package
#check volume_translation_chain

end LeanFormal.IUT.XiFPaper.Mzk1K1K2RayVolumePackagesActual
end