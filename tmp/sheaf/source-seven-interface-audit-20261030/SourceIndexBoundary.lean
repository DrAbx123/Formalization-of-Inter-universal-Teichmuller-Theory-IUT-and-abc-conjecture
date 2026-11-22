import tmp.sheaf.xif.paper.S1231SourceCoreActual
import tmp.sheaf.xif.paper.S1232LogVolumeShiftActual
import tmp.sheaf.xif.paper.S1233ThetaPossibleImageActual
import LeanFormal.IUT.IUTIII.Theorem311.ParametricCarrier

/-!
Local audit of the seven-interface checklist. This does not identify lattice
translations with the paper's indeterminacies or the finite theta-scale image
with the paper's full allowed image family. It tests the existing interfaces
on exactly the currently implemented source-index operations.
-/

noncomputable section

namespace LeanFormal.IUT.SourceSevenInterfaceAudit

open Theorem311Source
open Theorem311Source.OriginalInput
open MultiradialKernel
open ParametricTheorem311
open XiFPaper.S1225SourceChoiceCoreActual
open XiFPaper.S1231SourceCoreActual
open XiFPaper.S1232LogVolumeShiftActual
open XiFPaper.S1233ThetaPossibleImageActual

universe ua uv upi umon ui
variable {l : PrimeGeFive} {V : Type uv}
variable (I : OriginalInput.{ua, uv, upi, umon, ui} l V)

/-- The existing scalar donors do assemble into the weak Profile interface.
This is an interface check, not an HDD readout or full possible-image theorem. -/
noncomputable def thetaScalarProfile :
    Profile (XiFPaper.S1231SourceCoreActual.sourceCore I) where
  logVolume := sourceLogVolume I
  possibleImage := thetaPossibleImage I
  ind1_invariant := fun _ _ => sourceLogVolume_eq I _ _
  ind2_invariant := fun _ _ => sourceLogVolume_eq I _ _
  ind3_upper := fun _ _ => le_of_eq (sourceLogVolume_eq I _ _)
  possibleImage_nonempty := thetaPossibleImage_nonempty I
  possibleImage_ind1 := fun _ _ => thetaPossibleImage_eq I _ _
  possibleImage_ind2 := fun _ _ => thetaPossibleImage_eq I _ _
  possibleImage_ind3 := by
    intro n c z hz
    refine ⟨z, ?_, le_rfl⟩
    rw [thetaPossibleImage_eq I _ c]
    exact hz

/-- Under the current definitions, the first Ind3 step is an Ind1 step. -/
theorem sourceInd3_one_eq_sourceInd1_neg_one (c : I.family.index) :
    sourceInd3 I 1 c = sourceInd1 I (-1) c := by
  unfold sourceInd3 sourceInd1
  simp only [neg_neg, zpow_one]
  exact (horizontalPerm_eq_translate I c).symm

/-- No choice of level repairs the strong grading while these operations
are held fixed. The obstruction is not specific to the constant-zero level. -/
theorem noExactGradingWithSourceOperations
    (C : Core ℤ I.family.index)
    (h1 : ∀ g c, C.ind1 g c = sourceInd1 I g c)
    (h3 : ∀ n c, C.ind3 n c = sourceInd3 I n c) :
    ¬ (∀ n c, C.level (C.ind3 n c) = C.level c + n) := by
  intro hlevel
  have hpreserve : C.level (C.ind3 1 C.base) = C.level C.base := by
    rw [h3, sourceInd3_one_eq_sourceInd1_neg_one I, ← h1]
    exact C.ind1_level (-1) C.base
  have hincrease := hlevel 1 C.base
  omega

/-- Consequently the present Carrier cannot use this exact pair of source
operations, even after changing level, profile, or connector. -/
theorem noCarrierWithSourceOperations :
    ¬ ∃ C : Carrier ℤ I.family.index,
      (∀ g c, C.core.ind1 g c = sourceInd1 I g c) ∧
      (∀ n c, C.core.ind3 n c = sourceInd3 I n c) := by
  rintro ⟨C, h1, h3⟩
  exact noExactGradingWithSourceOperations I C.core h1 h3 C.ind3_level_eq

#print axioms thetaScalarProfile
#print axioms sourceInd3_one_eq_sourceInd1_neg_one
#print axioms noExactGradingWithSourceOperations
#print axioms noCarrierWithSourceOperations

end LeanFormal.IUT.SourceSevenInterfaceAudit

end
