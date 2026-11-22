import tmp.sheaf.xif.paper.S1894D5LargeImageActual
import LeanFormal.IUT.IUTI.InitialTheta.SourceTorsionCarrierReduction

noncomputable section
open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.XiFPaper.S1894D5LargeImageActual
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 0

namespace LeanFormal.IUT.XiFPaper.S2835ImageContainsSL2Conditional

/-- l = 5 ClauseC image containment from a Serre-style large-image statement. -/
theorem S2835_imageContainsSL2_five
    {F : Type*} [Field F]
    (X : PuncturedEllipticCurve F)
    (h : InitialThetaSource.TorsionCarrierReduction.SerreStyleLargeImageStatement X
      S2771FiveLabel)
    (b : (Fin 2 → ZMod S2771FiveLabel.value) ≃ₗ[ZMod S2771FiveLabel.value]
      X.LTorsion S2771FiveLabel) :
    Subgroup.map Matrix.SpecialLinearGroup.toGL
        (⊤ : Subgroup (Matrix.SpecialLinearGroup (Fin 2)
          (ZMod S2771FiveLabel.value))) ≤
      (X.galoisLTorsionMatrixRepresentation S2771FiveLabel b).range := by
  obtain ⟨b0, h0⟩ := h
  have hb : S1894GenImageTail X S2771FiveLabel b :=
    (S1894GenImageTail_congr X S2771FiveLabel b b0).mpr h0
  exact hb

#check S2835_imageContainsSL2_five
#print axioms S2835_imageContainsSL2_five

end LeanFormal.IUT.XiFPaper.S2835ImageContainsSL2Conditional
end
