import tmp.sheaf.xif.paper.S2784KernelFieldActual
import tmp.sheaf.xif.paper.S1894D5LargeImageActual
import LeanFormal.IUT.IUTI.InitialTheta.SourceTorsionCarrierReduction

noncomputable section
open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.XiFPaper.S2784KernelFieldActual
open LeanFormal.IUT.XiFPaper.S1894D5LargeImageActual
open LeanFormal.IUT.XiFPaper.S2771Gap1ClosedActual
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 0
set_option synthInstance.maxHeartbeats 0
set_option maxRecDepth 100000

namespace LeanFormal.IUT.XiFPaper.S2835ImageContainsSL2Actual

local instance s2835GaussianFact :
    Fact (Irreducible (Polynomial.X ^ 2 - Polynomial.C (-1) : Polynomial ℚ)) :=
  ⟨gaussianPolynomial_irreducible⟩

/-- The arithmetic-37 curve and the S2771 5-torsion basis. -/
abbrev S2835Curve : PuncturedEllipticCurve GaussianField :=
  curve37Gaussian

abbrev S2835Basis :
    (Fin 2 → ZMod S2771FiveLabel.value) ≃ₗ[ZMod S2771FiveLabel.value]
      S2835Curve.LTorsion S2771FiveLabel :=
  basis37

/-- Basis-independence consumer: the Serre statement at an arbitrary basis
implies the SL2 containment at the fixed arithmetic-37 basis. -/
theorem S2835_imageContainsSL2_of_serre_at_basis
    (h : InitialThetaSource.TorsionCarrierReduction.SerreStyleLargeImageStatement
      S2835Curve S2771FiveLabel) :
    Subgroup.map Matrix.SpecialLinearGroup.toGL
        (⊤ : Subgroup (Matrix.SpecialLinearGroup (Fin 2)
          (ZMod S2771FiveLabel.value))) ≤
      (S2835Curve.galoisLTorsionMatrixRepresentation S2771FiveLabel
        S2835Basis).range := by
  let b0 : S1894GenBasis S2835Curve S2771FiveLabel := h.choose
  have h0 : S1894GenImageTail S2835Curve S2771FiveLabel b0 := h.choose_spec
  have hcongr := S1894GenImageTail_congr S2835Curve S2771FiveLabel
    S2835Basis b0
  exact hcongr.mpr h0

#check S2835_imageContainsSL2_of_serre_at_basis
#print axioms S2835_imageContainsSL2_of_serre_at_basis

end LeanFormal.IUT.XiFPaper.S2835ImageContainsSL2Actual
end
