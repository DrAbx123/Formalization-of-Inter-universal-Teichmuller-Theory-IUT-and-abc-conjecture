import tmp.sheaf.xif.paper.Mzk1P7LargeImageSourceDoneActual
import Mathlib.Tactic

noncomputable section
namespace LeanFormal.IUT.XiFPaper.Mzk1P7DownstreamLargeImageActual
open LeanFormal.IUT LeanFormal.IUT.InitialThetaSource
open Matrix

variable {l : PrimeGeFive} {A : InitialThetaArithmeticData l}
    {S : SourceSignQuotientData A} {C : SourceClauseA A S}
    {B : SourceClauseB A S C}

/-- P7 downstream large-image consumer. -/
theorem p7_downstream_largeImage (D : SourceClauseC A S C B) :
    ∀ M : Matrix.SpecialLinearGroup (Fin 2) (ZMod l.value),
      M.toGL ∈ (A.curve.galoisLTorsionMatrixRepresentation l D.torsion_basis).range :=
  LeanFormal.IUT.XiFPaper.Mzk1P7LargeImageSourceDoneActual.p7_D_largeImage_source D

#print axioms p7_downstream_largeImage
end LeanFormal.IUT.XiFPaper.Mzk1P7DownstreamLargeImageActual