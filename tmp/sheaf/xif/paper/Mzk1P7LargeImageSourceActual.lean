/- P7 hT-free large-image source: the concrete transvection data comes from the
actual source clause C, so the D-indexed large-image theorem needs no external
transvection hypothesis. -/
import tmp.sheaf.xif.paper.Mzk1P7DLargeImageActual
import tmp.sheaf.xif.paper.Mzk1P7SourceTransvectionActual
import Mathlib.Tactic

noncomputable section
namespace LeanFormal.IUT.XiFPaper.Mzk1P7LargeImageSourceActual
open LeanFormal.IUT LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.XiFPaper.Mzk1P7DLargeImageActual
open LeanFormal.IUT.XiFPaper.Mzk1P7SourceTransvectionActual
open Matrix

variable {l : PrimeGeFive} {A : InitialThetaArithmeticData l}
    {S : SourceSignQuotientData A} {C : SourceClauseA A S}
    {B : SourceClauseB A S C}

/-- P7 large-image source, fully from Clause C: the transvection witness is the
actual source transvection, and the no-invariant-line condition is the actual
D-indexed hline. -/
theorem p7_D_largeImage_source (D : SourceClauseC A S C B)
    (g : Matrix.SpecialLinearGroup (Fin 2) (ZMod l.value)) :
    g.toGL ∈ (A.curve.galoisLTorsionMatrixRepresentation l D.torsion_basis).range :=
  p7_D_largeImage_of_transvection D (p7_source_transvection_data D) g

#print axioms p7_D_largeImage_source

end LeanFormal.IUT.XiFPaper.Mzk1P7LargeImageSourceActual
end
