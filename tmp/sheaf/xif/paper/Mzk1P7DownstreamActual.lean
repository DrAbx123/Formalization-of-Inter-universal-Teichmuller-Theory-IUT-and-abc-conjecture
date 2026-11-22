import tmp.sheaf.xif.paper.Mzk1P7ClauseCSupportActual
import tmp.sheaf.xif.paper.Mzk1P7LargeImageSourceDoneActual
import Mathlib.Tactic

noncomputable section
namespace LeanFormal.IUT.XiFPaper.Mzk1P7DownstreamActual
open LeanFormal.IUT LeanFormal.IUT.InitialThetaSource
open Matrix

variable {l : PrimeGeFive} {A : InitialThetaArithmeticData l}
    {S : SourceSignQuotientData A} {C : SourceClauseA A S}
    {B : SourceClauseB A S C}

/-- P7 downstream: Clause C support together with the full SL₂ large-image
source. -/
theorem p7_downstream_clauseC (D : SourceClauseC A S C B) :
    LeanFormal.IUT.XiFPaper.Mzk1P7ClauseCSupportActual.P7ClauseCSupport D ∧
    (∀ M : Matrix.SpecialLinearGroup (Fin 2) (ZMod l.value),
      M.toGL ∈ (A.curve.galoisLTorsionMatrixRepresentation l D.torsion_basis).range) :=
  ⟨LeanFormal.IUT.XiFPaper.Mzk1P7ClauseCSupportActual.p7_clauseC_support D,
    LeanFormal.IUT.XiFPaper.Mzk1P7LargeImageSourceDoneActual.p7_D_largeImage_source D⟩

#print axioms p7_downstream_clauseC
end LeanFormal.IUT.XiFPaper.Mzk1P7DownstreamActual