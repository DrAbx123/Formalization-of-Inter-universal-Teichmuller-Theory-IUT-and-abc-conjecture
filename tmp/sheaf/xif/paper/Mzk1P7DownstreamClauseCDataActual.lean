import tmp.sheaf.xif.paper.Mzk1P7ClauseCSupportActual
import Mathlib.Tactic

noncomputable section
namespace LeanFormal.IUT.XiFPaper.Mzk1P7DownstreamClauseCDataActual
open LeanFormal.IUT LeanFormal.IUT.InitialThetaSource

variable {l : PrimeGeFive} {A : InitialThetaArithmeticData l}
    {S : SourceSignQuotientData A} {C : SourceClauseA A S}
    {B : SourceClauseB A S C}

/-- P7 downstream Clause C support consumer. -/
theorem p7_downstream_clauseCData (D : SourceClauseC A S C B) :
    LeanFormal.IUT.XiFPaper.Mzk1P7ClauseCSupportActual.P7ClauseCSupport D :=
  LeanFormal.IUT.XiFPaper.Mzk1P7ClauseCSupportActual.p7_clauseC_support D

#print axioms p7_downstream_clauseCData
end LeanFormal.IUT.XiFPaper.Mzk1P7DownstreamClauseCDataActual