import tmp.sheaf.xif.paper.S2817ClauseDFActual
import tmp.sheaf.xif.paper.S2823ClauseDConditionalActual
import tmp.sheaf.xif.paper.S2774ClauseCFromDataActual
noncomputable section
open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.XiFPaper.S2817ClauseDEFScaffold
open LeanFormal.IUT.XiFPaper.S2823ClauseDConditionalActual
open LeanFormal.IUT.XiFPaper.S2774ClauseCFromDataActual
open LeanFormal.IUT.XiFPaper.S2817ClauseDFActual
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option linter.checkUnivs false
set_option maxHeartbeats 16000000
namespace LeanFormal.IUT.XiFPaper.S2823ClauseDEFActual
universe u

/-- Bundled ClauseC-from-data plus D/E/F scaffolds.  ClauseC uses the actual
canonical representation with explicit imageContainsSL2/kernel-field inputs;
then ClauseD scaffold, ClauseE localFamily and ClauseF boundary are explicit.
-/
structure S2823ClauseDEFDataActual
    {l : PrimeGeFive} {A : InitialThetaArithmeticData.{u} l}
    {S : SourceSignQuotientData A} {C : SourceClauseA A S}
    {B : SourceClauseB A S C}
    (torsion23Rational : A.curve.Torsion23Rational)
    (torsionBasis : (Fin 2 → ZMod l.value) ≃ₗ[ZMod l.value]
      A.curve.LTorsion l)
    (imageContainsSL2 :
      Subgroup.map Matrix.SpecialLinearGroup.toGL ⊤ ≤
        (PuncturedEllipticCurve.galoisLTorsionMatrixRepresentation l
          A.curve torsionBasis).range)
    (kernelFieldIdentification :
      A.K ≃ₐ[A.F]
        (PuncturedEllipticCurve.galoisLTorsionKernelField l A.curve
          torsionBasis))
    (kernelFieldIdentificationRange :
      (Set.range fun x => (kernelFieldIdentification x :
        AlgebraicClosure A.F)) =
        (PuncturedEllipticCurve.galoisLTorsionKernelField l A.curve
          torsionBasis : Set (AlgebraicClosure A.F))) where
  clauseC : SourceClauseC A S C B :=
    S2774_sourceClauseC torsion23Rational torsionBasis imageContainsSL2
      kernelFieldIdentification kernelFieldIdentificationRange
  kSide : S2817ClauseDScaffold (l := l) (A := A) (S := S)
  clauseD : SourceClauseD A S C B clauseC :=
    S2817ClauseD kSide
  localFamily :
    SourceClauseELocalFamilyUnit A S C B clauseC clauseD
  clauseE : SourceClauseE A S C B clauseC clauseD :=
    SourceClauseELocalFamilyUnit.assemble localFamily
  boundary :
    SourceClauseFBoundaryUnit A S C B clauseC clauseD clauseE
  clauseF : SourceClauseF A S C B clauseC clauseD clauseE :=
    SourceClauseFBoundaryUnit.assemble boundary

#check S2823ClauseDEFDataActual
#check S2823ClauseDEFDataActual.clauseD
#check S2823ClauseDEFDataActual.clauseE
#check S2823ClauseDEFDataActual.clauseF

end LeanFormal.IUT.XiFPaper.S2823ClauseDEFActual