import tmp.sheaf.xif.paper.Mzk1P7ClauseCSupportActual
import LeanFormal.IUT.IUTI.InitialTheta.SourceTorsionCarrierReduction
import Mathlib.Tactic
noncomputable section
namespace LeanFormal.IUT.XiFPaper.Mzk1P7ClauseCActualDone
open LeanFormal.IUT LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.TorsionCarrierReduction
open LeanFormal.IUT.XiFPaper.Mzk1P7ClauseCSupportActual
universe u
variable {l : PrimeGeFive} {A : InitialThetaArithmeticData.{u} l}
    {S : SourceSignQuotientData A} {C : SourceClauseA A S}
    {B : SourceClauseB A S C}
/-- Actual clause-(c) record from a frozen torsion datum plus six-torsion rationality. -/
noncomputable def p7_sourceClauseC
    (D : SourceTorsionDatum l A)
    (torsion23Rational : PuncturedEllipticCurve.Torsion23Rational A.curve) :
    SourceClauseC A S C B :=
  D.toSourceClauseC (S := S) (C := C) (B := B) torsion23Rational
/-- P7 support for that actual clause-(c) record. -/
theorem p7_clauseC_support_of_torsionDatum
    (D : SourceTorsionDatum l A)
    (torsion23Rational : PuncturedEllipticCurve.Torsion23Rational A.curve) :
    P7ClauseCSupport (l := l)
      (p7_sourceClauseC (S := S) (C := C) (B := B) D torsion23Rational) :=
  p7_clauseC_support _
#print axioms p7_clauseC_support_of_torsionDatum
end LeanFormal.IUT.XiFPaper.Mzk1P7ClauseCActualDone
end