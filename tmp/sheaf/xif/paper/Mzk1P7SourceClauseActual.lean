/- P7 SourceClauseC actual reduction: from a frozen torsion datum plus 2/3-
torsion rationality the literal clause-(c) record is produced. The canonical
representation is definitional and the kernel-field range condition is
discharged internally. The K = F case is recorded as impossible. -/
import LeanFormal.IUT.IUTI.InitialTheta.SourceTorsionCarrierReduction
import tmp.sheaf.xif.paper.S1519NativeThetaConcreteActual
import Mathlib.Tactic

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace LeanFormal.IUT.XiFPaper.Mzk1P7SourceClauseActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.TorsionCarrierReduction
open LeanFormal.IUT.XiFPaper.S1519NativeThetaConcreteActual

variable {l : PrimeGeFive} {A : InitialThetaArithmeticData l}
    {S : SourceSignQuotientData A} {C : SourceClauseA A S}
    {B : SourceClauseB A S C}

/-- Actual clause-(c) record from the frozen torsion datum: the canonical
representation is definitional and the kernel-field range condition is
discharged by the datum. -/
noncomputable def sourceClauseC_of_torsionDatum
    (D : SourceTorsionDatum l A)
    (torsion23Rational : PuncturedEllipticCurve.Torsion23Rational A.curve) :
    SourceClauseC A S C B :=
  SourceTorsionDatum.toSourceClauseC (S := S) (C := C) (B := B)
    D torsion23Rational

@[simp] theorem sourceClauseC_of_torsionDatum_torsion_basis
    (D : SourceTorsionDatum l A)
    (torsion23Rational : PuncturedEllipticCurve.Torsion23Rational A.curve) :
    (sourceClauseC_of_torsionDatum (S := S) (C := C) (B := B) D
      torsion23Rational).torsion_basis = D.torsion_basis := rfl

@[simp] theorem sourceClauseC_of_torsionDatum_representation
    (D : SourceTorsionDatum l A)
    (torsion23Rational : PuncturedEllipticCurve.Torsion23Rational A.curve) :
    (sourceClauseC_of_torsionDatum (S := S) (C := C) (B := B) D
      torsion23Rational).representation = D.representation := rfl

/-- True blocker: when `K` is `F`-algebra equivalent to `F`, no clause-(c)
record exists (kernel-field identification contradicts large image). -/
theorem sourceClauseC_empty_of_K_algEquiv_F
    (hKA : Nonempty (A.K ≃ₐ[A.F] A.F)) :
    IsEmpty (SourceClauseC A S C B) :=
  S1519_sourceClauseC_empty hKA

theorem no_sourceClauseC_of_K_algEquiv_F
    (hKA : Nonempty (A.K ≃ₐ[A.F] A.F)) (D : SourceClauseC A S C B) : False :=
  S1519_no_sourceClauseC_false hKA D

#print axioms sourceClauseC_of_torsionDatum
#print axioms sourceClauseC_empty_of_K_algEquiv_F

end LeanFormal.IUT.XiFPaper.Mzk1P7SourceClauseActual
end
