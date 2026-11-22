import tmp.sheaf.xif.paper.S2482CorrectedSourceSignQuotientActual
import LeanFormal.IUT.IUTI.InitialTheta.SourceClauseConstructors

noncomputable section
open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.XiFPaper.S2482CorrectedSourceSignQuotientActual
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option linter.checkUnivs false
set_option maxHeartbeats 16000000

namespace LeanFormal.IUT.XiFPaper.S2907bCorrectedClauseABCDFActual

universe u
variable {l : PrimeGeFive}
variable {A : InitialThetaArithmeticData.{u} l}

/-- Corrected canonical K-quotient data: exactly the corrected K-side torsion
basis, supplied explicitly by the corrected ClauseC. -/
noncomputable def canonicalKQuotientDataCorrected
    (torsion_basis :
      (Fin 2 → ZMod l.value) ≃ₗ[ZMod l.value]
        (A.curve.baseChange A.K).LTorsion l) :
    TorsionRankOneQuotientData l (A.curve.baseChange A.K) where
  torsion_basis := torsion_basis

@[simp] theorem canonicalKQuotientDataCorrected_torsion_basis
    (torsion_basis :
      (Fin 2 → ZMod l.value) ≃ₗ[ZMod l.value]
        (A.curve.baseChange A.K).LTorsion l) :
    (canonicalKQuotientDataCorrected (A := A) torsion_basis).torsion_basis =
      torsion_basis :=
  rfl

#check canonicalKQuotientDataCorrected
#check canonicalKQuotientDataCorrected_torsion_basis
#print axioms canonicalKQuotientDataCorrected

end LeanFormal.IUT.XiFPaper.S2907bCorrectedClauseABCDFActual
end
