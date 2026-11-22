import tmp.sheaf.xif.paper.Mzk1B5LocalGlobalProductFormulaActual
import LeanFormal.IUT.Foundations.LocalFields.FinitePadicHaarScaling
/-! GAP-DET-HAAR step 4: central scalar p^m reduction -/
noncomputable section
namespace LeanFormal.IUT.XiFPaper.Mzk1GapDetHaarScalarActual
open LeanFormal.IUT.FinitePadicHaarScaling
/-- Scalar p-scaling donor. -/
def scalarDonors : List String :=
  [ "measure_prime_smul_finiteDimensional", "log_measure_prime_smul_finiteDimensional" ]
theorem scalarDonors_length : scalarDonors.length = 2 := rfl
/-- Remaining scalar step: central p^m contributes p^{-m*d} and composes with SNF. -/
def scalarMissing : List String :=
  [ "central p^m scalar factor",
    "composition with SNF diagonal and GL factors" ]
theorem scalarMissing_length : scalarMissing.length = 2 := rfl
end LeanFormal.IUT.XiFPaper.Mzk1GapDetHaarScalarActual
end
