import tmp.sheaf.xif.paper.Mzk1P7SourceTorsionDatumActual
import tmp.sheaf.xif.paper.Mzk1P7ClauseCSupportActual
import tmp.sheaf.xif.paper.Mzk1P7LargeImageSourceDoneActual
import Mathlib.Tactic
noncomputable section
namespace LeanFormal.IUT.XiFPaper.Mzk1P7NativeSourceActual
open LeanFormal.IUT LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.N8Closure.NativeInput
open LeanFormal.IUT.XiFPaper.Mzk1P7SourceTorsionDatumActual
open LeanFormal.IUT.XiFPaper.Mzk1P7ClauseCSupportActual
open LeanFormal.IUT.XiFPaper.Mzk1P7LargeImageSourceDoneActual
open Matrix
variable {l : PrimeGeFive} (X : N8NativeInput l)
/-- P7 native source: clause-(c) support for the reconstructed actual
SourceClauseC. -/
theorem p7_native_clauseC_support :
    P7ClauseCSupport (l := l) (sourceClauseC_of_native X) :=
  p7_clauseC_support _
/-- P7 native source: full SL2 large-image for the reconstructed
SourceClauseC. -/
theorem p7_native_largeImage :
    ∀ M : Matrix.SpecialLinearGroup (Fin 2) (ZMod l.value),
      M.toGL ∈ (X.S.arithmetic.curve.galoisLTorsionMatrixRepresentation
        l (sourceClauseC_of_native X).torsion_basis).range :=
  p7_D_largeImage_source (sourceClauseC_of_native X)
#print axioms p7_native_clauseC_support
#print axioms p7_native_largeImage
end LeanFormal.IUT.XiFPaper.Mzk1P7NativeSourceActual
end