import tmp.sheaf.xif.paper.OrigXiFPaperLineBundleActual
import tmp.sheaf.xif.paper.OrigXiFPaperLineBundleODActual
/-! # S1497: exact native donor field for the paper O(-D) line bundle
D : OrigXiFPaperLineBundleData I requires an actual X : N8NativeInput l with
X.S.arithmetic = I.initial.arithmetic.  For the concrete Gaussian paper input
the tree supplies no SourceNativeInitialThetaData with that arithmetic, so no
actual X is constructed here.  The exact first field is stated as a subtype;
it is definitionally the donor structure, not a new weak Prop. -/
noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
namespace LeanFormal.IUT.XiFPaper.S1497NativeLineBundleDonorActual
open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.XiFPaper.OrigXiFPaperLineBundle
open LeanFormal.IUT.XiFPaper.OrigXiFPaperLineBundleODActual
universe uv upi umon ui
variable {l : PrimeGeFive} {V : Type uv}
/-- Exact native donor: an actual N8 native input whose arithmetic root is
the paper input's arithmetic root. -/
abbrev NativeDonorExact (I : OriginalInput.{0, uv, upi, umon, ui} l V) : Type 1 :=
  OrigXiFPaperLineBundleData I
-- No inhabitant is asserted; unconditional use of the O(-D) object is
-- equivalent to this exact native donor field.
#check origXiFPaperQPilotObjectOD
end LeanFormal.IUT.XiFPaper.S1497NativeLineBundleDonorActual
