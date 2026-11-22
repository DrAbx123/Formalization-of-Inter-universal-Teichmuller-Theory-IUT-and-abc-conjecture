import tmp.sheaf.xif.paper.S1280SourceDefinition31Actual
import tmp.sheaf.n8.closure.NativeInput
import tmp.sheaf.xif.paper.OrigXiFPaperLineBundleActual
/-! # S1503: bridge from concrete Gaussian arithmetic to native source data
A native donor X needs S : SourceNativeInitialThetaData with S.arithmetic =
S1280Arithmetic and a NativeLattice.  The paper SourceDefinition31Data does not
provide the native tuple/clauses; the exact first field is the subtype
NativeBridgeExact below.  Given it (and the arithmetic comparison for the paper
input), the O(-D) donor is actual; no fake X is constructed. -/
noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
namespace LeanFormal.IUT.XiFPaper.S1503SourceNativeBridgeActual
open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.N8Closure.NativeInput
open LeanFormal.IUT.XiFPaper.S1280SourceDefinition31Actual
open LeanFormal.IUT.XiFPaper.OrigXiFPaperLineBundle
universe uv upi umon ui
variable {l : PrimeGeFive}
/-- Exact first field: actual native initial Theta data whose arithmetic is
the concrete Gaussian arithmetic. -/
abbrev NativeBridgeExact : Type 1 :=
  { T : SourceNativeInitialThetaData l // T.arithmetic = S1280Arithmetic l }
/-- Exact native input field: an N8NativeInput with the concrete arithmetic. -/
abbrev NativeInputBridgeExact : Type 1 :=
  { X : N8NativeInput l // X.S.arithmetic = S1280Arithmetic l }
/-- Given the native bridge and the paper input's arithmetic comparison, the
O(-D) donor D is actual.  No X is fabricated: both exact fields are inputs. -/
noncomputable def donorOfBridge
    (I : OriginalInput.{0, uv, upi, umon, ui} l V)
    (X : NativeInputBridgeExact (l := l))
    (hroot : I.initial.arithmetic = S1280Arithmetic l) :
    OrigXiFPaperLineBundleData I where
  X := X.1
  arithmetic_root_eq := X.2.trans hroot.symm
-- The bridge is exactly the S1497 native donor field.
#check donorOfBridge
end LeanFormal.IUT.XiFPaper.S1503SourceNativeBridgeActual
