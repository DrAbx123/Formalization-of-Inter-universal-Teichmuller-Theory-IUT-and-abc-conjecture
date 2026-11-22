import tmp.sheaf.xif.paper.S1494NativeArithmeticRootActual
import tmp.sheaf.xif.paper.S1280SourceDefinition31Actual
import tmp.sheaf.xif.paper.S1360D9OrbicurveSlotActual
/-! # S1532: A2 field for the concrete Gaussian native root
S1494 reduces OrigXiFPaperLineBundleData to OrigXiFPaperNativeRoot, and
further to SourceSignQuotientData + SourceClauseAssembly (A2 totalization).
Here the exact first A2 field at S1280Arithmetic is isolated as
S1532A2FirstField; given it and its clause assembly, the actual native root T
is constructed, and hence the paper native root for any input whose
arithmetic is S1280Arithmetic.  No fake T/X is constructed. -/
noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000
namespace LeanFormal.IUT.XiFPaper.S1532PaperNativeRootActual
open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.XiFPaper.S1280SourceDefinition31Actual
open LeanFormal.IUT.XiFPaper.S1494NativeArithmeticRootActual
variable {l : PrimeGeFive} {V : Type}
/-- Exact first A2 field at the concrete Gaussian arithmetic: an actual sign
quotient datum. -/
abbrev S1532A2FirstField : Type 1 :=
  SourceSignQuotientData (S1280Arithmetic l)
/-- The second A2 field: the six source clauses over the sign quotient. -/
abbrev S1532A2Assembly (SQ : S1532A2FirstField (l := l)) : Type 1 :=
  SourceClauseAssembly (S1280Arithmetic l) SQ
/-- Given the exact A2 fields, the native root T is actual. -/
noncomputable def nativeRootOfA2 (SQ : S1532A2FirstField (l := l))
    (assembly : S1532A2Assembly SQ) :
    { T : SourceNativeInitialThetaData.{0} l //
        T.arithmetic = S1280Arithmetic l } :=
  ⟨(witnessOfClauseAssembly (S1280Arithmetic l) SQ assembly).sourceData, rfl⟩
/-- The actual native root is the first component of the A2 construction. -/
theorem nativeRootOfA2_arithmetic (SQ : S1532A2FirstField (l := l))
    (assembly : S1532A2Assembly SQ) :
    (nativeRootOfA2 SQ assembly).1.arithmetic = S1280Arithmetic l :=
  (nativeRootOfA2 SQ assembly).2
/-- For a paper input over the concrete Gaussian arithmetic, the A2 fields give
the actual OrigXiFPaperNativeRoot, hence the T of S1494/S1503. -/
theorem paperNativeRoot_of_a2
    (I : OriginalInput.{0, 0, 0, 0, 0} l V)
    (hroot : I.initial.arithmetic = S1280Arithmetic l)
    (SQ : S1532A2FirstField (l := l))
    (assembly : S1532A2Assembly SQ) :
    Nonempty (OrigXiFPaperNativeRoot I) := by
  refine ⟨⟨(nativeRootOfA2 SQ assembly).1, ?_⟩⟩
  rw [nativeRootOfA2_arithmetic, hroot]
-- Exact first missing A2 field, recorded without an inhabitant.
-- S1532A2FirstField = SourceSignQuotientData (S1280Arithmetic l)
-- S1532A2Assembly SQ = SourceClauseAssembly (S1280Arithmetic l) SQ
end LeanFormal.IUT.XiFPaper.S1532PaperNativeRootActual
