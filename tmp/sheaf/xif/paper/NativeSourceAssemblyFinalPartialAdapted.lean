import tmp.sheaf.xif.paper.NativeSourceAssemblyPartialAdapted

/-!
# Final conditional NativeSourceAssembly integration

Integrates the actual partial NativeSourceAssembly (badFinite, carriers,
torsion partial, five compatibility fields) with the exact missing fields
split, torsionGaps, exact-sequence splitting section, cuspCount/positivity,
d7, and cuspHyp. The full NativeSourceAssembly X.S and its SourceDefinition31Data
consumer are constructed only from those fields. No new axiom; integration
only. WRITE-ONLY: no lake.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT.XiFPaper.NativeSourceAssemblyFinalPartialAdapted

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.N8Closure.NativeInput
open LeanFormal.IUT.N8Closure.NativeReductionFieldsActual
open LeanFormal.IUT.XiFPaper.NativeSourceAssemblyPartialAdapted

universe u

variable {l : PrimeGeFive}
variable (X : N8NativeInput l)

/-- The exact missing final-assembly field package. -/
abbrev MissingFinalAssemblyFields := NativeSourceAssemblyMissingFields (l := l) X

/-- Full NativeSourceAssembly from the actual part and the exact missing
/-- fields. This is the final conditional integration. -/
noncomputable def finalNativeSourceAssembly
    (M : MissingFinalAssemblyFields (l := l) X) :
    NativeSourceAssembly X.S :=
  nativeSourceAssemblyOfMissing (l := l) X M

/-- The SourceDefinition31Data consumer of the conditionally assembled
/-- NativeSourceAssembly. -/
noncomputable def finalSourceDefinition31Data
    (M : MissingFinalAssemblyFields (l := l) X) :
    SourceDefinition31Data.{0} l :=
  (finalNativeSourceAssembly (l := l) X M).toSourceData

/-- Exact missing final fields: the full missing field package. -/
def ExactMissingFinalFields : Prop :=
  Nonempty (MissingFinalAssemblyFields (l := l) X)

#check MissingFinalAssemblyFields
#check finalNativeSourceAssembly
#check finalSourceDefinition31Data
#check NativeSourceAssembly.toSourceData
#check ExactMissingFinalFields

end LeanFormal.IUT.XiFPaper.NativeSourceAssemblyFinalPartialAdapted

end
