import LeanFormal.IUT.IUTI.InitialTheta.SourceDefinition31Boundary
import tmp.sheaf.xif.paper.NativeCuspCountActualAdapted
import tmp.sheaf.xif.paper.NativeSourceAssemblyActual

/-!
# Source cusp count: actual contract projection and exact native gap

Task-676 searches the actual InitialThetaArithmeticData/curve/cusp data for a
positive Nat cusp count usable by NativeSourceAssembly.

Findings:

* SourceDefinition31Data.orbicurve.cuspCount : Nat and
  SourceDefinition31Data.orbicurve.cuspCount_pos : 0 < cuspCount are actual
  fields of the assembled Definition 3.1 contract
  (SourceDefinition31Boundary.lean:455-456 and cover_cusp_count_pos:757-758).
* The native tuple carries only the geometric cusp
  T.tuple.source.epsilon : Iut.OrbicurveBoundaryCusp ...; it does not carry a Nat
  cusp count.  No native declaration converts the geometric cusp to a positive
  Nat.
* NativeSourceAssembly.cuspCount/cuspCount_pos are independent fields; they are
  not produced by the native X.S data.  The exact missing object is a positive
  natural source cusp count, not the geometric cusp coordinate.

This file constructs the actual count projection from a SourceDefinition31Data
contract, and records the exact missing native count object.  No arbitrary
count/True/PUnit/axiom/sorry.  WRITE-ONLY; compilation queued.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT.XiFPaper.SourceCuspCountActualAdapted

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.N8Closure.NativeInput
open LeanFormal.IUT.XiFPaper.NativeCuspCountActualAdapted
open LeanFormal.IUT.XiFPaper.NativeSourceAssemblyActual

universe ua uv upi umon ui

variable {l : PrimeGeFive}
variable (S : SourceDefinition31Data l)
variable (T : SourceNativeInitialThetaData.{0} l)

/-- The actual positive Nat cusp count of the assembled Definition 3.1 contract. -/
def sourceCuspCount : Nat :=
  S.orbicurve.cuspCount

/-- The actual positivity proof for the assembled source cusp count. -/
theorem sourceCuspCount_pos : 0 < sourceCuspCount (S := S) :=
  S.orbicurve.cuspCount_pos

/-- The contract cusp count is exactly the orbi-curve cuspCount field. -/
theorem sourceCuspCount_eq : sourceCuspCount (S := S) = S.orbicurve.cuspCount := rfl

/-- The source contract cusp count is a positive Nat, as required by the
NativeSourceAssembly field shape. -/
theorem sourceCuspCount_positive_field :
    0 < sourceCuspCount (S := S) :=
  sourceCuspCount_pos S

/-! ## Exact missing native count -/

/-- Exact missing object for the native assembly: a positive Nat cusp count in
the native-tuple direction.  The assembled contract supplies one only after a
SourceDefinition31Data contract exists; the native tuple does not. -/
structure MissingNativeCuspCountObject where
  cuspCount : Nat
  cuspCount_pos : 0 < cuspCount

/-- The missing native count object, as a proposition. -/
def MissingNativeCuspCountProp : Prop :=
  Nonempty MissingNativeCuspCountObject

/-- The missing native count is exactly the conditional Nat/positivity object. -/
theorem missingNativeCuspCountProp_iff :
    MissingNativeCuspCountProp ↔
      Nonempty MissingNativeCuspCountObject := Iff.rfl

/-- Actual contract projection is available but is not a native X.S count. -/
theorem sourceCuspCountActualStatus :
    sourceCuspCount (S := S) = S.orbicurve.cuspCount ∧
      0 < sourceCuspCount (S := S) :=
  ⟨sourceCuspCount_eq S, sourceCuspCount_pos S⟩

end LeanFormal.IUT.XiFPaper.SourceCuspCountActualAdapted
