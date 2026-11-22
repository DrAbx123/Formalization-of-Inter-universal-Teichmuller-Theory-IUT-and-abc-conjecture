import tmp.sheaf.xif.paper.NativeSourceAssemblyActual
import tmp.sheaf.n8.closure.NativeSourceSectionsCuspActual
import LeanFormal.IUT.IUTI.InitialTheta.SourceDefinition31Boundary
import LeanFormal.IUT.IUTI.InitialTheta.SourceCompletion

/-!
# Actual cuspCount / cuspCount_pos construction attempt

Task-669 attempts the NativeSourceAssembly fields

  cuspCount : Nat
  cuspCount_pos : 0 < cuspCount

from the actual source curve/cusp/OrbicurveBoundaryCusp data.

Actual data available:

* the native tuple carries a geometric cusp
  T.tuple.source.epsilon : Iut.OrbicurveBoundaryCusp T.tuple.source.cK
  (NativeSourceSectionsCuspActual.nativeTupleEpsilon);
* the Definition 3.1 contract type SourceCuspClause has cuspCount/cuspCount_pos,
  and SourceDefinition31Data supplies them only after the contract is assembled;
* NativeSourceAssembly itself has cuspCount/cuspCount_pos as fields, not derived
  from the tuple epsilon.

No source declaration converts an OrbicurveBoundaryCusp (geometric cusp
coordinate) into a positive Nat cusp count.  Such a count is an additional
source card.  This file therefore constructs the exact conditional field
package and reports the missing source object; it does not choose a count.

No arbitrary count/True/PUnit/axiom/sorry.  WRITE-ONLY; compilation queued.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT.XiFPaper.NativeCuspCountActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.NativeSourceSectionsCuspActual
open LeanFormal.IUT.XiFPaper.NativeSourceAssemblyActual

universe u

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)

/-- The exact missing source object: a positive natural cusp count. -/
structure NativeCuspCountSource where
  cuspCount : Nat
  cuspCount_pos : 0 < cuspCount

/-- The conditional count read out of the exact source object. -/
def NativeCuspCountSource.countValue (C : NativeCuspCountSource T) : Nat :=
  C.cuspCount

/-- The conditional positivity of the source count. -/
theorem NativeCuspCountSource.countValue_pos
    (C : NativeCuspCountSource T) : 0 < C.countValue :=
  C.cuspCount_pos

/-- Replace the cuspCount/cuspCount_pos fields of the conditional assembly
package by an explicit source count.  All other fields remain the supplied
actual conditional assembly fields. -/
noncomputable def withCuspCount
    (F : NativeSourceAssemblyFields T) (C : NativeCuspCountSource T) :
    NativeSourceAssemblyFields T :=
  { F with
    cuspCount := C.cuspCount
    cuspCount_pos := C.cuspCount_pos }

/-- The resulting cusp count is exactly the supplied source count. -/
theorem withCuspCount_cuspCount
    (F : NativeSourceAssemblyFields T) (C : NativeCuspCountSource T) :
    (withCuspCount (l := l) T F C).cuspCount = C.cuspCount := rfl

/-- The resulting positivity is exactly the supplied source proof. -/
theorem withCuspCount_cuspCount_pos
    (F : NativeSourceAssemblyFields T) (C : NativeCuspCountSource T) :
    (withCuspCount (l := l) T F C).cuspCount_pos =
      C.cuspCount_pos := rfl

/-- Exact missing source object, as a proposition. -/
def MissingNativeCuspCount : Prop :=
  Nonempty (NativeCuspCountSource T)

/-- The missing count is exactly the conditional source package. -/
theorem missingNativeCuspCount_iff :
    MissingNativeCuspCount (l := l) T ↔
      Nonempty (NativeCuspCountSource T) := Iff.rfl

/-- The actual geometric cusp coordinate is available; it is not a Nat count. -/
noncomputable def nativeGeometricCusp :
    Iut.OrbicurveBoundaryCusp
      (SourceCompletion.ofSourceNative T).sourceSignQuotientData.cK :=
  nativeTupleEpsilon (SourceCompletion.ofSourceNative T)

end LeanFormal.IUT.XiFPaper.NativeCuspCountActual
