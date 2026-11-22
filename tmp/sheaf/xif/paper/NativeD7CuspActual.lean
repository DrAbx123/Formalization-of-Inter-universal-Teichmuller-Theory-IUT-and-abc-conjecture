import tmp.sheaf.n8.closure.NativeD7Proof
import tmp.sheaf.n8.closure.NativeSourceSectionsCuspActual

/-!
# Native D7 and cusp fields for NativeSourceAssembly

Task-660: construct the fields

  d7 : NativeD7Intake (SourceCompletion.ofSourceNative T)
  cuspHyp : NativeCuspClauseHypotheses

from actual source arithmetic / cusp data, or record the exact missing objects.

Actual data available:
* the native tuple epsilon, an actual geometric
  Iut.OrbicurveBoundaryCusp (not a Real);
* the canonical place-section layer of the native arithmetic input;
* the native SourceCompletion clause records.

Exact obstructions:
1. D7: SourceCompletion clause E does not provide the canonical-layer
   compatibility required by D7LocalGroupSectionSupply. The exact missing
   object is ClauseEToD7Compatibility C.
2. Cusp: NativeCuspClauseHypotheses requires real epsilon/cuspScale data plus
   the native geometric-to-real realization proposition. The native tuple
   epsilon is not a Real, and no cuspScale Real is attached to the native tuple.

This file constructs the actual package conditionally on exactly these objects
and does not fabricate any local group, real coordinate, or compatibility. No
toy/True/PUnit/axiom/sorry is used.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT.XiFPaper
namespace NativeD7CuspActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.Definition31D4D9Supply
open LeanFormal.IUT.InitialThetaSource.NativeSourceSectionsCuspActual

universe u

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)

/-- The actual native completion associated to T. -/
abbrev nativeCompletion : SourceCompletion.{0} l :=
  SourceCompletion.ofSourceNative T

/-- The actual native tuple epsilon: geometric cusp boundary object. -/
def nativeEpsilonGeometric :
    Iut.OrbicurveBoundaryCusp (nativeCompletion T).sourceSignQuotientData.cK :=
  (nativeCompletion T).tuple.epsilon

/-- Exact missing D7 object for the native completion. -/
def MissingNativeD7Object : Prop :=
  Nonempty (ClauseEToD7Compatibility (nativeCompletion T))

/-- Exact missing cusp object: a real epsilon/cuspScale package with the
native geometric-to-real realization. No such package is constructed here. -/
def MissingNativeCuspObject : Prop :=
  Nonempty NativeCuspClauseHypotheses

/-- The exact primitive package needed for the two NativeSourceAssembly fields. -/
structure NativeD7CuspPrimitives where
  d7_compatibility : ClauseEToD7Compatibility (nativeCompletion T)
  cusp_hypotheses : NativeCuspClauseHypotheses

/-- The actual d7 field from the exact Clause E compatibility. -/
noncomputable def nativeD7Field
    (H : ClauseEToD7Compatibility (nativeCompletion T)) :
    NativeD7Intake (nativeCompletion T) :=
  nativeD7IntakeOfCompatibility (nativeCompletion T) H

/-- The actual cuspHyp field from the exact real cusp package. -/
noncomputable def nativeCuspField
    (H : NativeCuspClauseHypotheses) : NativeCuspClauseHypotheses :=
  H

/-- The two exact NativeSourceAssembly fields. -/
structure NativeD7CuspFields where
  d7 : NativeD7Intake (nativeCompletion T)
  cuspHyp : NativeCuspClauseHypotheses

/-- Conditional actual D7/cusp fields from the exact primitives. -/
noncomputable def nativeD7CuspFields
    (P : NativeD7CuspPrimitives T) : NativeD7CuspFields T where
  d7 := nativeD7Field T P.d7_compatibility
  cuspHyp := nativeCuspField P.cusp_hypotheses

/-- The exact primitives are sufficient for the D7/cusp fields. -/
theorem nativeD7CuspFields_nonempty_of_primitives
    (P : NativeD7CuspPrimitives T) : Nonempty (NativeD7CuspFields T) :=
  ⟨nativeD7CuspFields T P⟩

/-- The exact primitive package is equivalent to the D7 compatibility plus a
real cusp package. -/
theorem nativeD7CuspPrimitives_iff :
    Nonempty (NativeD7CuspPrimitives T) ↔
      (Nonempty (ClauseEToD7Compatibility (nativeCompletion T)) ∧
        MissingNativeCuspObject) := by
  constructor
  · rintro ⟨P⟩
    exact ⟨⟨P.d7_compatibility⟩, ⟨P.cusp_hypotheses⟩⟩
  · rintro ⟨⟨H⟩, ⟨C⟩⟩
    exact ⟨{ d7_compatibility := H, cusp_hypotheses := C }⟩

/-- Exact remaining objects, recorded as a named package without asserting an
inhabitant: native D7 compatibility and a real cusp package. -/
def NativeD7CuspMissing : Prop :=
  MissingNativeD7Object (T := T) ∧ MissingNativeCuspObject

end NativeD7CuspActual
end LeanFormal.IUT.XiFPaper
end
