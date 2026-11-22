import tmp.sheaf.n8.closure.EtaBadFiniteSourceActual
import tmp.sheaf.n8.closure.EtaNativeDefinition31ObjectsAssembly

set_option maxHeartbeats 1200000
set_option relaxedAutoImplicit false

/-!
# Source qualification condition for bad finiteness

`RequiredBadFiniteness X` (i.e. `Set.Finite X.S.tuple.source.V_mod_bad`) is not
derivable from the current native fields.  This file makes it an explicit
SOURCE QUALIFICATION field of the corrected Definition 3.1 target.  It is a
source condition, not an arbitrary finite witness: no `Fintype` or `Finite`
instance is chosen and no `Nonempty` is assumed as a theorem.  The corrected
target is exactly the previous assembly target with this qualification named.
-/

noncomputable section

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.N8Closure.NativeInput
open LeanFormal.IUT.N8Closure.NativeContractFieldsActualAttempt
open LeanFormal.IUT.N8Closure.NativeBadFintypeSourceAttempt
open LeanFormal.IUT.N8Closure.NativeBadFiniteTargetCorrection
open LeanFormal.IUT.N8Closure.NativeReductionRestActual
open LeanFormal.IUT.N8Closure.EtaBadFiniteSourceActual
open LeanFormal.IUT.N8Closure.EtaNativeDefinition31ObjectsAssembly

namespace LeanFormal.IUT.N8Closure.EtaSourceWithBadFiniteCondition

universe u

variable {l : PrimeGeFive} (X : N8NativeInput l)

/-- Corrected Definition 3.1 input: the source qualification (bad-set
finiteness) plus the exact remaining reduction/source-clause inputs. -/
structure SourceQualifiedDefinition31Input (X : N8NativeInput l) where
  /-- Explicit SOURCE qualification: `V_mod_bad` is finite. -/
  qualification : RequiredBadFiniteness (X := X)
  /-- Exact remaining reduction/q inputs. -/
  reductionRest : NativeReductionRestRemaining X
  /-- Exact remaining full-clause targets. -/
  remaining : NativeDefinition31RemainingTargets X

/-- Corrected Definition 3.1 target.  This is a target/source-condition
package, not a construction of an arbitrary finite witness. -/
def CorrectedDefinition31Target : Prop :=
  Nonempty (SourceQualifiedDefinition31Input (l := l) X)

/-- Actual projection: the corrected target carries the source finiteness
condition explicitly. -/
theorem correctedTarget_source_condition
    (h : CorrectedDefinition31Target (X := X)) :
    RequiredBadFiniteness (X := X) :=
  h.some.qualification

/-- Actual corrected input to the previous assembly input, using the source
qualification to build the corrected bad-finite card (not an arbitrary
witness). -/
noncomputable def assemblyInputsOfCorrected
    (I : SourceQualifiedDefinition31Input (X := X)) :
    NativeDefinition31AssemblyInputs (X := X) where
  badFinite := nativeSourceWithBadFiniteOfSetFinite X I.qualification
  reductionRest := I.reductionRest
  remaining := I.remaining

/-- Actual converse: the previous assembly input yields the corrected input
with the source condition exposed. -/
noncomputable def correctedInputOfAssembly
    (A : NativeDefinition31AssemblyInputs (X := X)) :
    SourceQualifiedDefinition31Input (X := X) where
  qualification := A.badFinite.badFinite
  reductionRest := A.reductionRest
  remaining := A.remaining

/-- Actual equivalence with the previous assembly target. -/
theorem correctedTarget_iff_assemblyInputs :
    CorrectedDefinition31Target (X := X) ↔
      Nonempty (NativeDefinition31AssemblyInputs (X := X)) := by
  constructor
  · rintro ⟨I⟩
    exact ⟨assemblyInputsOfCorrected (X := X) I⟩
  · rintro ⟨A⟩
    exact ⟨correctedInputOfAssembly (X := X) A⟩

/-- Downstream consumer check: the actual reduction clause consumes the
corrected input. -/
noncomputable def reductionClauseOfCorrected
    (I : SourceQualifiedDefinition31Input (X := X)) :
    SourceReductionClause (NativeSelectedPlaces X) (NativeBadPlaces X) :=
  nativeReductionClauseOf X
    (nativeSourceWithBadFiniteOfSetFinite X I.qualification)
    I.reductionRest

/-- The correction does not add a theorem asserting the source condition; it
records the condition as a field of the target package. -/
theorem correctedTarget_is_source_condition_not_witness
    (h : CorrectedDefinition31Target (X := X)) :
    RequiredBadFiniteness (X := X) := h.some.qualification

end LeanFormal.IUT.N8Closure.EtaSourceWithBadFiniteCondition

end
