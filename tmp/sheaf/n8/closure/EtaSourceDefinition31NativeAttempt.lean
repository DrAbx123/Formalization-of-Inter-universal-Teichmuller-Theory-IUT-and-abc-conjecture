import tmp.sheaf.n8.closure.C10BridgeProof
import LeanFormal.IUT.IUTI.InitialTheta.SourceDefinition31Boundary
import LeanFormal.IUT.IUTI.InitialTheta.SourceDefinition31Quantifiers

set_option maxHeartbeats 1200000
set_option relaxedAutoImplicit false

/-!
# Native SourceDefinition31Data attempt

NativeLocalShell carries the actual SourceNativeInitialThetaData (arithmetic and
clauses A-F).  SourceDefinition31Data additionally needs the reduction clause,
torsion, orbicurve, sections, cusp, and their compatibility props.  Those source
objects are not present in N8NativeInput; this file records the exact donor
interface and the exact gap.  No arbitrary SourceDefinition31Data is chosen.
-/

noncomputable section

open MeasureTheory BigOperators
open LeanFormal.IUT
open LeanFormal.IUT.N8Closure.NativeInput
open LeanFormal.IUT.N8Closure.C10BridgeProof
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.InitialThetaSource

namespace LeanFormal.IUT.N8Closure.EtaSourceDefinition31NativeAttempt

universe u

variable {l : PrimeGeFive} (X : N8NativeInput l)

/-- Actual arithmetic root from native data. -/
abbrev nativeArithmetic : InitialThetaArithmeticData l :=
  X.S.arithmetic

/-- Actual Clause A from native data. -/
abbrev nativeClauseA : SourceClauseA X.S.arithmetic X.S.tuple.source :=
  X.S.clauseA

/-- Actual Clause B from native data. -/
abbrev nativeClauseB :
    SourceClauseB X.S.arithmetic X.S.tuple.source X.S.clauseA :=
  X.S.clauseB

/-- Actual Clause C from native data. -/
abbrev nativeClauseC :
    SourceClauseC X.S.arithmetic X.S.tuple.source X.S.clauseA X.S.clauseB :=
  X.S.clauseC

/-- Actual Clause D from native data. -/
abbrev nativeClauseD :
    SourceClauseD X.S.arithmetic X.S.tuple.source X.S.clauseA X.S.clauseB X.S.clauseC :=
  X.S.clauseD

/-- Exact donor interface for the missing SourceDefinition31Data fields. -/
structure NativeDefinition31Objects (X : N8NativeInput l) where
  selectedPlaces : Type
  badPlaces : Type
  reduction : SourceReductionClause selectedPlaces badPlaces
  torsion : SourceTorsionClause l
  orbicurve : SourceOrbicurveClause
  sections : SourceSectionClause
  cusp : SourceCuspClause
  arithmetic_reduction_compatibility : Prop
  arithmetic_reduction_compatibility_proved :
    arithmetic_reduction_compatibility
  arithmetic_torsion_compatibility : Prop
  arithmetic_torsion_compatibility_proved :
    arithmetic_torsion_compatibility
  arithmetic_orbicurve_compatibility : Prop
  arithmetic_orbicurve_compatibility_proved :
    arithmetic_orbicurve_compatibility
  arithmetic_section_compatibility : Prop
  arithmetic_section_compatibility_proved :
    arithmetic_section_compatibility
  arithmetic_cusp_compatibility : Prop
  arithmetic_cusp_compatibility_proved :
    arithmetic_cusp_compatibility

/-- Assemble SourceDefinition31Data from native arithmetic/clauses A-D and the
exact missing source objects. -/
noncomputable def sourceDefinition31DataOfNativeObjects
    (D : NativeDefinition31Objects (l := l) X) :
    SourceDefinition31Data.{0} l where
  arithmetic := X.S.arithmetic
  selectedPlaces := D.selectedPlaces
  badPlaces := D.badPlaces
  reduction := D.reduction
  torsion := D.torsion
  orbicurve := D.orbicurve
  sections := D.sections
  cusp := D.cusp
  arithmetic_reduction_compatibility := D.arithmetic_reduction_compatibility
  arithmetic_reduction_compatibility_proved :=
    D.arithmetic_reduction_compatibility_proved
  arithmetic_torsion_compatibility := D.arithmetic_torsion_compatibility
  arithmetic_torsion_compatibility_proved :=
    D.arithmetic_torsion_compatibility_proved
  arithmetic_orbicurve_compatibility := D.arithmetic_orbicurve_compatibility
  arithmetic_orbicurve_compatibility_proved :=
    D.arithmetic_orbicurve_compatibility_proved
  arithmetic_section_compatibility := D.arithmetic_section_compatibility
  arithmetic_section_compatibility_proved :=
    D.arithmetic_section_compatibility_proved
  arithmetic_cusp_compatibility := D.arithmetic_cusp_compatibility
  arithmetic_cusp_compatibility_proved :=
    D.arithmetic_cusp_compatibility_proved

theorem sourceDefinition31DataOfNativeObjects_arithmetic
    (D : NativeDefinition31Objects (l := l) X) :
    (sourceDefinition31DataOfNativeObjects (X := X) D).arithmetic =
      X.S.arithmetic := rfl

/-- Exact gap: no actual package of the missing source objects is supplied by
the native N8 input. -/
def NativeDefinition31ConstructionTarget : Prop :=
  Nonempty (NativeDefinition31Objects (l := l) X)

end LeanFormal.IUT.N8Closure.EtaSourceDefinition31NativeAttempt

end