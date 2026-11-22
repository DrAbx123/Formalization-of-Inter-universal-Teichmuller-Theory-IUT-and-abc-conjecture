import tmp.sheaf.n8.closure.NativeSourceAssembly
import tmp.sheaf.n8.closure.NativeReductionFieldsActual
import tmp.sheaf.n8.closure.NativeSourceTorsionActual
import tmp.sheaf.n8.closure.NativeSourceOrbicurveActual
import tmp.sheaf.n8.closure.NativeSourceSectionsCuspActual
import tmp.sheaf.n8.closure.NativeD7Proof

/-!
# NativeSourceAssembly from X.S: construction attempt and exact gaps

Task-643 tries to construct NativeSourceAssembly X.S (and hence the
SourceDefinition31Data donor) from the actual native root X.S.

The structure NativeSourceAssembly (NativeSourceAssembly.lean:44-70) has exactly
these fields:

  badFinite : NativeBadSetFinite T
  split : NativeSplitMultiplicativeAtLift T
  torsionGaps : NativeSourceTorsionGaps ... T.clauseC
  exactSequence : SourceExactSequenceClause
  curve, puncturedCurve, cover, structureGroup : Type
  [structureGroupLaw : Group structureGroup]
  curveToPunctured : puncturedCurve -> curve
  coverToPunctured : cover -> puncturedCurve
  cover_surjective : Function.Surjective coverToPunctured
  cuspCount : Nat
  cuspCount_pos : 0 < cuspCount
  d7 : NativeD7Intake (SourceCompletion.ofSourceNative T)
  cuspHyp : NativeCuspClauseHypotheses
  redCompat/torCompat/orbCompat/secCompat/cusCompat : Prop
  their five _proved fields.

Actual source data supplies the native T and its clause records, but no
production declaration constructs this package.  The exact missing fields are:

1. badFinite: NativeBadSetFinite T = T.tuple.source.V_mod_bad.Finite;
   no Fintype/Set.Finite proof for the native bad set (task-521/618).
2. split: NativeSplitMultiplicativeAtLift T; missing canonical Tate split
   primitive at the actual q (NativeSplitProof).
3. torsionGaps: NativeSourceTorsionGaps; missing torsionLabel, six-torsion
   independence, and l-torsion compatibility (task-533).
4. exactSequence: SourceExactSequenceClause; sourceExactSequenceOfGroups needs
   the actual profinite sequence plus a splitting section baseGroup ->*
   coverGroup; the section and point-set carriers are not in the native tuple.
5. curve/puncturedCurve/cover/structureGroup and the two point maps: native
   clause records carry orbicurve/group data, not these point-set carriers.
6. d7: NativeD7Intake (SourceCompletion.ofSourceNative T); NativeD7Proof shows
   no unconditional D7 local-group section supply is constructed.
7. cuspHyp: NativeCuspClauseHypotheses requires a real cusp coordinate and
   cuspScale plus the missing native epsilon realization; the native epsilon is
   an OrbicurveBoundaryCusp, not a Real.
8. redCompat/torCompat/orbCompat/secCompat/cusCompat and their proofs: the
   compatibility clauses are not simultaneously proved from X.S alone.

This file provides the exact conditional object constructor from the missing
field package.  No field is fabricated; no arbitrary data/True/PUnit/axiom/sorry
is used.  WRITE-ONLY; compilation queued.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT.XiFPaper.NativeSourceAssemblyActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.N8Closure.C1Actual
open LeanFormal.IUT.N8Closure.NativeReductionFieldsActual
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.InitialThetaSource.NativeSourceTorsion
open LeanFormal.IUT.InitialThetaSource.NativeSourceOrbicurveActual
open LeanFormal.IUT.InitialThetaSource.NativeSourceSectionsCuspActual

universe u

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)

/-- Exact conditional donor fields for NativeSourceAssembly.  Every field is the
actual source datum required by the frozen structure; none is manufactured. -/
structure NativeSourceAssemblyFields
    (T : SourceNativeInitialThetaData.{0} l) where
  badFinite : NativeBadSetFinite T
  split : NativeSplitMultiplicativeAtLift T
  torsionGaps : NativeSourceTorsionGaps (A := T.arithmetic)
    (S := T.tuple.source) (C := T.clauseA) (B := T.clauseB) T.clauseC
  exactSequence : SourceExactSequenceClause
  curve : Type
  puncturedCurve : Type
  cover : Type
  structureGroup : Type
  [structureGroupLaw : Group structureGroup]
  curveToPunctured : puncturedCurve -> curve
  coverToPunctured : cover -> puncturedCurve
  cover_surjective : Function.Surjective coverToPunctured
  cuspCount : Nat
  cuspCount_pos : 0 < cuspCount
  d7 : NativeD7Intake (SourceCompletion.ofSourceNative T)
  cuspHyp : NativeCuspClauseHypotheses
  redCompat : Prop
  redCompat_proved : redCompat
  torCompat : Prop
  torCompat_proved : torCompat
  orbCompat : Prop
  orbCompat_proved : orbCompat
  secCompat : Prop
  secCompat_proved : secCompat
  cusCompat : Prop
  cusCompat_proved : cusCompat

namespace NativeSourceAssemblyFields

variable {T : SourceNativeInitialThetaData.{0} l}
variable (M : NativeSourceAssemblyFields T)

/-- The actual NativeSourceAssembly constructed from the exact conditional
field package.  This is an object constructor, not an existence proof. -/
noncomputable def toAssembly : NativeSourceAssembly T where
  badFinite := M.badFinite
  split := M.split
  torsionGaps := M.torsionGaps
  exactSequence := M.exactSequence
  curve := M.curve
  puncturedCurve := M.puncturedCurve
  cover := M.cover
  structureGroup := M.structureGroup
  structureGroupLaw := M.structureGroupLaw
  curveToPunctured := M.curveToPunctured
  coverToPunctured := M.coverToPunctured
  cover_surjective := M.cover_surjective
  cuspCount := M.cuspCount
  cuspCount_pos := M.cuspCount_pos
  d7 := M.d7
  cuspHyp := M.cuspHyp
  redCompat := M.redCompat
  redCompat_proved := M.redCompat_proved
  torCompat := M.torCompat
  torCompat_proved := M.torCompat_proved
  orbCompat := M.orbCompat
  orbCompat_proved := M.orbCompat_proved
  secCompat := M.secCompat
  secCompat_proved := M.secCompat_proved
  cusCompat := M.cusCompat
  cusCompat_proved := M.cusCompat_proved

end NativeSourceAssemblyFields

/-- The exact missing assembly package for T = X.S. -/
def MissingNativeSourceAssembly
    (T : SourceNativeInitialThetaData.{0} l) : Prop :=
  Nonempty (NativeSourceAssemblyFields T)

/-- The missing field package is exactly the object needed to construct the
frozen NativeSourceAssembly. -/
theorem missingNativeSourceAssembly_iff :
    MissingNativeSourceAssembly (l := l) T ↔
      Nonempty (NativeSourceAssemblyFields T) := Iff.rfl

/-- A conditional actual NativeSourceAssembly from the exact field package. -/
noncomputable def nativeSourceAssemblyOfFields
    {T : SourceNativeInitialThetaData.{0} l}
    (M : NativeSourceAssemblyFields T) : NativeSourceAssembly T :=
  M.toAssembly

end LeanFormal.IUT.XiFPaper.NativeSourceAssemblyActual
