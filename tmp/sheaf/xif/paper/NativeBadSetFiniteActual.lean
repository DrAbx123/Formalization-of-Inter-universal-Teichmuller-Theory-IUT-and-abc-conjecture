import tmp.sheaf.n8.closure.NativeBadFintypeClosed
import tmp.sheaf.n8.closure.NativeReductionFieldsActual
import tmp.sheaf.n8.closure.NativeSourceAssembly
import tmp.sheaf.xif.paper.NativeSourceAssemblyActual
import LeanFormal.IUT.IUTI.InitialTheta.SourcePlacePartitionReduction

/-!
# Actual NativeBadSetFinite field

Task-652 constructs the actual badFinite field required by
NativeSourceAssemblyFields, reusing:

* NativeBadFintypeClosed.nativeBadSetFinite: the unconditional-in-source proof
  of X.S.tuple.source.V_mod_bad.Finite, obtained from the finite-good-reduction
  route and NativeLocalReductionDisjointAlt.nativeLocalReductionDisjoint_alt;
* NativeBadFintypeClosed.nativeBadFintype: the actual Fintype on the native bad
  places;
* NativeReductionFieldsActual.NativeBadSetFinite: the exact field type.

The constructed object is the actual field

  badFinite : NativeBadSetFinite X.S.

No arbitrary finiteness/Fintype is chosen; the Fintype is obtained from the
proved Nonempty by Classical.choice inside the existing closed module.  The
remaining NativeSourceAssembly fields (split, torsionGaps, exactSequence,
carrier/cover data, d7, cuspHyp, compatibility proofs) are not constructed
here and remain the exact missing fields from task-643.  No toy/True/PUnit/
axiom/sorry is used.  WRITE-ONLY; compilation is queued.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT.XiFPaper.NativeBadSetFiniteActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.N8Closure.NativeInput
open LeanFormal.IUT.N8Closure.NativeReductionFieldsActual
open LeanFormal.IUT.N8Closure.NativeBadFintypeClosed
open LeanFormal.IUT.N8Closure.C1Actual
open LeanFormal.IUT.XiFPaper.NativeSourceAssemblyActual
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction

universe u

variable {l : PrimeGeFive}
variable (X : N8NativeInput l)

/-- The actual badFinite field: the native bad moduli set is finite, proved from
the existing closed local-disjointness route. -/
theorem nativeBadSetFiniteActual :
    NativeBadSetFinite X.S :=
  nativeBadSetFinite (X := X)

/-- The actual Fintype construction on the native bad places. -/
noncomputable def nativeBadFintypeActual :
    Fintype (Bad (nativePlaceSelection X.S)) :=
  nativeBadFintype (X := X)

/-- The actual nonempty Fintype statement, in the form used by the donor. -/
theorem nativeBadFintypeNonemptyActual :
    Nonempty (Fintype (Bad (nativePlaceSelection X.S))) :=
  nativeBadFintype_nonempty (X := X)

/-- The exact badFinite field in NativeSourceAssemblyFields shape. -/
noncomputable def nativeBadSetFiniteField :
    NativeBadSetFinite X.S :=
  nativeBadSetFiniteActual (X := X)

/-- The badFinite field is the closed native finiteness theorem. -/
theorem nativeBadSetFiniteField_eq :
    nativeBadSetFiniteField (X := X) = nativeBadSetFinite (X := X) := rfl

/-- The field yields the exact Fintype primitive used to build the reduction
clause in NativeSourceAssembly. -/
theorem nativeBadSetFiniteField_fintype :
    Nonempty (Fintype (Bad (nativePlaceSelection X.S))) :=
  (nativeBadFintype_iff_sourceFinite X.S).mpr
    (nativeBadSetFiniteField (X := X))

/-! ## Exact remaining NativeSourceAssembly fields

The badFinite field above is actual.  The following fields of
NativeSourceAssemblyFields are not supplied by this file and remain the exact
missing source data:

* split : NativeSplitMultiplicativeAtLift X.S;
* torsionGaps : NativeSourceTorsionGaps ...;
* exactSequence : SourceExactSequenceClause;
* curve/puncturedCurve/cover/structureGroup and maps;
* cuspCount/cuspCount_pos;
* d7 : NativeD7Intake (SourceCompletion.ofSourceNative X.S);
* cuspHyp : NativeCuspClauseHypotheses;
* redCompat/torCompat/orbCompat/secCompat/cusCompat and proofs.

No other field is hidden in this construction.
-/

end LeanFormal.IUT.XiFPaper.NativeBadSetFiniteActual
