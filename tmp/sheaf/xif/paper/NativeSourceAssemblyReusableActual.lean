import tmp.sheaf.xif.paper.NativeSourceAssemblyPartial
import tmp.sheaf.xif.paper.NativeSourceAssemblyFieldsActual
import tmp.sheaf.xif.paper.NativeAssemblySplitIntegration
import tmp.sheaf.xif.paper.NativeD7CuspActual
import tmp.sheaf.xif.paper.NativeCuspCountActual
import tmp.sheaf.xif.paper.ExactSequenceSplittingActual
import tmp.sheaf.xif.paper.NativeTorsionGapsActual

/-!
# Reusable NativeSourceAssembly fields and exact missing fields

The actual reusable part is already constructed:

* badFinite (NativeBadSetFiniteActual);
* curve/puncturedCurve/cover/structureGroup and point maps;
* five compatibility fields;
* torsion carrier and rank-two basis;
* clause-D exact sequence injection/projection/exactness data;
* the native geometric cusp coordinate.

The remaining fields are exactly:

* split (canonical Tate criterion);
* torsionGaps (torsionLabel, six-torsion independence, l-torsion compatibility);
* exactSequence splitting section;
* cuspCount/cuspCount_pos;
* d7 (Clause E -> D7 compatibility);
* cuspHyp (real cusp package).

This file assembles every actual field and gives the exact conditional constructor
from the missing package.  No missing field is fabricated.
-/

set_option relaxedAutoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 1000000

noncomputable section

namespace LeanFormal.IUT.XiFPaper.NativeSourceAssemblyReusableActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.N8Closure.NativeInput
open LeanFormal.IUT.XiFPaper.NativeSourceAssemblyPartial
open LeanFormal.IUT.XiFPaper.NativeSourceAssemblyActual
open LeanFormal.IUT.XiFPaper.NativeSourceAssemblyFieldsActual
open LeanFormal.IUT.XiFPaper.NativeAssemblySplitIntegration
open LeanFormal.IUT.XiFPaper.NativeD7CuspActual
open LeanFormal.IUT.XiFPaper.NativeCuspCountActual
open LeanFormal.IUT.InitialThetaSource.ExactSequenceSplittingActual
open LeanFormal.IUT.InitialThetaSource.NativeSourceTorsion

universe u

variable {l : PrimeGeFive}
variable (X : N8NativeInput l)

/-- Actual reusable part of NativeSourceAssembly. -/
structure ReusableNativeSourceFields where
  part : ActualNativeAssemblyPart (l := l) X
  exactSequenceData : ActualExactSequenceData (l := l) X.S
  geometricCusp : Iut.OrbicurveBoundaryCusp
    (SourceCompletion.ofSourceNative X.S).sourceSignQuotientData.cK

/-- The actual reusable fields, constructed without missing data. -/
noncomputable def reusableNativeSourceFields :
    ReusableNativeSourceFields (l := l) X where
  part := actualNativeAssemblyPart (l := l) X
  exactSequenceData := actualExactSequenceData (l := l) X.S
  geometricCusp := nativeGeometricCusp (l := l) X.S

/-- Exact remaining fields for NativeSourceAssembly. -/
structure MissingNativeSourceAssemblyFields where
  splitCriterion : MissingCanonicalTateSplitCriterion (l := l) X
  torsionGaps : NativeSourceTorsionGaps (A := X.S.arithmetic)
    (S := X.S.tuple.source) (C := X.S.clauseA) (B := X.S.clauseB) X.S.clauseC
  section : ExactSequenceSplittingSection (l := l) X.S
  cuspCount : Nat
  cuspCount_pos : 0 < cuspCount
  d7CuspPrimitives : NativeD7CuspPrimitives (l := l) X.S

/-- Assemble all actual reusable fields plus the exact missing fields into the
full NativeSourceAssemblyFields package. -/
noncomputable def nativeSourceAssemblyFieldsOfParts
    (R : ReusableNativeSourceFields (l := l) X)
    (M : MissingNativeSourceAssemblyFields (l := l) X) :
    NativeSourceAssemblyFields X.S where
  badFinite := R.part.badFinite
  split := splitFieldOfCanonicalCriterion (l := l) X M.splitCriterion
  torsionGaps := M.torsionGaps
  exactSequence := sourceExactSequence_of_section (l := l) X.S M.section
  curve := R.part.carriers.curve
  puncturedCurve := R.part.carriers.puncturedCurve
  cover := R.part.carriers.cover
  structureGroup := R.part.carriers.structureGroup
  structureGroupLaw := R.part.carriers.structureGroupLaw
  curveToPunctured := R.part.carriers.curveToPunctured
  coverToPunctured := R.part.carriers.coverToPunctured
  cover_surjective := R.part.carriers.cover_surjective
  cuspCount := M.cuspCount
  cuspCount_pos := M.cuspCount_pos
  d7 := nativeD7Field (l := l) X.S M.d7CuspPrimitives.d7_compatibility
  cuspHyp := M.d7CuspPrimitives.cusp_hypotheses
  redCompat := R.part.compat.redCompat
  redCompat_proved := R.part.compat.redCompat_proved
  torCompat := R.part.compat.torCompat
  torCompat_proved := R.part.compat.torCompat_proved
  orbCompat := R.part.compat.orbCompat
  orbCompat_proved := R.part.compat.orbCompat_proved
  secCompat := R.part.compat.secCompat
  secCompat_proved := R.part.compat.secCompat_proved
  cusCompat := R.part.compat.cusCompat
  cusCompat_proved := R.part.compat.cusCompat_proved

/-- The exact missing field package is sufficient to close the full assembly. -/
theorem nativeSourceAssemblyFields_nonempty_of_missing
    (M : MissingNativeSourceAssemblyFields (l := l) X) :
    Nonempty (NativeSourceAssemblyFields X.S) :=
  ⟨nativeSourceAssemblyFieldsOfParts (l := l) X
    (reusableNativeSourceFields (l := l) X) M⟩

/-- Exact remaining gap proposition. -/
def NativeSourceAssemblyExactGap : Prop :=
  Nonempty (MissingNativeSourceAssemblyFields (l := l) X)

/-- The exact gap is exactly the missing package above. -/
theorem nativeSourceAssemblyExactGap_iff :
    NativeSourceAssemblyExactGap (l := l) X ↔
      Nonempty (MissingNativeSourceAssemblyFields (l := l) X) :=
  Iff.rfl

end LeanFormal.IUT.XiFPaper.NativeSourceAssemblyReusableActual

end
