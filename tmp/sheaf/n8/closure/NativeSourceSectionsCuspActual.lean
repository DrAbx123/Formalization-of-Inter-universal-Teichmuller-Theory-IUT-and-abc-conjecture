import LeanFormal.IUT.IUTI.InitialTheta.SourceCompletion
import LeanFormal.IUT.IUTI.InitialTheta.SourceDefinition31D4D9Supply
import LeanFormal.IUT.IUTI.InitialTheta.SourceDefinition31LocalValuationSections
import LeanFormal.IUT.IUTI.InitialTheta.SourceDefinition31Boundary

/-! # Native `SourceSectionClause` and `SourceCuspClause`

This file builds the Definition 3.1(e)/(f) boundary clauses from native
source data where possible, and isolates the exact type obstruction for the
cusp clause.

## Native data used

* `C : SourceCompletion l` is the native completed source record.  It carries
  the native clauses `C.clauseA` ... `C.clauseF`, the native tuple
  `C.tuple`, and the native tuple epsilon `C.tuple.epsilon`.
* `C.tuple.epsilon : Iut.OrbicurveBoundaryCusp C.sourceSignQuotientData.cK`
  is the actual native cusp boundary object.
* `SourceValuationSectionLayer.canonical C.arithmetic` is the actual
  canonical place-section layer for the native arithmetic input.

## Section clause (actual construction, conditional on the D7 local-group intake)

`d7SectionLayerBridge` (Definition31D4D9Supply) constructs a
`SourceSectionClause` from the canonical place-section layer plus the
explicit D7 local-group supply.  The place half is actual; the local-group
half is the exact missing intake `D7LocalGroupSectionSupply`
(Definition 3.1(e), lines 3220-3272).  No local groups are invented.

## Cusp clause (exact obstruction)

`SourceCuspClause` requires

    epsilon : Real,  cuspScale : Real,

with positivity/nonzero/compatibility data.  The native tuple epsilon is an
`Iut.OrbicurveBoundaryCusp`, a geometric compactification boundary point, not
a real number.  There is no map `OrbicurveBoundaryCusp -> Real` in the tree,
and no `cuspScale : Real` attached to the native tuple.  Therefore the cusp
clause cannot be constructed from the native tuple epsilon alone.  The existing
constructors in `SourceClauseConstructors.lean` (`ofCanonicalBoundaryData`,
`boundaryOriginFromKBasis`, `ofCanonicalKBoundaryOrigin`) build a
`SourceClauseF`, not the real-valued boundary `SourceCuspClause`, so they do
not discharge this target.  The file
provides the exact explicit hypothesis package `NativeCuspClauseHypotheses`
and a conditional constructor; it does NOT choose arbitrary reals.

No `PUnit`, `True`, `sorry`, or axiom is used; no fake maps are introduced.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT
namespace InitialThetaSource
namespace NativeSourceSectionsCuspActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.Definition31D4D9Supply

variable {l : PrimeGeFive}

/-- The native tuple epsilon: the actual geometric cusp boundary object of the
native tuple. This is the object whose type blocks the real-valued
`SourceCuspClause` construction. -/
def nativeTupleEpsilon (C : SourceCompletion.{0} l) :
    Iut.OrbicurveBoundaryCusp C.sourceSignQuotientData.cK :=
  C.tuple.epsilon

theorem nativeTupleEpsilon_eq (C : SourceCompletion.{0} l) :
    nativeTupleEpsilon C = C.tuple.epsilon := rfl

/-- The native tuple epsilon is not a real number: its type is the geometric
`OrbicurveBoundaryCusp`, so no `SourceCuspClause.epsilon : Real` can be read
off it without an additional realization. -/
example (C : SourceCompletion.{0} l) :
    Iut.OrbicurveBoundaryCusp C.sourceSignQuotientData.cK :=
  nativeTupleEpsilon C

/-- The D7 local-group intake: the exact missing half of Definition 3.1(e). -/
abbrev NativeD7Intake (C : SourceCompletion.{0} l) : Type 1 :=
  D7LocalGroupSectionSupply.{0, 0}
    (SourceValuationSectionLayer.canonical C.arithmetic)

/-- Actual native section clause from the canonical place-section layer and
the explicit D7 local-group intake. No local group is fabricated here. -/
def nativeSectionClause (C : SourceCompletion.{0} l)
    (G : NativeD7Intake C) : Theorem311Source.SourceSectionClause :=
  d7SectionLayerBridge (SourceValuationSectionLayer.canonical C.arithmetic) G

theorem nativeSectionClause_valuationCarrier (C : SourceCompletion.{0} l)
    (G : NativeD7Intake C) :
    (nativeSectionClause C G).valuationCarrier =
      (SourceValuationSectionLayer.canonical C.arithmetic).valuationCarrier :=
  rfl

theorem nativeSectionClause_modifiedValuationCarrier (C : SourceCompletion.{0} l)
    (G : NativeD7Intake C) :
    (nativeSectionClause C G).modifiedValuationCarrier =
      (SourceValuationSectionLayer.canonical C.arithmetic).modifiedValuationCarrier :=
  rfl

theorem nativeSectionClause_sectionMap (C : SourceCompletion.{0} l)
    (G : NativeD7Intake C) :
    (nativeSectionClause C G).sectionMap =
      (SourceValuationSectionLayer.canonical C.arithmetic).sectionMap :=
  rfl

theorem nativeSectionClause_sectionRightInverse (C : SourceCompletion.{0} l)
    (G : NativeD7Intake C) :
    (nativeSectionClause C G).sectionRightInverse =
      (SourceValuationSectionLayer.canonical C.arithmetic).sectionRightInverse :=
  rfl

theorem nativeSectionClause_finitePlaceData (C : SourceCompletion.{0} l)
    (G : NativeD7Intake C) :
    (nativeSectionClause C G).finitePlaceData = G.finitePlaceData :=
  rfl

theorem nativeSectionClause_infinitePlaceData (C : SourceCompletion.{0} l)
    (G : NativeD7Intake C) :
    (nativeSectionClause C G).infinitePlaceData = G.infinitePlaceData :=
  rfl

/-- Exact explicit hypotheses for a real-valued cusp clause. These are
hypotheses, not values read from the native tuple; `native_epsilon_realization`
records the missing bridge from the geometric `OrbicurveBoundaryCusp` to this
real cusp coordinate. -/
structure NativeCuspClauseHypotheses where
  /-- The real cusp coordinate required by `SourceCuspClause`. -/
  epsilon : Real
  epsilon_positive : 0 < epsilon
  epsilon_nonzero : epsilon ≠ 0
  /-- The real cusp scale required by `SourceCuspClause`. -/
  cuspScale : Real
  cuspScale_positive : 0 < cuspScale
  epsilon_scale_relation : epsilon * cuspScale ≠ 0
  epsilon_compatibility : Prop
  epsilon_compatibility_proved : epsilon_compatibility
  /-- Exact missing identification of the native geometric cusp with the real
  coordinate `epsilon`. This proposition is not proved here. -/
  native_epsilon_realization : Prop

/-- Conditional cusp clause from the exact real-coordinate hypotheses. The
real fields are not arbitrary constants of this file; they are the explicit
input package, and `native_epsilon_realization` records the missing native
realization. -/
def nativeCuspClauseOfHypotheses
    (H : NativeCuspClauseHypotheses) : Theorem311Source.SourceCuspClause where
  epsilon := H.epsilon
  epsilon_positive := H.epsilon_positive
  epsilon_nonzero := H.epsilon_nonzero
  epsilon_compatibility := H.epsilon_compatibility
  epsilon_compatibility_proved := H.epsilon_compatibility_proved
  cuspScale := H.cuspScale
  cuspScale_positive := H.cuspScale_positive
  epsilon_scale_relation := H.epsilon_scale_relation

theorem nativeCuspClauseOfHypotheses_epsilon
    (H : NativeCuspClauseHypotheses) :
    (nativeCuspClauseOfHypotheses H).epsilon = H.epsilon := rfl

theorem nativeCuspClauseOfHypotheses_cuspScale
    (H : NativeCuspClauseHypotheses) :
    (nativeCuspClauseOfHypotheses H).cuspScale = H.cuspScale := rfl

end NativeSourceSectionsCuspActual
end InitialThetaSource
end LeanFormal.IUT

end
