import tmp.sheaf.n8.closure.NativeSourceSectionsCuspActual
import LeanFormal.IUT.IUTI.InitialTheta.SourceClauseConstructors

/-! # Derived native section/cusp fields: exact primitives

Bottom-up audit of `SourceCompletion`/clause F against the two boundary
clauses of Definition 3.1(e)/(f).

## Result

* The section clause reduces exactly to the D7 local-group primitive
  `NativeD7Intake C = D7LocalGroupSectionSupply (canonical layer)`; the place
  half is already actual, the local-group half is not determined by
  `SourceCompletion` (global `clauseC.x_groups/c_groups` are not local groups
  over the canonical valuation carriers).
* The cusp clause reduces exactly to a real-coordinate primitive
  `NativeCuspClauseHypotheses`; the native tuple epsilon is an
  `Iut.OrbicurveBoundaryCusp`, not a real number, and neither
  `SourceCompletion` nor clause F supplies `epsilon : Real` or
  `cuspScale : Real`.  No arbitrary real is chosen.

These are exact primitive fields, not interface additions: the constructors
below consume them and produce the actual clauses.

No `PUnit`, `True`, `sorry`, or axiom is used.  No derivation is asserted.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT
namespace InitialThetaSource
namespace NativeSectionsCuspFieldsActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.NativeSourceSectionsCuspActual
open LeanFormal.IUT.InitialThetaSource.Definition31D4D9Supply

variable {l : PrimeGeFive} (C : SourceCompletion.{0} l)

/-- The native tuple epsilon is the actual geometric boundary cusp. -/
def nativeTupleEpsilonType :
    Iut.OrbicurveBoundaryCusp C.sourceSignQuotientData.cK :=
  nativeTupleEpsilon C

/-- The clause-F boundary cusp is the same native geometric cusp. -/
def clauseFBoundaryCusp :
    Iut.OrbicurveBoundaryCusp C.sourceSignQuotientData.cK :=
  C.clauseF.boundary_origin.cusp

theorem clauseFBoundaryCusp_eq_native :
    clauseFBoundaryCusp C = nativeTupleEpsilon C :=
  C.clauseF.boundary_cusp_eq_epsilon

/-- The exact D7 primitive: the local-group supply over the canonical
valuation section. This is the only missing field of the section clause. -/
abbrev D7Primitive (C : SourceCompletion.{0} l) : Type 1 :=
  NativeD7Intake C

/-- Exact section clause from the D7 primitive. -/
def sectionClauseFromD7Primitive (C : SourceCompletion.{0} l)
    (G : D7Primitive C) : Theorem311Source.SourceSectionClause :=
  nativeSectionClause C G

theorem sectionClauseFromD7Primitive_carrier (C : SourceCompletion.{0} l)
    (G : D7Primitive C) :
    (sectionClauseFromD7Primitive C G).valuationCarrier =
      (SourceValuationSectionLayer.canonical C.arithmetic).valuationCarrier :=
  rfl

/-- The exact real-coordinate primitive of the cusp clause. -/
abbrev CuspPrimitive : Type :=
  NativeCuspClauseHypotheses

/-- Exact cusp clause from the real-coordinate primitive. -/
def cuspClauseFromPrimitive (H : CuspPrimitive) :
    Theorem311Source.SourceCuspClause :=
  nativeCuspClauseOfHypotheses H

theorem cuspClauseFromPrimitive_epsilon (H : CuspPrimitive) :
    (cuspClauseFromPrimitive H).epsilon = H.epsilon := rfl

theorem cuspClauseFromPrimitive_cuspScale (H : CuspPrimitive) :
    (cuspClauseFromPrimitive H).cuspScale = H.cuspScale := rfl

/-- Exact primitive proposition for the section clause: existence of the D7
local-group supply. This is not proved from `C`. -/
def D7PrimitiveRequired (C : SourceCompletion.{0} l) : Prop :=
  Nonempty (D7Primitive C)

/-- Exact primitive proposition for the cusp clause: existence of the real
coordinate package. This is not proved from `C` or clause F. -/
def CuspPrimitiveRequired : Prop :=
  Nonempty CuspPrimitive

/-- The global clause-C group data exists, but it is global, not the local
group supply over the canonical valuation carriers. This records the exact
type distinction without fabricating a map. -/
def clauseCGlobalCGroup :=
  C.clauseD.c_groups

def clauseCGlobalCGroupType :
    SourceOrbicurveGroupData C.sourceSignQuotientData.cK
      (Iut.AbsoluteGaloisProfinite C.arithmetic.K) :=
  clauseCGlobalCGroup C

/-- Clause E carries local sources at the selected places, but those are
indexed by the selected source set, not by the canonical valuation carriers.
This is the exact D7 obstruction. -/
def clauseELocalSource
    (v : {v : NumberFieldPlace C.arithmetic.K //
      v ∈ C.sourceSignQuotientData.V})
    (hv : v.1.IsFinite) :=
  C.clauseE.finite_local v hv

end NativeSectionsCuspFieldsActual
end InitialThetaSource
end LeanFormal.IUT

end
