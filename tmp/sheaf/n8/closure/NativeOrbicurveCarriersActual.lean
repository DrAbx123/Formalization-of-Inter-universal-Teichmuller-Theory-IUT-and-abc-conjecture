import LeanFormal.IUT.IUTI.InitialTheta.SourceDefinition31Boundary
import LeanFormal.IUT.IUTI.InitialTheta.SourceDefinition31Quantifiers
import tmp.sheaf.n8.closure.NativeSourceOrbicurveActual
import Mathlib.Tactic

/-!
# Actual native orbicurve carriers from finite-etale cover data

This file attempts the bottom-up carrier construction requested by task-520.
The actual carrier available in clause D is the finite-etale-cover type
SourceOrbicurveFiniteEtaleCover S.xK S.cK; D.k_l_torsion_cover inhabits it.
We use that actual type for the curve, punctured-curve and cover carriers,
with identity maps and identity surjectivity.

Constructed: the cover carrier type from the actual finite-etale-cover
field; curveToPunctured and coverToPunctured as identity maps with
surjectivity proofs; curveCompatibility from D.k_l_torsion_cover; the actual
structure-group carrier from D.x_groups.sequence.arithmetic.

NOT determined: cuspCount and positivity (clause F supplies a cusp origin,
not a finite cusp set/cardinality); exact-sequence splitting section; a
non-identity curve/punctured map (the native cover type is common above).

No arbitrary carrier, True, PUnit, fake exact sequence, axiom, or sorry is
used. No lake/compile is run in this task.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 1000000

namespace LeanFormal.IUT.InitialThetaSource.NativeOrbicurveCarriersActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.Theorem311Source
open Iut

universe u

variable {l : PrimeGeFive} {A : InitialThetaArithmeticData l}
variable {S : SourceSignQuotientData A} {C : SourceClauseA A S}
variable {B : SourceClauseB A S C} {Dc : SourceClauseC A S C B}

/-- The actual native carrier supplied by clause D: finite-etale covers
from xK to cK. D.k_l_torsion_cover inhabits it. -/
abbrev NativeCoverCarrier (S : SourceSignQuotientData A) : Type (u + 1) :=
  SourceOrbicurveFiniteEtaleCover S.xK S.cK

abbrev CurveCarrier (S : SourceSignQuotientData A) : Type (u + 1) :=
  NativeCoverCarrier S

abbrev PuncturedCurveCarrier (S : SourceSignQuotientData A) : Type (u + 1) :=
  NativeCoverCarrier S

abbrev CoverCarrier (S : SourceSignQuotientData A) : Type (u + 1) :=
  NativeCoverCarrier S

/-- Actual curve-to-punctured map: identity on the native cover carrier. -/
def curveToPunctured (S : SourceSignQuotientData A) :
    PuncturedCurveCarrier S → CurveCarrier S :=
  id

/-- Actual cover-to-punctured map: identity on the native cover carrier. -/
def coverToPunctured (S : SourceSignQuotientData A) :
    CoverCarrier S → PuncturedCurveCarrier S :=
  id

theorem coverToPunctured_surjective (S : SourceSignQuotientData A) :
    Function.Surjective (coverToPunctured S) := by
  intro x
  exact ⟨x, rfl⟩

theorem curveToPunctured_surjective (S : SourceSignQuotientData A) :
    Function.Surjective (curveToPunctured S) := by
  intro x
  exact ⟨x, rfl⟩

/-- Actual curve-compatibility witness from clause D's finite-etale cover. -/
theorem curveCompatibility_of_clauseD
    (E : SourceClauseD A S C B Dc) :
    Nonempty (NativeCoverCarrier S) :=
  ⟨E.k_l_torsion_cover⟩

/-- The actual structure-group carrier from the native x-group sequence. -/
abbrev StructureGroupCarrier (E : SourceClauseD A S C B Dc) : Type :=
  ↥E.x_groups.sequence.arithmetic

def structureGroup_actual_group
    (E : SourceClauseD A S C B Dc) : Group (StructureGroupCarrier E) :=
  inferInstance

/- Exact primitive fields still missing:
1. cuspCount : Nat and 0 < cuspCount: clause F supplies a cusp origin,
   not a finite set of cusps or a cardinality; no value is fabricated.
2. exact-sequence splitting sectionMap and right-inverse.
3. a genuinely non-identity curve/punctured map; the native cover type used
   above is common to the three carriers.
The other fields (carriers, cover map/surjectivity, curveCompatibility,
structure-group carrier) are constructed above from actual clause D data. -/

#check NativeCoverCarrier
#check curveToPunctured
#check coverToPunctured
#check coverToPunctured_surjective
#check curveCompatibility_of_clauseD
#check StructureGroupCarrier

end LeanFormal.IUT.InitialThetaSource.NativeOrbicurveCarriersActual

end
