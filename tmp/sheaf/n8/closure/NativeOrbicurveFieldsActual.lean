import tmp.sheaf.n8.closure.NativeSourceOrbicurveActual
import LeanFormal.IUT.IUTI.InitialTheta.SourceClauseConstructors
import Mathlib.Tactic

/-!
# Bottom-up native orbicurve fields from clauses D/E/F

Reuses NativeSourceOrbicurveActual.lean for the actual native exact
sequence. This file derives what is actually determined by clauses D/E/F:

* the exact sequence clause from D.x_groups.sequence (with the explicit
  missing splitting section);
* curve compatibility from the actual finite-etale cover
  D.k_l_torsion_cover;
* the cusp origin from clause F and its equality with S.epsilon.

The following SourceOrbicurveClause fields are NOT determined by the
clause data and are reported as exact primitives:

* curve/punctured/cover point carriers and curveToPunctured;
* coverToPunctured and its surjectivity (no point map is supplied; only
  the orbicurve stack morphism exists);
* cuspCount with positivity (clause F has one cusp origin but no finite
  cusp set/cardinality);
* the exact-sequence splitting section (already explicit above).

No arbitrary carrier, True, PUnit, fake exact sequence, axiom, or sorry is
used. curveCompatibility is derived, not assumed.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 1000000

namespace LeanFormal.IUT.InitialThetaSource.NativeOrbicurveFieldsActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.Theorem311Source
open Iut

universe u

variable {l : PrimeGeFive} {A : InitialThetaArithmeticData l}
variable {S : SourceSignQuotientData A} {C : SourceClauseA A S}
variable {B : SourceClauseB A S C} {Dc : SourceClauseC A S C B}

/-- Clause D's actual finite-etale cover gives the curve-compatibility
witness: a nonempty native cover from xK to cK. -/
theorem curveCompatibility_of_clauseD
    (E : SourceClauseD A S C B Dc) :
    Nonempty (SourceOrbicurveFiniteEtaleCover S.xK S.cK) :=
  ⟨E.k_l_torsion_cover⟩

/-- Clause D's actual exact sequence, with the missing splitting section as an
explicit primitive. -/
def exactSequence_of_clauseD
    (E : SourceClauseD A S C B Dc)
    (sectionMap : ↥(AbsoluteGaloisProfinite A.K) →*
      ↥E.x_groups.sequence.arithmetic)
    (section_right_inverse : ∀ x : ↥(AbsoluteGaloisProfinite A.K),
      E.x_groups.sequence.projection (sectionMap x) = x) :
    SourceExactSequenceClause :=
  NativeSourceOrbicurveActual.sourceExactSequenceOfGroups
    E.x_groups.sequence sectionMap section_right_inverse

/-- Clause F's cusp decomposition gives the actual cusp origin. -/
def cusp_of_clauseF
    {E : SourceClauseD A S C B Dc}
    (L : SourceClauseE A S C B Dc E)
    (F : SourceClauseF A S C B Dc E L) :
    Iut.OrbicurveBoundaryCusp S.cK :=
  F.cusp_decomposition.cusp

/-- Clause F identifies the cusp origin with the sign-quotient epsilon. -/
theorem cusp_eq_epsilon_of_clauseF
    {E : SourceClauseD A S C B Dc}
    (L : SourceClauseE A S C B Dc E)
    (F : SourceClauseF A S C B Dc E L) :
    F.cusp_decomposition.cusp = S.epsilon :=
  F.cusp_decomposition_cusp_eq_origin.trans F.boundary_cusp_eq_epsilon

/- Exact primitive fields still missing for a full SourceOrbicurveClause:
1. curve/punctured/cover point carriers;
2. curveToPunctured;
3. coverToPunctured and Function.Surjective coverToPunctured;
4. cuspCount and 0 < cuspCount;
5. the exact-sequence splitting sectionMap and right-inverse proof.
Only curveCompatibility is derived outright (from D.k_l_torsion_cover).
No fake data is introduced. -/

#check curveCompatibility_of_clauseD
#check exactSequence_of_clauseD
#check cusp_of_clauseF
#check cusp_eq_epsilon_of_clauseF

end LeanFormal.IUT.InitialThetaSource.NativeOrbicurveFieldsActual

end
