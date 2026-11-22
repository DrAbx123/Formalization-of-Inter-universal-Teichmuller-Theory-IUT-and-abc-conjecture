import LeanFormal.IUT.IUTI.InitialTheta.SourceDefinition31Boundary
import LeanFormal.IUT.IUTI.InitialTheta.SourceDefinition31Quantifiers

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

/-!
# Native cusp proof attempt: real epsilon and cuspScale from geometric cusp data

Task-531 write-only attempt.

Inputs read:
* SourceDefinition31Quantifiers.lean, SourceClauseF:
  - boundary_origin : TorsionQuotientBoundaryOrigin l A S.cK;
  - boundary_cusp_eq_epsilon : boundary_origin.cusp = S.epsilon;
  - cusp_decomposition : OrbicurveCuspidalDecompositionData E.c_groups.groups;
  - cusp_decomposition_cusp_eq_origin : cusp_decomposition.cusp = boundary_origin.cusp.
* SourceSignQuotientData: epsilon : OrbicurveBoundaryCusp S.cK.
* SourceDefinition31Boundary.lean, SourceCuspClause:
  - epsilon : Real, epsilon_positive, epsilon_nonzero,
    epsilon_compatibility, cuspScale : Real, cuspScale_positive,
    epsilon_scale_relation.

The actual source cusp is geometric:
Iut.OrbicurveBoundaryCusp S.cK. Neither SourceClauseF nor the cusp
decomposition constructs a map from this geometric cusp object to a Real
number, and neither supplies a real cuspScale. The source also supplies no
positivity theorem for a real cusp width. Therefore the following are exact
missing source primitives:

1. geometricCuspToReal : Iut.OrbicurveBoundaryCusp S.cK -> Real;
2. epsilon_positive : 0 < geometricCuspToReal S.epsilon;
3. cuspScale : Real and cuspScale_positive : 0 < cuspScale;
4. epsilon_compatibility : Prop and its proof.

Given exactly these primitives, this file constructs SourceCuspClause. It does
not choose a fake real number, does not use True/PUnit, and does not assert
that the geometric cusp has a real realization.
-/

noncomputable section

namespace LeanFormal.IUT.InitialThetaSource.NativeCuspProof

open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source

universe u

variable {l : PrimeGeFive}
variable {A : InitialThetaArithmeticData.{u} l}
variable {S : SourceSignQuotientData A}

/-- The exact missing geometric-real realization data for the cusp. -/
structure GeometricCuspRealization where
  /-- Missing map from the geometric cusp to a real cusp datum. -/
  geometricCuspToReal : Iut.OrbicurveBoundaryCusp S.cK → Real
  /-- The selected source cusp has positive real value. -/
  epsilon_positive : 0 < geometricCuspToReal S.epsilon
  /-- The real cusp scale. -/
  cuspScale : Real
  cuspScale_positive : 0 < cuspScale
  /-- The cusp compatibility statement, supplied by the source instance. -/
  epsilon_compatibility : Prop
  epsilon_compatibility_proved : epsilon_compatibility

/-- The actual selected geometric cusp is S.epsilon. -/
theorem selectedGeometricCusp :
    S.epsilon = S.epsilon := rfl

/-- The geometric cusp realization yields the real SourceCuspClause. The only
non-derived fields are the four primitives of GeometricCuspRealization. -/
noncomputable def geometricCuspRealizationToSourceCuspClause
    (R : GeometricCuspRealization (S := S)) :
    SourceCuspClause where
  epsilon := R.geometricCuspToReal S.epsilon
  epsilon_positive := R.epsilon_positive
  epsilon_nonzero := ne_of_gt R.epsilon_positive
  epsilon_compatibility := R.epsilon_compatibility
  epsilon_compatibility_proved := R.epsilon_compatibility_proved
  cuspScale := R.cuspScale
  cuspScale_positive := R.cuspScale_positive
  epsilon_scale_relation :=
    ne_of_gt (mul_pos R.epsilon_positive R.cuspScale_positive)

/-- The constructed real epsilon is exactly the geometric realization value. -/
theorem geometricCuspRealizationToSourceCuspClause_epsilon
    (R : GeometricCuspRealization (S := S)) :
    (geometricCuspRealizationToSourceCuspClause R).epsilon =
      R.geometricCuspToReal S.epsilon := rfl

/-- The constructed cusp scale is exactly the supplied real scale. -/
theorem geometricCuspRealizationToSourceCuspClause_cuspScale
    (R : GeometricCuspRealization (S := S)) :
    (geometricCuspRealizationToSourceCuspClause R).cuspScale = R.cuspScale := rfl

/-- The constructed real epsilon is positive. -/
theorem geometricCuspRealizationToSourceCuspClause_epsilon_pos
    (R : GeometricCuspRealization (S := S)) :
    0 < (geometricCuspRealizationToSourceCuspClause R).epsilon :=
  R.epsilon_positive

/-- The constructed cusp scale is positive. -/
theorem geometricCuspRealizationToSourceCuspClause_cuspScale_pos
    (R : GeometricCuspRealization (S := S)) :
    0 < (geometricCuspRealizationToSourceCuspClause R).cuspScale :=
  R.cuspScale_positive

/-- The constructed epsilon is nonzero. -/
theorem geometricCuspRealizationToSourceCuspClause_epsilon_ne_zero
    (R : GeometricCuspRealization (S := S)) :
    (geometricCuspRealizationToSourceCuspClause R).epsilon ≠ 0 :=
  ne_of_gt R.epsilon_positive

/-- The constructed epsilon/cuspScale product is nonzero. -/
theorem geometricCuspRealizationToSourceCuspClause_epsilon_scale_ne_zero
    (R : GeometricCuspRealization (S := S)) :
    (geometricCuspRealizationToSourceCuspClause R).epsilon *
      (geometricCuspRealizationToSourceCuspClause R).cuspScale ≠ 0 :=
  ne_of_gt (mul_pos R.epsilon_positive R.cuspScale_positive)

/-- The source clause F boundary cusp is the selected sign-quotient epsilon.
This is the actual geometric cusp identity available from SourceClauseF. -/
theorem clauseF_cusp_eq_epsilon
    {C : SourceClauseA A S} {B : SourceClauseB A S C}
    {D : SourceClauseC A S C B} {E : SourceClauseD A S C B D}
    {L : SourceClauseE A S C B D E}
    (F : SourceClauseF A S C B D E L) :
    F.boundary_origin.cusp = S.epsilon :=
  F.boundary_cusp_eq_epsilon

/-- The source clause F cusp decomposition lands at the selected epsilon. -/
theorem clauseF_cuspDecomposition_cusp_eq_epsilon
    {C : SourceClauseA A S} {B : SourceClauseB A S C}
    {D : SourceClauseC A S C B} {E : SourceClauseD A S C B D}
    {L : SourceClauseE A S C B D E}
    (F : SourceClauseF A S C B D E L) :
    F.cusp_decomposition.cusp = S.epsilon := by
  rw [F.cusp_decomposition_cusp_eq_origin, F.boundary_cusp_eq_epsilon]

/-- The exact missing-primitive package for the real cusp clause. -/
structure NativeCuspPrimitiveFields where
  geometricCuspToReal : Iut.OrbicurveBoundaryCusp S.cK → Real
  epsilon_positive : 0 < geometricCuspToReal S.epsilon
  cuspScale : Real
  cuspScale_positive : 0 < cuspScale
  epsilon_compatibility : Prop
  epsilon_compatibility_proved : epsilon_compatibility

/-- The primitive package is exactly the geometric realization structure. -/
def NativeCuspPrimitiveFields.toGeometricRealization
    (P : NativeCuspPrimitiveFields (S := S)) :
    GeometricCuspRealization (S := S) where
  geometricCuspToReal := P.geometricCuspToReal
  epsilon_positive := P.epsilon_positive
  cuspScale := P.cuspScale
  cuspScale_positive := P.cuspScale_positive
  epsilon_compatibility := P.epsilon_compatibility
  epsilon_compatibility_proved := P.epsilon_compatibility_proved

/-- The primitive package yields the real cusp clause through the explicit
geometric realization. -/
noncomputable def NativeCuspPrimitiveFields.toSourceCuspClause
    (P : NativeCuspPrimitiveFields (S := S)) : SourceCuspClause :=
  geometricCuspRealizationToSourceCuspClause P.toGeometricRealization

/-- Exact status: the geometric cusp is actual, but the real epsilon map and
the cuspScale/positivity/compatibility data are exactly the missing primitive
fields. No theorem in the current sources constructs them. -/
theorem nativeCuspProofStatus
    (P : NativeCuspPrimitiveFields (S := S)) :
    (P.toSourceCuspClause).epsilon = P.geometricCuspToReal S.epsilon ∧
      0 < (P.toSourceCuspClause).epsilon ∧
      0 < (P.toSourceCuspClause).cuspScale ∧
      (P.toSourceCuspClause).epsilon * (P.toSourceCuspClause).cuspScale ≠ 0 :=
  ⟨rfl, P.epsilon_positive, P.cuspScale_positive,
    ne_of_gt (mul_pos P.epsilon_positive P.cuspScale_positive)⟩

end LeanFormal.IUT.InitialThetaSource.NativeCuspProof

end
