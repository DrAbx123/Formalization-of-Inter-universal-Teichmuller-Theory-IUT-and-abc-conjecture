/-
  Source-level Tate point uniformization (scratch).

  This file assembles the actually provable canonical Tate point map from the
  production files and isolates the exact remaining classical statement for the
  split multiplicative source curve.

  Proven here:
  * the canonical quotient point map `tateQuotientPoint q hq hdata` as a function;
  * its q^Z-periodicity and nonvanishing (both from production);
  * existence of the closed source q_v datum from SourceQvClosed.

  Not proven: injectivity/surjectivity of the canonical map and the group
  isomorphism E(K) ~= K^x/q^Z.  These are isolated in
  `CanonicalTatePointMapBijectionObligation` and
  `SourcePointUniformizationObligation`.
-/
import LeanFormal.IUT.Foundations.NumberField.SourceQvClosed
import LeanFormal.IUT.Foundations.Geometry.TateUniformizationPointMap
import LeanFormal.IUT.Foundations.Geometry.TateUniformizationPointMapReduction
import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
import Mathlib.Tactic

set_option relaxedAutoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

noncomputable section

namespace LeanFormal.IUT.SourcePointUniformization

open LeanFormal.IUT
open LeanFormal.IUT.TateCurve
open LeanFormal.IUT.SourceQvClosed
open LeanFormal.IUT.NumberFieldFinitePlace

universe u

variable {K : Type u} [NontriviallyNormedField K] [CompleteSpace K]
  [CharZero K] [IsUltrametricDist K]

/-! ## The canonical point map that is actually constructed -/

/-- The canonical Tate quotient point map, as an actual function from the
pole-excluded K^x/q^Z quotient to affine points of the canonical q-curve. -/
def canonicalTatePointMap (q : K) (hq : q ≠ 0)
    (hdata : TateWeierstrassPointData q) :
    TateParameterQuotient q hq → (TateCurve.weierstrassCurve K q).toAffine.Point :=
  fun w => tateQuotientPoint q hq hdata w

/-- The canonical point map is q^Z-periodic. -/
theorem canonicalTatePointMap_orbit (q : K) (hq : q ≠ 0)
    (hdata : TateWeierstrassPointData q) (m : ℤ)
    (u : ↥(coordinateParameterDomain q)) :
    canonicalTatePointMap q hq hdata
        (Quotient.mk _ (tateParameterOrbit hq m u)) =
      canonicalTatePointMap q hq hdata (Quotient.mk _ u) :=
  tateQuotientPoint_orbit hq hdata m u

/-- No canonical point-map value is the point at infinity. -/
theorem canonicalTatePointMap_ne_zero (q : K) (hq : q ≠ 0)
    (hdata : TateWeierstrassPointData q)
    (w : TateParameterQuotient q hq) :
    canonicalTatePointMap q hq hdata w ≠ 0 :=
  tateQuotientPoint_ne_zero hq hdata w

/-! ## Exact canonical bijection obligation -/

/-- The exact remaining canonical Tate point-map statement: injectivity and
surjectivity onto the nonzero affine points.  This is exactly the production
`TateUniformizationPointMapGap`. -/
def CanonicalTatePointMapBijectionObligation (q : K) (hq : q ≠ 0)
    (hdata : TateWeierstrassPointData q) : Prop :=
  TateUniformizationPointMapGap q hq hdata

/-- The bijection obligation is equivalent to the two concrete pair-coordinate
conditions from production. -/
theorem canonicalTatePointMapBijectionObligation_iff (q : K) (hq : q ≠ 0)
    (hdata : TateWeierstrassPointData q) :
    CanonicalTatePointMapBijectionObligation q hq hdata ↔
      tatePairCoordinatesSeparateOrbits q ∧ tateCoordinatesCoverNonzeroPoints q :=
  tateUniformizationPointMapGap_iff_pairConditions q hq hdata

/-! ## Closed source q_v input -/

section SourceFinitePlace

variable {F : Type u} [Field F] [NumberField F]

local instance instAlgebraSourceField (v : NumberField.FinitePlace F) :
    Algebra F (NormalizedCompletion v) :=
  inferInstanceAs (Algebra F (Completion v))

/-- The closed source q_v theorem from production, restated for the point layer. -/
theorem sourceQv_exists_at_finitePlace (v : NumberField.FinitePlace F)
    (X : PuncturedEllipticCurve F)
    (hsplit : X.HasSplitMultiplicativeReductionAt v) :
    Nonempty (SourceQv (K := NormalizedCompletion v)
      (X.baseChange (NormalizedCompletion v)).curve
      (X.baseChange (NormalizedCompletion v)).isElliptic) :=
  exists_sourceQv_at_finitePlace_closed v X hsplit

/-- The exact source point-uniformization obligation.  It is deliberately a Prop
with no inhabitant: it requires a source q_v, a Weierstrass coordinate change
identifying the canonical q-curve with the local source curve, the canonical
point-map bijection, and the group-level point equivalence E(K) ~= K^x/q^Z. -/
def SourcePointUniformizationObligation (v : NumberField.FinitePlace F)
    (X : PuncturedEllipticCurve F)
    (hsplit : X.HasSplitMultiplicativeReductionAt v) : Prop :=
  letI : (X.baseChange (NormalizedCompletion v)).curve.IsElliptic :=
    (X.baseChange (NormalizedCompletion v)).isElliptic
  ∃ S : SourceQv (K := NormalizedCompletion v)
      (X.baseChange (NormalizedCompletion v)).curve
      (X.baseChange (NormalizedCompletion v)).isElliptic,
    ∃ hdata : TateWeierstrassPointData (K := NormalizedCompletion v) S.q,
      CanonicalTatePointMapBijectionObligation (K := NormalizedCompletion v) S.q
        S.q_ne_zero hdata ∧
      ∃ C : WeierstrassCurve.VariableChange (NormalizedCompletion v),
        C • TateCurve.weierstrassCurve (NormalizedCompletion v) S.q =
          (X.baseChange (NormalizedCompletion v)).curve ∧
        Nonempty ((X.baseChange (NormalizedCompletion v)).curve.toProjective.Point ≃+
          Additive ((NormalizedCompletion v)ˣ ⧸
            Subgroup.zpowers (Units.mk0 S.q S.q_ne_zero)))

end SourceFinitePlace

/-! ## Exact remaining statement, stated without hiding it in data

The classical Tate point uniformization theorem supplies:
1. a point data hdata and the canonical bijection
   TateParameterQuotient q hq ~= nonzero points of the canonical q-curve;
2. a Weierstrass coordinate change from the canonical q-curve to the source
   curve E;
3. the group law on the canonical q-curve and the resulting group isomorphism
   E(K) ~= K^x / q^Z.
None of these three is proved here; they are isolated in
SourcePointUniformizationObligation. -/

end LeanFormal.IUT.SourcePointUniformization

end