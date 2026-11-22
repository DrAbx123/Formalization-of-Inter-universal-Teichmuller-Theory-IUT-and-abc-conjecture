import tmp.external.ported.flt_test.Definitions.Def_AlgebraicCurve_CanonicalDivisor
import tmp.external.ported.flt_test.Theorems.Thm_AlgebraicCurve_ell_canonicalDivisor_eq_genus_of_riemannRoch
import tmp.external.ported.flt_test.Theorems.Thm_AlgebraicCurve_degree_canonicalDivisor_eq_of_riemannRoch

/-!
# AG-FLT canonical-divisor / genus promotion (first-class importable modules; audit component)

COMPONENT, not a paper object.  Named consumers: stage4, stepxi GeometricCore,
Lead AG-INFRA-PLAN; [Mzk1]/GenEll genus layer.

Promotes the ported FLT canonical-divisor layer (green modules; Apache-2.0,
attribution in ported headers):
* HasCanonicalDivisor class, canonicalDivisorOf (+ apply lemma), canonicalClass,
  genus (tmp/external/ported/flt_core/Definitions/Def_AlgebraicCurve_CanonicalDivisor);
* the two COMPLETE ported theorems linking canonical divisor, genus and RR:
  ell(canonicalDivisorOf omega) = genus, and deg(canonicalDivisorOf omega) = 2g-2
  (tmp/external/ported/flt_test/Theorems/Thm_AlgebraicCurve_{ell,degree}_canonicalDivisor_eq_*),
  both conditional exactly on the RR rows / constants-are-base as in the source.
No axiom/fake data; source modules grep sorry/axiom = 0.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 1000000

namespace LeanFormal.IUT.XiFPaper.AG_FLT_CanonicalDivisorPromotionActual

open LeanFormal.IUT
open AlgebraicCurve KaehlerDifferential

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

/-- Promoted canonical divisor of a nonzero Kaehler differential. -/
noncomputable def promotion_canonicalDivisorOf [HasCanonicalDivisor (K := K) (F := F)]
    {ω : Ω[F⁄K]} (hω : ω ≠ 0) : AlgebraicCurve.Divisor K F :=
  canonicalDivisorOf hω

/-- COMPLETE proof (ported): value of the canonical divisor on a place. -/
theorem promotion_canonicalDivisorOf_apply [HasCanonicalDivisor (K := K) (F := F)]
    {ω : Ω[F⁄K]} (hω : ω ≠ 0) (v : AlgebraicCurve.Place K F) :
    promotion_canonicalDivisorOf hω v = v.ordDifferential ω :=
  canonicalDivisorOf_apply hω v

/-- Promoted canonical class in Pic. -/
noncomputable def promotion_canonicalClass [HasCanonicalDivisor (K := K) (F := F)] :
    AlgebraicCurve.Pic K F :=
  canonicalClass K F

/-- Promoted genus from the canonical divisor. -/
noncomputable def promotion_genus [HasCanonicalDivisor (K := K) (F := F)] : Nat :=
  genus K F

/-- COMPLETE proof (ported, conditional on the RR row set exactly as in source):
ell of the canonical divisor = genus. -/
theorem promotion_ell_canonicalDivisor_eq_genus_of_riemannRoch
    [IsCurveOver K F] [HasCanonicalDivisor (K := K) (F := F)]
    [∀ v : AlgebraicCurve.Place K F, v.DCoordGenerates]
    (hRR : FunctionFieldRiemannRoch K F) (hC : ConstantsAreBase K F)
    {ω : Ω[F⁄K]} (hω : ω ≠ 0) :
    (AlgebraicCurve.ell (canonicalDivisorOf hω) : Int) = (genus K F : Int) :=
  AlgebraicCurve.ell_canonicalDivisor_eq_genus_of_riemannRoch hRR hC hω

/-- COMPLETE proof (ported, conditional on the RR row set exactly as in source):
degree of the canonical divisor = 2g-2. -/
theorem promotion_degree_canonicalDivisor_eq_of_riemannRoch
    [IsCurveOver K F] [HasCanonicalDivisor (K := K) (F := F)]
    [∀ v : AlgebraicCurve.Place K F, v.DCoordGenerates]
    (hRR : FunctionFieldRiemannRoch K F) (hC : ConstantsAreBase K F)
    {ω : Ω[F⁄K]} (hω : ω ≠ 0) :
    AlgebraicCurve.Divisor.degree (canonicalDivisorOf hω) = 2 * (genus K F : Int) - 2 :=
  AlgebraicCurve.degree_canonicalDivisor_eq_of_riemannRoch hRR hC hω

end LeanFormal.IUT.XiFPaper.AG_FLT_CanonicalDivisorPromotionActual
