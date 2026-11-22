import tmp.sheaf.xif.paper.AG_FLT_CanonicalDivisorPromotionActual
import Mathlib.Tactic

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 1000000

/-!
# AG10: canonical divisor / genus layer (A-class reuse of canonical promotions)

Consumes qpilot's canonical promotions (all complete proofs):
* AG_FLT_CanonicalDivisorPromotionActual (checker CITABLE 3):
  promotion_canonicalDivisorOf/_apply, promotion_canonicalClass, promotion_genus,
  promotion_ell_canonicalDivisor_eq_genus_of_riemannRoch (COMPLETE),
  promotion_degree_canonicalDivisor_eq_of_riemannRoch (COMPLETE);
* AG_FLT_RiemannRochPromotionActual (RR rows + two COMPLETE reductions);
* AG_FLT_CechPromotionActual (Cech H0/H1 complete proofs, used in AG05).
The genus layer completes the bottom-up AG chain toward GeometricCore (genus g and
canonical divisor are the RR inputs of [Mzk1] Thm 2.5).  Conditional hypotheses are
exactly the paper RR rows (hRR, hC, DCoordGenerates) as in the source; no new axiom.

**Component, not paper object.**  Registry frozen 14041; no registry edits.
No sorry/axiom/True/PUnit/toy carrier.
-/

namespace LeanFormal.IUT.XiFPaper.AG10CanonicalDivisorGenusActual

open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.AG_FLT_CanonicalDivisorPromotionActual
open AlgebraicCurve KaehlerDifferential

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

/-- The canonical divisor of a nonzero Kaehler differential (A-class reuse). -/
noncomputable def ag10CanonicalDivisor [HasCanonicalDivisor (K := K) (F := F)]
    {ω : Ω[F⁄K]} (hω : ω ≠ 0) : AlgebraicCurve.Divisor K F :=
  promotion_canonicalDivisorOf hω

/-- Value formula: the canonical divisor at a place is the order of the differential
(complete proof, reused). -/
theorem ag10CanonicalDivisor_apply [HasCanonicalDivisor (K := K) (F := F)]
    {ω : Ω[F⁄K]} (hω : ω ≠ 0) (v : AlgebraicCurve.Place K F) :
    ag10CanonicalDivisor hω v = v.ordDifferential ω :=
  promotion_canonicalDivisorOf_apply hω v

/-- The canonical class in Pic (A-class reuse). -/
noncomputable def ag10CanonicalClass [HasCanonicalDivisor (K := K) (F := F)] :
    AlgebraicCurve.Pic K F :=
  promotion_canonicalClass (K := K) (F := F)

/-- The genus from the canonical divisor (A-class reuse). -/
noncomputable def ag10Genus [HasCanonicalDivisor (K := K) (F := F)] : Nat :=
  promotion_genus (K := K) (F := F)

/-- Ell of the canonical divisor equals the genus (COMPLETE ported proof; conditional
on the paper RR rows exactly as in the source). -/
theorem ag10_ell_canonicalDivisor_eq_genus
    [IsCurveOver K F] [HasCanonicalDivisor (K := K) (F := F)]
    [∀ v : AlgebraicCurve.Place K F, v.DCoordGenerates]
    (hRR : FunctionFieldRiemannRoch K F) (hC : ConstantsAreBase K F)
    {ω : Ω[F⁄K]} (hω : ω ≠ 0) :
    (AlgebraicCurve.ell (canonicalDivisorOf hω) : Int) = (genus K F : Int) :=
  promotion_ell_canonicalDivisor_eq_genus_of_riemannRoch hRR hC hω

/-- Degree of the canonical divisor is 2g-2 (COMPLETE ported proof; same paper-row
conditions). -/
theorem ag10_degree_canonicalDivisor_eq
    [IsCurveOver K F] [HasCanonicalDivisor (K := K) (F := F)]
    [∀ v : AlgebraicCurve.Place K F, v.DCoordGenerates]
    (hRR : FunctionFieldRiemannRoch K F) (hC : ConstantsAreBase K F)
    {ω : Ω[F⁄K]} (hω : ω ≠ 0) :
    AlgebraicCurve.Divisor.degree (canonicalDivisorOf hω) =
      2 * (genus K F : Int) - 2 :=
  promotion_degree_canonicalDivisor_eq_of_riemannRoch hRR hC hω

/-- A-class reuse record. -/
def ag10Reuse : List (String × String × String) :=
  [ ("canonical divisor / canonical class / genus", "AG_FLT_CanonicalDivisorPromotionActual (CITABLE 3; ported flt_test)", "A (complete; reused)"),
    ("ell(canonical) = g and deg(canonical) = 2g-2", "promotion_ell_/degree_canonicalDivisor_eq_*", "A (COMPLETE ported proofs; conditional exactly on paper RR rows)"),
    ("RR rows", "AG_FLT_RiemannRochPromotionActual (separate canonical module; NOT imported here to avoid flt/flt_test duplicate-namespace clash)", "A (reuse in its own consumers)"),
    ("Cech H0/H1", "AG_FLT_CechPromotionActual (CITABLE 5)", "A (reuse; AG05)"),
    ("GeometricCore inputs", "[Mzk1] Thm 2.5 uses genus/canonical divisor/RR (class-D GeometricCore; this layer supplies the A-class AG side)", "A infra; assembly gated") ]

end LeanFormal.IUT.XiFPaper.AG10CanonicalDivisorGenusActual

end
