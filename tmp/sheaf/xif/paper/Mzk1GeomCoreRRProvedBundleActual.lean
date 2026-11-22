import tmp.sheaf.xif.paper.Mzk1RRProvedActual
import tmp.sheaf.xif.paper.Mzk1GeomCoreRRProvedActual

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 2000000

noncomputable section

/-!
# STEP 0 prior-art: D-RR bundle (B6b BOTTOM evidence) -> Mzk1RRProvedActual.functionFieldRiemannRoch_proved (flt_core real port) + Mzk1GeomCoreRRProvedActual.zero_divisor_exists_proved/degree_punctureDivisor/canonical_degree_le_two_genus -> PROVED bundle: RR statement + zero divisor existence from one context (no named inputs beyond ported instances). No closure claim.

# Mzk1GeomCoreRRProvedBundleActual — D-RR proved bundle

PROVED:
* `rr_zeroDivisor_bundle`: FunctionFieldRiemannRoch K F AND a zero-divisor function for
  any finite T with |T| >= 2g+1;
* `rr_canonical_bound`: the canonical degree bound 2g-1.
Registry frozen 14041.  No closure claim.
-/

namespace LeanFormal.IUT.XiFPaper.Mzk1GeomCoreRRProvedBundleActual

open AlgebraicCurve
open LeanFormal.IUT.XiFPaper.Mzk1RRProvedActual
open LeanFormal.IUT.XiFPaper.Mzk1GeomCoreRRProvedActual

universe u v

/-- **PROVED:** RR statement + zero divisor existence bundle on the flt_core root. -/
theorem rr_zeroDivisor_bundle {K F : Type*} [Field K] [IsAlgClosed K] [Infinite K]
    [DecidableEq (RatFunc K)] [Field F] [Algebra K F]
    [HasCanonicalDivisor (K := K) (F := F)]
    [∀ w : Place K F, w.DCoordGenerates]
    [Algebra (RatFunc K) F] [IsScalarTower K (RatFunc K) F]
    [Algebra.IsIntegral (RatFunc K) F] [Module.Finite (RatFunc K) F]
    [HasLocalResidue K F] [∀ w : Place K F, w.FiniteResidue] [Nontrivial Ω[F⁄K]]
    [IsCurveOver K F] [IsCurveOver K (RatFunc K)]
    [∀ u : Place K (RatFunc K), u.FiniteResidue]
    [HasCanonicalLocalResidueKStar K F] [HasPrincipalDivisors K F]
    [Algebra.IsSeparable (RatFunc K) F]
    [Nontrivial Ω[(RatFunc K)⁄K]] [∀ v : Place K (RatFunc K), v.DCoordGenerates]
    [FiniteDimensional (RatFunc K) F] [HasSeparableResidue K F]
    (T : Finset (Place K F)) (hcard : 2 * genus K F + 1 ≤ T.card) :
    FunctionFieldRiemannRoch K F ∧
      ∃ g : F, g ≠ 0 ∧ (∀ p : Place K F, 0 < p.ord g ↔ p ∈ T) ∧
        ∀ t ∈ T, t.ord g = 1 :=
  ⟨functionFieldRiemannRoch_proved (K := K) (F := F),
    zero_divisor_exists_proved (K := K) (F := F) T hcard⟩

/-- **PROVED:** the canonical divisor degree is at most 2g-1. -/
theorem rr_canonical_bound {K F : Type*} [Field K] [Field F] [Algebra K F]
    [HasCanonicalDivisor (K := K) (F := F)]
    (hex : ∃ ω : Ω[F⁄K], ω ≠ 0) :
    Divisor.degree (canonicalDivisorOf hex.choose_spec) ≤ 2 * (genus K F : ℤ) - 1 :=
  canonical_degree_le_two_genus hex

def rrBundleRows : List (String × String × String) :=
  [ ("RR statement + zero divisor bundle", "PROVED", "rr_zeroDivisor_bundle")
  , ("canonical degree bound 2g-1", "PROVED", "rr_canonical_bound")
  , ("named inputs of this bundle", "NONE", "only the ported flt_core instances; no hRR/hdual hypotheses") ]

theorem rrBundleRows_length : rrBundleRows.length = 3 := rfl

#check rr_zeroDivisor_bundle
#check rr_canonical_bound
#check rrBundleRows_length

end LeanFormal.IUT.XiFPaper.Mzk1GeomCoreRRProvedBundleActual
end