import tmp.sheaf.xif.paper.AG_FLT_ProvedTheoremsPromotionActual
import Mathlib.Tactic

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 2000000

/-!
# AG14: canonical proved-theorems consumer (A-class reuse; qpilot promotions)

STEP 0 prior-art (reuse, no re-proof): qpilot AG_FLT_ProvedTheoremsPromotionActual
(CITABLE 3) re-exports the three serially-compiled FLT results with explicit
statements and COMPLETE ported proofs (source grep sorry/axiom = 0):
* serrePairing_bijective_and_flip_bijective (Serre pairing + flip bijective);
* weilDualityAdelic_of_isAlgClosed (adelic Weil duality over algebraically closed K);
* cechRiemannRoch_of_genusReached (Cech Riemann-Roch at reached genus).
This file is the AG-layer consumer: exact-statement re-exports under ag14_* names so
GeomCore/RR/Serde consumers import a stable AG name instead of the promotion module.
No axiom added; the proof terms are the promoted ported solutions.
NOTE: imports only the flt_core universe (namespace-clash safe).

**Component, not paper object.**  Registry frozen 14041; no registry edits.
No sorry/axiom/True/PUnit/toy carrier.
-/

namespace LeanFormal.IUT.XiFPaper.AG14ProvedTheoremsConsumerActual

open LeanFormal.IUT.XiFPaper.AG_FLT_ProvedTheoremsPromotionActual
open AlgebraicCurve KaehlerDifferential

/-- A-class: Serre pairing and its flip are bijective (COMPLETE ported proof). -/
theorem ag14_serde_pairing_bijective
    {K : Type*} {F : Type*} [Field K] [Field F] [Algebra K F]
    [PerfectField K] [Algebra.EssFiniteType K F] [IsCurveOver K F]
    [HasCanonicalDivisor (K := K) (F := F)] [∀ v : Place K F, v.DCoordGenerates]
    [HasCanonicalLocalResidueKStar K F]
    (hC : ConstantsAreBase K F) (hRT : ResidueTheorem K F)
    {S₀ S₁ : Set (Place K F)} (hcover : S₀ ∪ S₁ = Set.univ) (h₀ : ∃ v, v ∉ S₀) (h₁ : ∃ v, v ∉ S₁) :
    Function.Bijective (serrePairing hRT hcover) ∧
      Function.Bijective (serrePairing hRT hcover).flip :=
  promotion_serrePairing_bijective_and_flip_bijective hC hRT hcover h₀ h₁

/-- A-class: adelic Weil duality over algebraically closed K (COMPLETE ported proof). -/
theorem ag14_weilDualityAdelic_of_isAlgClosed
    {K F : Type*} [Field K] [IsAlgClosed K] [DecidableEq (RatFunc K)]
    [Field F] [Algebra K F]
    [HasCanonicalDivisor (K := K) (F := F)]
    [∀ w : Place K F, w.DCoordGenerates]
    [Algebra (RatFunc K) F] [IsScalarTower K (RatFunc K) F]
    [Algebra.IsIntegral (RatFunc K) F] [Module.Finite (RatFunc K) F]
    [HasLocalResidue K F]
    [∀ w : Place K F, w.FiniteResidue]
    [Nontrivial Ω[F⁄K]]
    [IsCurveOver K F] [IsCurveOver K (RatFunc K)]
    [∀ u : Place K (RatFunc K), u.FiniteResidue]
    [HasCanonicalLocalResidueKStar K F]
    [HasPrincipalDivisors K F] [Algebra.IsSeparable (RatFunc K) F]
    [Nontrivial Ω[(RatFunc K)⁄K]] [∀ v : Place K (RatFunc K), v.DCoordGenerates]
    [FiniteDimensional (RatFunc K) F] [HasSeparableResidue K F] :
    WeilDualityAdelic K F :=
  promotion_weilDualityAdelic_of_isAlgClosed

/-- A-class: Cech Riemann-Roch at reached genus (COMPLETE ported proof). -/
theorem ag14_cechRiemannRoch_of_genusReached
    {K F : Type*} [Field K] [Field F] [Algebra K F] [IsCurveOver K F]
    [FiniteDimensional K ↥(LSpace (0 : Divisor K F))]
    {γ : ℤ} {D₀ : Divisor K F} (h : RiemannGenusReachedAt γ D₀)
    {S₀ S₁ : Set (Place K F)} (hcover : S₀ ∪ S₁ = Set.univ) (h₀ : ∃ v, v ∉ S₀) (h₁ : ∃ v, v ∉ S₁)
    (D : Divisor K F) :
    FiniteDimensional K ↥(cechH0 S₀ S₁ D) ∧ Module.Finite K (cechH1 S₀ S₁ D) ∧
      Module.finrank K ↥(cechH0 S₀ S₁ D) = ell D ∧
      Module.finrank K (cechH1 S₀ S₁ D) = indexOfSpecialty D ∧
      (Module.finrank K ↥(cechH0 S₀ S₁ D) : ℤ) - Module.finrank K (cechH1 S₀ S₁ D)
        = Divisor.degree D + 1 - γ ∧
      (D₀ ≤ D → Subsingleton (cechH1 S₀ S₁ D)) :=
  promotion_cechRiemannRoch_of_genusReached h hcover h₀ h₁ D

/-- A-class reuse record. -/
def ag14Reuse : List (String × String × String) :=
  [ ("Serre pairing + flip bijective", "AG_FLT_ProvedTheoremsPromotionActual.promotion_serrePairing_bijective_and_flip_bijective", "A (COMPLETE ported proof; conditional on hC/hRT/cover rows)"),
    ("WeilDualityAdelic over alg. closed K", "promotion_weilDualityAdelic_of_isAlgClosed", "A (COMPLETE ported proof)"),
    ("Cech Riemann-Roch at reached genus", "promotion_cechRiemannRoch_of_genusReached", "A (COMPLETE ported proof; conditional on genus-reached row)"),
    ("consumers", "GeomCore / AG06b RR reductions / AG10/AG11 Serde-genus layers", "A (reuse)") ]

end LeanFormal.IUT.XiFPaper.AG14ProvedTheoremsConsumerActual

end
