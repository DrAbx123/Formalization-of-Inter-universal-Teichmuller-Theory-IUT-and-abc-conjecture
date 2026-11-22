import tmp.external.ported.flt_core.P2M.Sol.S_AlgebraicCurve_serrePairing_bijective_and_flip_bijective
import tmp.external.ported.flt_core.P2M.Sol.S_AlgebraicCurve_weilDualityAdelic_of_isAlgClosed
import tmp.external.ported.flt_core.P2M.Sol.S_AlgebraicCurve_cechRiemannRoch_of_genusReached

/-!
# AG-FLT proved-theorems promotion (first-class importable; audit component)

COMPONENT, not a paper object.  Named consumers: stepxi GeometricCore, stage4,
Lead AG-INFRA-PLAN.  Ported assets, Apache-2.0 attribution in ported headers.

Re-exports the three serially-compiled (EXIT=0; oleans on disk) FLT theorem
results with their exact statements (complete ported proofs; source grep
sorry/axiom = 0):
* Serre pairing and its flip are bijective;
* adelic Weil duality over algebraically closed K;
* Cech Riemann-Roch at reached genus.
No axiom/fake data added here; the proof terms are the ported solutions.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 0

namespace LeanFormal.IUT.XiFPaper.AG_FLT_ProvedTheoremsPromotionActual

open AlgebraicCurve KaehlerDifferential

/-- COMPLETE PROOF (ported): Serre pairing and its flip are bijective. -/
theorem promotion_serrePairing_bijective_and_flip_bijective
    {K : Type*} {F : Type*} [Field K] [Field F] [Algebra K F]
    [PerfectField K] [Algebra.EssFiniteType K F] [IsCurveOver K F]
    [HasCanonicalDivisor (K := K) (F := F)] [∀ v : Place K F, v.DCoordGenerates]
    [HasCanonicalLocalResidueKStar K F]
    (hC : ConstantsAreBase K F) (hRT : ResidueTheorem K F)
    {S₀ S₁ : Set (Place K F)} (hcover : S₀ ∪ S₁ = Set.univ) (h₀ : ∃ v, v ∉ S₀) (h₁ : ∃ v, v ∉ S₁) :
    Function.Bijective (serrePairing hRT hcover) ∧
      Function.Bijective (serrePairing hRT hcover).flip :=
  P2MW.S_AlgebraicCurve_serrePairing_bijective_and_flip_bijective.solution hC hRT hcover h₀ h₁

/-- COMPLETE PROOF (ported): adelic Weil duality over algebraically closed K. -/
theorem promotion_weilDualityAdelic_of_isAlgClosed
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
  P2MW.S_AlgebraicCurve_weilDualityAdelic_of_isAlgClosed.solution

/-- COMPLETE PROOF (ported): Cech Riemann-Roch at reached genus. -/
theorem promotion_cechRiemannRoch_of_genusReached
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
  P2MW.S_AlgebraicCurve_cechRiemannRoch_of_genusReached.solution h hcover h₀ h₁ D

end LeanFormal.IUT.XiFPaper.AG_FLT_ProvedTheoremsPromotionActual
