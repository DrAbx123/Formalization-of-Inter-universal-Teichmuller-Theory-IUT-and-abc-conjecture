import tmp.sheaf.xif.paper.AG_FLT_ProvedTheoremsPromotionActual

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 2000000

noncomputable section

/-!
# STEP 0 prior-art: RR|Serre|Weil duality|Cech|GeometricCore -> hits AG_FLT_ProvedTheoremsPromotionActual (CITABLE 3 decls: promotion_serrePairing_bijective_and_flip_bijective / promotion_weilDualityAdelic_of_isAlgClosed / promotion_cechRiemannRoch_of_genusReached = COMPLETE ported proofs) -> REUSE (real RR/duality content for GeometricCore; consumed as first-class theorems).

# [GenEll] 15b: GeometricCore RR/Serde/Cech consumption (COMPLETE ported proofs)

Companion of GenEll15GeometricCoreAssemblyActual (kept separate because the ported
flt_core namespace duplicates the flt_test namespace used by the finite-map
skeleton file: importing both in one file clashes).
TASK (Lead): consume the three promotion theorems as the REAL RR/duality content
for GeometricCore instead of named hypotheses.  Every theorem below is a
re-export of the complete ported proof; no new axiom/fake data.
Registry frozen 14041.
-/

namespace LeanFormal.IUT.XiFPaper.GenEll15bRRConsumptionActual

open LeanFormal.IUT.XiFPaper.AG_FLT_ProvedTheoremsPromotionActual
open AlgebraicCurve KaehlerDifferential

/-- **Serre pairing (COMPLETE ported proof):** the Serre pairing and its flip are
bijective. -/
theorem genEll15b_serrePairing
    {K : Type*} {F : Type*} [Field K] [Field F] [Algebra K F]
    [PerfectField K] [Algebra.EssFiniteType K F] [IsCurveOver K F]
    [HasCanonicalDivisor (K := K) (F := F)] [∀ v : Place K F, v.DCoordGenerates]
    [HasCanonicalLocalResidueKStar K F]
    (hC : ConstantsAreBase K F) (hRT : ResidueTheorem K F)
    {S₀ S₁ : Set (Place K F)} (hcover : S₀ ∪ S₁ = Set.univ)
    (h₀ : ∃ v, v ∉ S₀) (h₁ : ∃ v, v ∉ S₁) :
    Function.Bijective (serrePairing hRT hcover) ∧
      Function.Bijective (serrePairing hRT hcover).flip :=
  promotion_serrePairing_bijective_and_flip_bijective hC hRT hcover h₀ h₁

/-- **Adelic Weil duality (COMPLETE ported proof)** over algebraically closed K. -/
theorem genEll15b_weilDualityAdelic
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

/-- **Cech Riemann-Roch at reached genus (COMPLETE ported proof).** -/
theorem genEll15b_cechRiemannRoch
    {K F : Type*} [Field K] [Field F] [Algebra K F] [IsCurveOver K F]
    [FiniteDimensional K ↥(LSpace (0 : Divisor K F))]
    {γ : ℤ} {D₀ : Divisor K F} (h : RiemannGenusReachedAt γ D₀)
    {S₀ S₁ : Set (Place K F)} (hcover : S₀ ∪ S₁ = Set.univ)
    (h₀ : ∃ v, v ∉ S₀) (h₁ : ∃ v, v ∉ S₁)
    (D : Divisor K F) :
    FiniteDimensional K ↥(cechH0 S₀ S₁ D) ∧ Module.Finite K (cechH1 S₀ S₁ D) ∧
      Module.finrank K ↥(cechH0 S₀ S₁ D) = ell D ∧
      Module.finrank K (cechH1 S₀ S₁ D) = indexOfSpecialty D ∧
      (Module.finrank K ↥(cechH0 S₀ S₁ D) : ℤ) - Module.finrank K (cechH1 S₀ S₁ D)
        = Divisor.degree D + 1 - γ ∧
      (D₀ ≤ D → Subsingleton (cechH1 S₀ S₁ D)) :=
  promotion_cechRiemannRoch_of_genusReached h hcover h₀ h₁ D

/-- Consumption rows for the GeometricCore RR/duality content. -/
def genEll15bRows : List (String × String) :=
  [ ("Serre pairing + flip bijective", "CONSUMED from AG_FLT promotion (COMPLETE ported proof); genEll15b_serrePairing")
  , ("adelic Weil duality over alg-closed K", "CONSUMED from AG_FLT promotion (COMPLETE ported proof); genEll15b_weilDualityAdelic")
  , ("Cech RR at reached genus", "CONSUMED from AG_FLT promotion (COMPLETE ported proof); genEll15b_cechRiemannRoch")
  , ("remaining GeometricCore gap", "finite-map existence + paper hypotheses/conditions (GenEll15GeometricCoreAssemblyActual rows); Belyi assets port pending qpilot") ]

/-- The RR consumption row record has four rows. -/
theorem genEll15bRows_length : genEll15bRows.length = 4 := rfl

#check genEll15b_serrePairing
#check genEll15b_weilDualityAdelic
#check genEll15b_cechRiemannRoch
#check genEll15bRows_length

end LeanFormal.IUT.XiFPaper.GenEll15bRRConsumptionActual
end