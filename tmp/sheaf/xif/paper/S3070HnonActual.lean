import tmp.sheaf.xif.paper.S3069RangeInclusionActual
import tmp.sheaf.xif.paper.S2809E6FiniteActual
import tmp.sheaf.xif.paper.S3062ChartZPreservationProof
import tmp.sheaf.xif.paper.S2821E37ProjectiveOverActual

noncomputable section
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S3069RangeInclusionActual
open LeanFormal.IUT.XiFPaper.S3068OpenImmersionFactorizationActual
open LeanFormal.IUT.XiFPaper.S3062ChartZPreservationProof
open LeanFormal.IUT.XiFPaper.S2820E37TransitionActual
open LeanFormal.IUT.XiFPaper.S2821E37ProjectiveOverActual
open LeanFormal.IUT.XiFPaper.S2801E37ProjectiveClosure
open LeanFormal.IUT.XiFPaper.S2801D6FaithfulActual
open LeanFormal.IUT.XiFPaper.S2844D6F6BaseChangeActual
open LeanFormal.IUT.XiFPaper.S2847A6ArithmeticActual
open CategoryTheory AlgebraicGeometry CategoryTheory.Limits
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 0

namespace LeanFormal.IUT.XiFPaper.S3070HnonActual

local instance : Fact (Irreducible (Polynomial.X ^ 2 - Polynomial.C (-1) : Polynomial ℚ)) :=
  ⟨gaussianPolynomial_irreducible⟩
local instance : Field S2844D6F6BaseChangeActual.K := S2847A6.fieldF
local instance : NumberField S2844D6F6BaseChangeActual.K := S2847A6.numberFieldF
local instance : DecidableEq S2844D6F6BaseChangeActual.K := Classical.decEq _

theorem S3070_hinf :
    (Spec.map (CommRingCat.ofHom (E37InfinityEval S2844D6F6BaseChangeActual.K)))
        (⊥ : PrimeSpectrum S2844D6F6BaseChangeActual.K) =
      E37InfinityPoint S2844D6F6BaseChangeActual.K := by
  change PrimeSpectrum.comap (E37InfinityEval S2844D6F6BaseChangeActual.K)
    (⊥ : PrimeSpectrum S2844D6F6BaseChangeActual.K) =
      E37InfinityPoint S2844D6F6BaseChangeActual.K
  apply PrimeSpectrum.ext
  change Ideal.comap (E37InfinityEval S2844D6F6BaseChangeActual.K) ⊥ =
    E37InfinityIdeal S2844D6F6BaseChangeActual.K
  rw [← RingHom.ker_eq_comap_bot]

theorem S3070_hfixpt
    (β : S2844D6F6BaseChangeActual.S2844X ⟶ S2844D6F6BaseChangeActual.S2844X)
    (βs : D.glued ⟶ D.glued)
    (hβs : βs = β.left)
    (hfix : S3062InfinityFixed β) :
    βs S3069Infinity = S3069Infinity := by
  let p : PrimeSpectrum S2844D6F6BaseChangeActual.K := ⊥
  have hp := congrArg (fun f => f p) hfix
  rw [← hβs] at hp
  let βs' : S2820E37ProjectiveScheme S2844D6F6BaseChangeActual.K ⟶
      S2820E37ProjectiveScheme S2844D6F6BaseChangeActual.K := βs
  change βs' (S2820E37ChartYMap S2844D6F6BaseChangeActual.K
        ((Spec.map (CommRingCat.ofHom (E37InfinityEval S2844D6F6BaseChangeActual.K))) p)) =
      S2820E37ChartYMap S2844D6F6BaseChangeActual.K
        ((Spec.map (CommRingCat.ofHom (E37InfinityEval S2844D6F6BaseChangeActual.K))) p) at hp
  rw [S3070_hinf] at hp
  change βs' (S2820E37ChartYMap S2844D6F6BaseChangeActual.K
      (E37InfinityPoint S2844D6F6BaseChangeActual.K)) =
    S2820E37ChartYMap S2844D6F6BaseChangeActual.K
      (E37InfinityPoint S2844D6F6BaseChangeActual.K)
  exact hp

theorem S3070_hnon_of_origin
    (β : S2844D6F6BaseChangeActual.S2844X ⟶ S2844D6F6BaseChangeActual.S2844X)
    (βs : D.glued ⟶ D.glued)
    (hβs : βs = β.left)
    (hfix : S3062InfinityFixed β)
    (hsq : βs ≫ βs = 𝟙 D.glued) :
    ∀ x : D.glued, x ≠ S3069Infinity → βs x ≠ S3069Infinity := by
  have hsq_point : ∀ x : D.glued, βs (βs x) = x := by
    intro x
    have h := congrArg (fun f : D.glued ⟶ D.glued => f x) hsq
    simpa using h
  have hfixpt : βs S3069Infinity = S3069Infinity :=
    S3070_hfixpt β βs hβs hfix
  intro x hx hβx
  have h := hsq_point x
  rw [hβx, hfixpt] at h
  exact hx h.symm

/-- Chart-Z factorization from origin-preserving β, β²=1, and hβs. -/
theorem S3070_factorization_of_origin
    (β : S2844D6F6BaseChangeActual.S2844X ⟶ S2844D6F6BaseChangeActual.S2844X)
    (βs : D.glued ⟶ D.glued)
    (hβs : βs = β.left)
    (hβ : β ≫ β = 𝟙 S2844D6F6BaseChangeActual.S2844X)
    (hfix : S3062InfinityFixed β) :
    S3062ChartZFactorization β := by
  have hsq : βs ≫ βs = 𝟙 D.glued := by
    have h := congrArg (fun f => Over.Hom.left f) hβ
    change Over.Hom.left β ≫ Over.Hom.left β =
      𝟙 (S2820E37ProjectiveScheme S2844D6F6BaseChangeActual.K) at h
    rw [← hβs] at h
    exact h
  have hnon := S3070_hnon_of_origin β βs hβs hfix hsq
  exact S3069_factorization_of_range β βs hβs
    (S3069_rangeInclusion_of_beta β βs hβs hβ hnon)

theorem S3070_chartZFactorizationTarget :
    S3062ChartZFactorizationTarget := by
  intro β hβ hfix
  exact S3070_factorization_of_origin β β.left rfl hβ hfix


#check S3070_hinf
#check S3070_factorization_of_origin
#check S3070_chartZFactorizationTarget
#check S3070_hfixpt
#check S3070_hnon_of_origin
#print axioms S3070_hinf
#print axioms S3070_hnon_of_origin
#print axioms S3070_factorization_of_origin
#print axioms S3070_chartZFactorizationTarget

end LeanFormal.IUT.XiFPaper.S3070HnonActual
end
