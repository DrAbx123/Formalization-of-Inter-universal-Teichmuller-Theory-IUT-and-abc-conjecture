/-
  Conditional source Psi^cns consumer: packages the actual infinite-place
  log/kernel consumer together with the exact source residual terms.

  The data are conditional on an explicit `SourcePsiCnsTerms`; no inhabitant
  of the residual is constructed or assumed.  The completion-level part is
  the actual green infinite-place log/kernel dictionary; the source part is
  the exact theta divisor/degree, global normalization and Galois-invariance
  data stated over the actual Definition 3.1 contract.
-/
import LeanFormal.IUT.IUTI.InitialTheta.SourceDefinition31Boundary
import LeanFormal.IUT.IUTII.Frobenioid.Example36ArchimedeanLocal
import Mathlib.NumberTheory.NumberField.Completion.InfinitePlace
import Mathlib.Tactic

open scoped BigOperators

set_option relaxedAutoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

noncomputable section

namespace LeanFormal.IUT.InfinitePlaceLogCompletion

open NumberField.InfinitePlace
open NumberField.InfinitePlace.Completion
open LeanFormal.IUT

universe u

variable {F : Type u} [Field F] [NumberField F]

/-- The actual archimedean local field at an infinite place. -/
abbrev InfinitePlaceLocalField (v : NumberField.InfinitePlace F) : Type u :=
  v.Completion

/-- The production archimedean closed ball of radius r. -/
def infinitePlaceRadius (v : NumberField.InfinitePlace F) (r : ℝ) :
    Set (InfinitePlaceLocalField v) :=
  localClosedBall (InfinitePlaceLocalField v) r

/-- The actual radius-realization property of the infinite-place completion. -/
theorem infinitePlace_radiusRealization (v : NumberField.InfinitePlace F) :
    RadiusRealization (InfinitePlaceLocalField v) := by
  intro r hr
  rcases isReal_or_isComplex v with hv | hv
  · let e := NumberField.InfinitePlace.Completion.isometryEquivRealOfIsReal hv
    obtain ⟨y, hy⟩ := radiusRealization_real r hr
    refine ⟨e.symm y, ?_⟩
    rw [← hy]
    have h0 : e 0 = 0 := by
      dsimp [e]
      exact (NumberField.InfinitePlace.Completion.ringEquivRealOfIsReal hv).map_zero
    have hd := e.isometry.dist_eq (e.symm y) 0
    rw [e.apply_symm_apply, h0, dist_eq_norm, sub_zero, dist_eq_norm, sub_zero] at hd
    exact hd.symm
  · let e := NumberField.InfinitePlace.Completion.isometryEquivComplexOfIsComplex hv
    obtain ⟨y, hy⟩ := radiusRealization_complex r hr
    refine ⟨e.symm y, ?_⟩
    rw [← hy]
    have h0 : e 0 = 0 := by
      dsimp [e]
      exact (NumberField.InfinitePlace.Completion.ringEquivComplexOfIsComplex hv).map_zero
    have hd := e.isometry.dist_eq (e.symm y) 0
    rw [e.apply_symm_apply, h0, dist_eq_norm, sub_zero, dist_eq_norm, sub_zero] at hd
    exact hd.symm

/-- The production kernel of the archimedean log: norm-one units. -/
def infinitePlaceKernel (v : NumberField.InfinitePlace F) :
    Subgroup (InfinitePlaceLocalField v)ˣ :=
  normOneUnits (InfinitePlaceLocalField v)

/-- The production additive archimedean log. -/
def infinitePlaceLog (v : NumberField.InfinitePlace F) :
    Additive (InfinitePlaceLocalField v)ˣ →+ ℝ :=
  absLogAddHom (InfinitePlaceLocalField v)

/-- Kernel description: a unit has zero log exactly when it lies in the
norm-one kernel. -/
theorem infinitePlaceLog_eq_zero_iff (v : NumberField.InfinitePlace F)
    (u : (InfinitePlaceLocalField v)ˣ) :
    infinitePlaceLog v (Additive.ofMul u) = 0 ↔
      u ∈ infinitePlaceKernel v := by
  simpa [infinitePlaceLog, infinitePlaceKernel] using
    (absLogAddHom_ofMul_eq_zero_iff (K := InfinitePlaceLocalField v) u)

/-- The actual archimedean log is onto the real line; this uses the actual
radius realization above. -/
theorem infinitePlaceLog_surjective (v : NumberField.InfinitePlace F) :
    Function.Surjective (infinitePlaceLog v) :=
  absLogAddHom_surjective (K := InfinitePlaceLocalField v)
    (infinitePlace_radiusRealization v)

/-- Partial `Psi^cns` carrier at the infinite place: the completion-level
additive log.  This is the actual partial piece; it is not the full source map. -/
def infinitePlacePsiCnsPartial (v : NumberField.InfinitePlace F) :
    Additive (InfinitePlaceLocalField v)ˣ →+ ℝ :=
  infinitePlaceLog v

theorem infinitePlacePsiCnsPartial_eq_log (v : NumberField.InfinitePlace F) :
    infinitePlacePsiCnsPartial v = infinitePlaceLog v := rfl

/-- Radius dictionary: under actual radius realization, closed balls with
nonnegative radii determine and are determined by the radius. -/
theorem infinitePlaceRadius_eq_iff (v : NumberField.InfinitePlace F)
    {r₁ r₂ : ℝ} (h₁ : 0 ≤ r₁) (h₂ : 0 ≤ r₂) :
    infinitePlaceRadius v r₁ = infinitePlaceRadius v r₂ ↔ r₁ = r₂ :=
  localClosedBall_eq_iff (infinitePlace_radiusRealization v) h₁ h₂


/-- Consumer package for the actual infinite-place log/kernel dictionary. -/
structure InfinitePlaceLogConsumerData (v : NumberField.InfinitePlace F) where
  radius : ℝ → Set (InfinitePlaceLocalField v)
  radius_realization : RadiusRealization (InfinitePlaceLocalField v)
  kernel : Subgroup (InfinitePlaceLocalField v)ˣ
  log : Additive (InfinitePlaceLocalField v)ˣ →+ ℝ
  log_kernel : ∀ u : (InfinitePlaceLocalField v)ˣ,
    log (Additive.ofMul u) = 0 ↔ u ∈ kernel
  log_surjective : Function.Surjective log
  psiCnsPartial : Additive (InfinitePlaceLocalField v)ˣ →+ ℝ
  psiCnsPartial_eq_log : psiCnsPartial = log

/-- Constructor packaging the actual infinite-place log/kernel dictionary. -/
def infinitePlaceLogConsumer (v : NumberField.InfinitePlace F) :
    InfinitePlaceLogConsumerData v where
  radius := infinitePlaceRadius v
  radius_realization := infinitePlace_radiusRealization v
  kernel := infinitePlaceKernel v
  log := infinitePlaceLog v
  log_kernel := infinitePlaceLog_eq_zero_iff v
  log_surjective := infinitePlaceLog_surjective v
  psiCnsPartial := infinitePlacePsiCnsPartial v
  psiCnsPartial_eq_log := infinitePlacePsiCnsPartial_eq_log v

end LeanFormal.IUT.InfinitePlaceLogCompletion

namespace LeanFormal.IUT.InfinitePlacePsiCnsSourceTerms

open LeanFormal.IUT Theorem311Source

universe u

variable {l : PrimeGeFive}

/-- The actual integral-unit group of the source field F: units of its ring of
integers.  This is a concrete existing group, not a placeholder carrier. -/
abbrev SourceIntegralUnits (S : SourceDefinition31Data l) : Type u :=
  (NumberField.RingOfIntegers S.arithmetic.F)ˣ

/-- The archimedean logarithm of a source integral unit at an infinite place. -/
def sourceIntegralUnitLog (S : SourceDefinition31Data l)
    (w : NumberField.InfinitePlace S.arithmetic.F) (u : SourceIntegralUnits S) : ℝ :=
  Real.log (w ((u : NumberField.RingOfIntegers S.arithmetic.F) : S.arithmetic.F))

/-- The source theta divisor, as integer coefficients on the actual infinite
places of F.  The degree is the weighted sum with local multiplicities. -/
abbrev SourceThetaDivisor (S : SourceDefinition31Data l) : Type u :=
  NumberField.InfinitePlace S.arithmetic.F → ℤ

def sourceThetaDegree (S : SourceDefinition31Data l) (D : SourceThetaDivisor S) : ℤ :=
  ∑ w : NumberField.InfinitePlace S.arithmetic.F,
    (NumberField.InfinitePlace.mult w : ℤ) * D w

/-- Exact global product-formula normalization required of source integral units. -/
def sourceGlobalNormalization (S : SourceDefinition31Data l)
    (u : SourceIntegralUnits S) : Prop :=
  ∑ w : NumberField.InfinitePlace S.arithmetic.F,
    (NumberField.InfinitePlace.mult w : ℝ) * sourceIntegralUnitLog S w u = 0

/-- Exact Galois invariance required of the source theta divisor, under the
actual Galois group of F over the base field Fmod. -/
def sourceGaloisInvariant (S : SourceDefinition31Data l)
    (D : SourceThetaDivisor S) : Prop :=
  ∀ σ : S.arithmetic.F ≃ₐ[S.arithmetic.Fmod] S.arithmetic.F,
    ∀ w : NumberField.InfinitePlace S.arithmetic.F,
      D (w.comap σ.toRingHom) = D w

/-- The missing source Psi^cns data, stated over the actual source contract.
All fields are actual source objects/properties; no arbitrary carrier type. -/
structure SourcePsiCnsTerms (S : SourceDefinition31Data l) where
  /-- The actual integral units used by the source Psi^cns. -/
  integralUnits : Subgroup (SourceIntegralUnits S) := ⊤
  /-- The theta divisor/degree data on the actual infinite places. -/
  thetaDivisor : SourceThetaDivisor S
  thetaDegree : ℤ
  thetaDegree_eq : thetaDegree = sourceThetaDegree S thetaDivisor
  /-- The exact global product-formula normalization. -/
  globalNormalization : ∀ u : SourceIntegralUnits S,
    sourceGlobalNormalization S u
  /-- The exact Galois invariance of the theta divisor. -/
  galoisInvariant : sourceGaloisInvariant S thetaDivisor

/-- The precise residual Prop: an inhabitant would be exactly the missing
source Psi^cns terms above.  No inhabitant is constructed or assumed. -/
def InfinitePlacePsiCnsSourceResidual (S : SourceDefinition31Data l) : Prop :=
  Nonempty (SourcePsiCnsTerms S)

/-- Partial theorem exposing the exact normalization term of a residual datum. -/
theorem sourcePsiCns_globalNormalization (S : SourceDefinition31Data l)
    (T : SourcePsiCnsTerms S) (u : SourceIntegralUnits S) :
    sourceGlobalNormalization S u :=
  T.globalNormalization u

/-- Partial theorem exposing the exact theta-degree term of a residual datum. -/
theorem sourcePsiCns_thetaDegree (S : SourceDefinition31Data l)
    (T : SourcePsiCnsTerms S) :
    T.thetaDegree = sourceThetaDegree S T.thetaDivisor :=
  T.thetaDegree_eq

/-- Partial theorem exposing the exact Galois-invariance term. -/
theorem sourcePsiCns_galoisInvariant (S : SourceDefinition31Data l)
    (T : SourcePsiCnsTerms S) :
    sourceGaloisInvariant S T.thetaDivisor :=
  T.galoisInvariant

end LeanFormal.IUT.InfinitePlacePsiCnsSourceTerms

namespace LeanFormal.IUT.InfinitePlacePsiCnsTermsConsumer

open LeanFormal.IUT.InfinitePlaceLogCompletion
open LeanFormal.IUT.InfinitePlacePsiCnsSourceTerms
open LeanFormal.IUT Theorem311Source

/-- The actual completion-level consumer together with the exact source terms. -/
structure InfinitePlacePsiCnsTermsConsumer
    (S : SourceDefinition31Data l) (v : NumberField.InfinitePlace S.arithmetic.F) where
  /-- Actual completion radius, kernel, log and partial Psi^cns carrier. -/
  completion : InfinitePlaceLogConsumerData v
  /-- The exact source Psi^cns terms (no inhabitant asserted here). -/
  sourceTerms : SourcePsiCnsTerms S

namespace InfinitePlacePsiCnsTermsConsumer

variable {l : PrimeGeFive} {S : SourceDefinition31Data l}
  {v : NumberField.InfinitePlace S.arithmetic.F}
  (C : InfinitePlacePsiCnsTermsConsumer S v)

/-- Projection of the actual completion-level radius/log/kernel carrier. -/
def completionRadiusRealization :
    RadiusRealization (InfinitePlaceLocalField v) :=
  C.completion.radius_realization

/-- Projection of the exact source global-normalization term. -/
def sourceGlobalNormalizationTerm (u : SourceIntegralUnits S) :
    sourceGlobalNormalization S u :=
  C.sourceTerms.globalNormalization u

/-- Projection of the exact source theta-degree equality. -/
def sourceThetaDegreeTerm :
    C.sourceTerms.thetaDegree = sourceThetaDegree S C.sourceTerms.thetaDivisor :=
  C.sourceTerms.thetaDegree_eq

/-- Projection of the exact source Galois-invariance term. -/
def sourceGaloisInvariantTerm :
    sourceGaloisInvariant S C.sourceTerms.thetaDivisor :=
  C.sourceTerms.galoisInvariant

end InfinitePlacePsiCnsTermsConsumer

/-- Conditional constructor: from the exact source terms and the actual
completion point, build the explicit consumer.  The source term is a
hypothesis; the residual is not inhabited here. -/
def infinitePlacePsiCnsTermsConsumerOf (S : SourceDefinition31Data l)
    (T : SourcePsiCnsTerms S) (v : NumberField.InfinitePlace S.arithmetic.F) :
    InfinitePlacePsiCnsTermsConsumer S v where
  completion := infinitePlaceLogConsumer v
  sourceTerms := T

theorem infinitePlacePsiCnsTermsConsumerOf_completion
    (S : SourceDefinition31Data l) (T : SourcePsiCnsTerms S)
    (v : NumberField.InfinitePlace S.arithmetic.F) :
    (infinitePlacePsiCnsTermsConsumerOf S T v).completion =
      infinitePlaceLogConsumer v := rfl

theorem infinitePlacePsiCnsTermsConsumerOf_terms
    (S : SourceDefinition31Data l) (T : SourcePsiCnsTerms S)
    (v : NumberField.InfinitePlace S.arithmetic.F) :
    (infinitePlacePsiCnsTermsConsumerOf S T v).sourceTerms = T := rfl

end LeanFormal.IUT.InfinitePlacePsiCnsTermsConsumer

end