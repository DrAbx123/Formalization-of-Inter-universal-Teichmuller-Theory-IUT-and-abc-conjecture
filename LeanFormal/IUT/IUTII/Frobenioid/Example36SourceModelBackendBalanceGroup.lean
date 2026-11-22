import LeanFormal.IUT.IUTII.Frobenioid.Example36SourceModelBackendBalance

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

/-!
# The backend divisor balance in the group completion of the effective cone

`Example36SourceModelBackendBalance` proves the backend balance identity

  n d(J₁) + Z = d(J₂) + div(f)

in the explicit divisor group `ExplicitDivisor F`, where `Z` is the effective
part (an arbitrary-sign explicit divisor).  This file supplies the
`Algebra.GrothendieckAddGroup (EffectiveDivisor F)` wrapper: it builds the
effective cone element `Z_+` from the nonnegative part of `Z`
(`Int.toNat` at finite places, `Real.toNNReal` at archimedean places), proves
that the canonical inclusion `effectiveToExplicit` sends `Z_+` to the explicit
effective part, and then transports the explicit balance identity across the
group-completion equivalence `coneGrothendieckEquiv`, using the frozen backend
agreement lemmas for `idealFamilyDivisorClass`, `of` and `globalModelDivisor`.

The result is the balance identity in the group completion:

  n • idealFamilyDivisorClass J₁ + of Z_+ = idealFamilyDivisorClass J₂ + globalModelDivisor f.

This is the arithmetic-divisor rewriting used by the model Frobenioid, stated
for the actual number-field place data (the case in which the effective part of
a morphism is a genuine nonnegative effective divisor).

Boundary: divisor-group coordinates and place data only; no source Hodge
theater, theta-pilot or q-pilot claim.
-/

noncomputable section

namespace LeanFormal.IUT.IUTII.Frobenioid
namespace Example36

open IsDedekindDomain NumberField
open scoped NumberField

universe u

variable {F : Type u} [Field F] [NumberField F]

namespace SourceModelBackendBalanceGroup

/-- The finite part of the nonnegative cone element: `Int.toNat` of the
finite coordinates, supported on the finite support of the effective part. -/
def effectivePartConeFinite (D : GlobalPlaceData F) (hD : D.HasFiniteSupport)
    {J₁ J₂ : GlobalIdealFamily F} (h : GlobalIdealFamily.Hom D J₁ J₂) :
    HeightOneSpectrum (𝓞 F) →₀ ℕ :=
  Finsupp.onFinset (SourceModelBackendBalance.effectivePartFiniteSupport D hD h)
    (fun v => (h.effectiveFinite v).toNat)
    (fun v hv => by
      by_contra hmem
      have hzero := SourceModelBackendBalance.effectiveFinite_eq_zero_of_not_mem
        D hD h hmem
      exact hv (by rw [hzero]; rfl))

/-- The finite coordinate of the nonnegative cone element. -/
@[simp]
theorem effectivePartConeFinite_apply (D : GlobalPlaceData F) (hD : D.HasFiniteSupport)
    {J₁ J₂ : GlobalIdealFamily F} (h : GlobalIdealFamily.Hom D J₁ J₂)
    (v : HeightOneSpectrum (𝓞 F)) :
    effectivePartConeFinite D hD h v = (h.effectiveFinite v).toNat :=
  Finsupp.onFinset_apply

/-- The effective cone element obtained from the nonnegative part of the
effective part of a morphism: `Int.toNat` of the finite coordinates and
`Real.toNNReal` of the archimedean coordinates, with the finite support of the
effective part. -/
def effectivePartCone (D : GlobalPlaceData F) (hD : D.HasFiniteSupport)
    {J₁ J₂ : GlobalIdealFamily F} (h : GlobalIdealFamily.Hom D J₁ J₂) :
    SourceModelBackend.EffectiveDivisor F :=
  (effectivePartConeFinite D hD h, fun w => (h.effectiveInfinite w).toNNReal)

/-- The finite coordinate of the nonnegative cone element. -/
@[simp]
theorem effectivePartCone_fst_apply (D : GlobalPlaceData F) (hD : D.HasFiniteSupport)
    {J₁ J₂ : GlobalIdealFamily F} (h : GlobalIdealFamily.Hom D J₁ J₂)
    (v : HeightOneSpectrum (𝓞 F)) :
    (effectivePartCone D hD h).1 v = (h.effectiveFinite v).toNat := by
  exact effectivePartConeFinite_apply D hD h v

/-- The archimedean coordinate of the nonnegative cone element. -/
@[simp]
theorem effectivePartCone_snd_apply (D : GlobalPlaceData F) (hD : D.HasFiniteSupport)
    {J₁ J₂ : GlobalIdealFamily F} (h : GlobalIdealFamily.Hom D J₁ J₂)
    (w : NumberField.InfinitePlace F) :
    (effectivePartCone D hD h).2 w = (h.effectiveInfinite w).toNNReal := rfl

/-- For the actual number-field place data, the nonnegative cone element maps
under the inclusion to the explicit effective part `Z = effectiveDivisorOfHom`.
This is the coercion lemma which makes the group-completion wrapper possible. -/
theorem numberField_effectiveToExplicit_effectivePartCone
    {J₁ J₂ : GlobalIdealFamily F}
    (h : GlobalIdealFamily.Hom (numberFieldGlobalPlaceData (F := F)) J₁ J₂) :
    SourceModelBackend.effectiveToExplicit
        (effectivePartCone (numberFieldGlobalPlaceData (F := F))
          numberFieldGlobalPlaceData_hasFiniteSupport h) =
      SourceModelBackendBalance.effectiveDivisorOfHom
        (numberFieldGlobalPlaceData (F := F))
        numberFieldGlobalPlaceData_hasFiniteSupport h := by
  apply Prod.ext
  · ext v
    rw [SourceModelBackend.effectiveToExplicit_fst_apply,
      effectivePartCone_fst_apply]
    show (((h.effectiveFinite v).toNat : ℕ) : ℤ) =
      (SourceModelBackendBalance.effectivePartFinite
        (numberFieldGlobalPlaceData (F := F))
        numberFieldGlobalPlaceData_hasFiniteSupport h) v
    rw [SourceModelBackendBalance.effectivePartFinite_apply]
    have hv : (0 : ℤ) ≤ h.effectiveFinite v := by
      have hc := h.effectiveFinite_mem_cone v
      simpa [numberFieldGlobalPlaceData, numberFieldFiniteLocalValueData,
        integerNonnegCone] using hc
    exact Int.toNat_of_nonneg hv
  · funext w
    rw [SourceModelBackend.effectiveToExplicit_snd_apply,
      effectivePartCone_snd_apply]
    have hw : (0 : ℝ) ≤ h.effectiveInfinite w := by
      have hc := h.effectiveInfinite_mem_cone w
      simpa [numberFieldGlobalPlaceData, numberFieldInfiniteLocalValueData,
        realNonnegCone] using hc
    exact Real.coe_toNNReal _ hw

/-- The image under the group-completion equivalence of the nonnegative cone
element is the explicit effective part. -/
theorem coneGrothendieckEquiv_effectivePartCone
    {J₁ J₂ : GlobalIdealFamily F}
    (h : GlobalIdealFamily.Hom (numberFieldGlobalPlaceData (F := F)) J₁ J₂) :
    SourceModelBackend.coneGrothendieckEquiv
        (Algebra.GrothendieckAddGroup.of
          (effectivePartCone (numberFieldGlobalPlaceData (F := F))
            numberFieldGlobalPlaceData_hasFiniteSupport h)) =
      SourceModelBackendBalance.effectiveDivisorOfHom
        (numberFieldGlobalPlaceData (F := F))
        numberFieldGlobalPlaceData_hasFiniteSupport h := by
  rw [SourceModelBackend.coneGrothendieckEquiv_of,
    numberField_effectiveToExplicit_effectivePartCone]

/-- The explicit principal divisor of the place data agrees with the backend
principal divisor map `globalModelDivisor` (in explicit coordinates). -/
theorem principalDivisorOfPlaceData_eq_principalDivisorExplicit (f : Fˣ) :
    SourceModelBackendBalance.principalDivisorOfPlaceData
        (numberFieldGlobalPlaceData (F := F))
        numberFieldGlobalPlaceData_hasFiniteSupport f =
      SourceModelBackend.principalDivisorExplicit (Additive.ofMul f) := by
  apply Prod.ext
  · ext v
    rw [SourceModelBackendBalance.principalDivisorOfPlaceData_fst_apply]
    show (numberFieldGlobalPlaceData (F := F)).finiteDelta f v =
      (SourceModelBackend.principalDivisorExplicit (Additive.ofMul f)).1 v
    rw [show (SourceModelBackend.principalDivisorExplicit (Additive.ofMul f)).1 =
        principalDivisorFinite f from rfl]
    exact (principalDivisorFinite_apply_eq_finiteDelta f v).symm
  · funext w
    rw [SourceModelBackendBalance.principalDivisorOfPlaceData_snd_apply]
    show (numberFieldGlobalPlaceData (F := F)).infiniteDelta f w =
      (SourceModelBackend.principalDivisorExplicit (Additive.ofMul f)).2 w
    rw [show (SourceModelBackend.principalDivisorExplicit (Additive.ofMul f)).2 =
        fun w => principalDivisorInfinite f w from rfl]
    exact (principalDivisorInfinite_apply_eq_infiniteDelta f w).symm

/-- The image of `globalModelDivisor` under the group-completion equivalence
is the explicit principal divisor map. -/
theorem coneGrothendieckEquiv_globalModelDivisor (u : Additive Fˣ) :
    SourceModelBackend.coneGrothendieckEquiv (F := F)
        (SourceModelBackend.globalModelDivisor (F := F) u) =
      SourceModelBackend.principalDivisorExplicit u := by
  rw [SourceModelBackend.globalModelDivisor, AddMonoidHom.comp_apply]
  change SourceModelBackend.coneGrothendieckEquiv (F := F)
      ((SourceModelBackend.coneGrothendieckEquiv (F := F)).symm
        (SourceModelBackend.principalDivisorExplicit u)) = _
  exact AddEquiv.apply_symm_apply _ _

/-- **Group-completion form of the backend balance identity.**  For a morphism
`h : Hom numberFieldGlobalPlaceData J₁ J₂` of degree `n` and multiplier `f`,
with `Z_+` the effective cone element of the nonnegative part of the effective
part, the balance identity holds in the group completion of the effective
divisor cone:

  n • idealFamilyDivisorClass J₁ + of Z_+ = idealFamilyDivisorClass J₂ + globalModelDivisor f.

It is obtained by applying `coneGrothendieckEquiv.injective` to the explicit
balance `backendBalanceEquation` and rewriting the three images with the backend
agreement lemmas. -/
theorem backendBalanceEquation_of_effectivePartCone
    {J₁ J₂ : GlobalIdealFamily F}
    (h : GlobalIdealFamily.Hom (numberFieldGlobalPlaceData (F := F)) J₁ J₂) :
    (h.degree : ℕ) • SourceModelBackend.idealFamilyDivisorClass (F := F) J₁ +
        Algebra.GrothendieckAddGroup.of
          (effectivePartCone (numberFieldGlobalPlaceData (F := F))
            numberFieldGlobalPlaceData_hasFiniteSupport h) =
      SourceModelBackend.idealFamilyDivisorClass (F := F) J₂ +
        SourceModelBackend.globalModelDivisor (F := F)
          (Additive.ofMul h.multiplier) := by
  apply SourceModelBackend.coneGrothendieckEquiv.injective
  have hL : SourceModelBackend.coneGrothendieckEquiv (F := F)
      ((h.degree : ℕ) • SourceModelBackend.idealFamilyDivisorClass (F := F) J₁ +
        Algebra.GrothendieckAddGroup.of
          (effectivePartCone (numberFieldGlobalPlaceData (F := F))
            numberFieldGlobalPlaceData_hasFiniteSupport h)) =
      (h.degree : ℕ) • arithmeticDivisorExplicit J₁ +
        SourceModelBackend.effectiveToExplicit
          (effectivePartCone (numberFieldGlobalPlaceData (F := F))
            numberFieldGlobalPlaceData_hasFiniteSupport h) := by
    rw [map_add, map_nsmul,
      show SourceModelBackend.coneGrothendieckEquiv (F := F)
        (SourceModelBackend.idealFamilyDivisorClass (F := F) J₁) =
          arithmeticDivisorExplicit J₁ from by
        rw [SourceModelBackend.idealFamilyDivisorClass]
        exact AddEquiv.apply_symm_apply _ _,
      SourceModelBackend.coneGrothendieckEquiv_of]
  have hR : SourceModelBackend.coneGrothendieckEquiv (F := F)
      (SourceModelBackend.idealFamilyDivisorClass (F := F) J₂ +
        SourceModelBackend.globalModelDivisor (F := F)
          (Additive.ofMul h.multiplier)) =
      arithmeticDivisorExplicit J₂ +
        SourceModelBackend.principalDivisorExplicit (Additive.ofMul h.multiplier) := by
    rw [map_add,
      show SourceModelBackend.coneGrothendieckEquiv (F := F)
        (SourceModelBackend.idealFamilyDivisorClass (F := F) J₂) =
          arithmeticDivisorExplicit J₂ from by
        rw [SourceModelBackend.idealFamilyDivisorClass]
        exact AddEquiv.apply_symm_apply _ _]
    exact congrArg (fun x => arithmeticDivisorExplicit J₂ + x)
      (coneGrothendieckEquiv_globalModelDivisor (Additive.ofMul h.multiplier))
  rw [hL, hR, numberField_effectiveToExplicit_effectivePartCone,
    ← principalDivisorOfPlaceData_eq_principalDivisorExplicit]
  exact SourceModelBackendBalance.backendBalanceEquation
    (numberFieldGlobalPlaceData (F := F))
    numberFieldGlobalPlaceData_hasFiniteSupport h

end SourceModelBackendBalanceGroup

end Example36
end LeanFormal.IUT.IUTII.Frobenioid