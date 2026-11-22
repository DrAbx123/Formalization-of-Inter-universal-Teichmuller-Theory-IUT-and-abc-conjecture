import LeanFormal.IUT.IUTII.Frobenioid.Example36TorsorTheory
import LeanFormal.IUT.IUTII.Frobenioid.Example36LocalContraction
import LeanFormal.IUT.IUTII.Frobenioid.Example36GlobalPlaceData
import LeanFormal.IUT.IUTII.Frobenioid.Example36GlobalIdealFamily

/-!
# Torsor presentations of global ideal families (IUT III, Example 3.6, (iii))

Layer 3, second half.  The local torsor points of Example 3.6 live in the
contracted products T_v = Gamma_v x^G T.  This file freezes the presentation
of a torsor object by a global base point t of the G = F^x-torsor T together
with the local value coordinates of the local points relative to t, at all
finite and archimedean places, with the almost-everywhere-standard
finite-support condition.

The main content is the base-point change of the coordinate description:
for a global unit h, the presentation with base point h • t has local
coordinates a_v - delta_v(h).  Consequently a morphism of degree n with
multiplier f between presentations is transported under a change of the two
base points to the multiplier

  f' = h_2^{-1} * f * h_1^n,

and the local integrality expressions are unchanged:

  delta_v(f') + n * a'_1 - a'_2 = delta_v(f) + n * a_1 - a_2.

This is precisely the change-of-base-point computation of the handoff
(chapter 1, G3).  The underlying base-point-free torsor objects and the
two-functor equivalence with global ideal families are in
Example36TorsorEquivalence.

Boundary: the presentation is base-point relative; no statement here claims
that a presentation is canonical.  The local contraction and the support
condition are the ones constructed in Layer 3.
-/

noncomputable section

namespace LeanFormal.IUT.IUTII.Frobenioid
namespace Example36

open scoped NumberField
open IsDedekindDomain NumberField

universe u

variable {F : Type u} [Field F] [NumberField F]

/-- A global torsor presentation of an object of Example 3.6: a G = F^x
torsor T with a chosen base point, local points in the contracted products
T_v at all places, and the finite-support condition relative to the base
point (all but finitely many finite places have the standard local point). -/
structure TorsorPresentation (D : GlobalPlaceData F) where
  /-- The underlying F^x-torsor. -/
  T : GTorsor Fˣ
  /-- The chosen global base point. -/
  base : T.carrier
  /-- The local points at the finite places. -/
  finitePoint : ∀ v : HeightOneSpectrum (𝓞 F), LocalContraction (D.finiteValue v) T
  /-- The local points at the archimedean places. -/
  infinitePoint : ∀ w : NumberField.InfinitePlace F, LocalContraction (D.infiniteValue w) T
  /-- Almost everywhere standard: the finite-place coordinates relative to the
  base point vanish except at finitely many places. -/
  finite_support : Set.Finite
    {v : HeightOneSpectrum (𝓞 F) |
      localCoord (D.finiteValue v) T base (finitePoint v) ≠ 0}

namespace TorsorPresentation

variable {D : GlobalPlaceData F}

/-- The finite-place coordinate of the local point relative to the base point. -/
def finiteCoord (P : TorsorPresentation D) (v : HeightOneSpectrum (𝓞 F)) : ℤ :=
  localCoord (D.finiteValue v) P.T P.base (P.finitePoint v)

/-- The archimedean coordinate of the local point relative to the base point. -/
def infiniteCoord (P : TorsorPresentation D) (w : NumberField.InfinitePlace F) : ℝ :=
  localCoord (D.infiniteValue w) P.T P.base (P.infinitePoint w)

@[simp]
theorem finiteCoord_def (P : TorsorPresentation D) (v : HeightOneSpectrum (𝓞 F)) :
    P.finiteCoord v =
      localCoord (D.finiteValue v) P.T P.base (P.finitePoint v) := rfl

@[simp]
theorem infiniteCoord_def (P : TorsorPresentation D)
    (w : NumberField.InfinitePlace F) :
    P.infiniteCoord w =
      localCoord (D.infiniteValue w) P.T P.base (P.infinitePoint w) := rfl

/-- The finite-support condition in coordinate form. -/
theorem finite_support_coord (P : TorsorPresentation D) :
    Set.Finite {v : HeightOneSpectrum (𝓞 F) | P.finiteCoord v ≠ 0} :=
  P.finite_support

/-- Change of the global base point of a presentation: the underlying torsor and
the local points are unchanged; the base point becomes h • base; the finite
coordinates become a_v - delta_v(h). -/
def rebase (hD : D.HasFiniteSupport) (P : TorsorPresentation D) (h : Fˣ) :
    TorsorPresentation D where
  T := P.T
  base := h • P.base
  finitePoint := P.finitePoint
  infinitePoint := P.infinitePoint
  finite_support := by
    refine Set.Finite.subset
      (Set.Finite.union P.finite_support (hD h)) ?_
    intro v hv
    have hnew : localCoord (D.finiteValue v) P.T (h • P.base) (P.finitePoint v) ≠ 0 := hv
    rw [localCoord_basePoint_change] at hnew
    by_cases hold : P.finiteCoord v = 0
    · by_cases hdel : D.finiteDelta h v = 0
      · have hold' : localCoord (D.finiteValue v) P.T P.base (P.finitePoint v) = 0 := hold
        have hdel' : (D.finiteValue v).deltaAdd h = 0 := hdel
        exact (hnew (by rw [hold', hdel']; simp)).elim
      · exact Or.inr hdel
    · exact Or.inl hold

@[simp]
theorem rebase_base (hD : D.HasFiniteSupport) (P : TorsorPresentation D) (h : Fˣ) :
    (rebase hD P h).base = h • P.base := rfl

@[simp]
theorem rebase_finitePoint (hD : D.HasFiniteSupport) (P : TorsorPresentation D) (h : Fˣ)
    (v : HeightOneSpectrum (𝓞 F)) :
    (rebase hD P h).finitePoint v = P.finitePoint v := rfl

@[simp]
theorem rebase_infinitePoint (hD : D.HasFiniteSupport) (P : TorsorPresentation D) (h : Fˣ)
    (w : NumberField.InfinitePlace F) :
    (rebase hD P h).infinitePoint w = P.infinitePoint w := rfl

/-- Base-point change of the finite coordinates. -/
theorem rebase_finiteCoord (hD : D.HasFiniteSupport) (P : TorsorPresentation D)
    (h : Fˣ) (v : HeightOneSpectrum (𝓞 F)) :
    (rebase hD P h).finiteCoord v = P.finiteCoord v - D.finiteDelta h v := by
  show localCoord (D.finiteValue v) P.T (h • P.base) (P.finitePoint v) =
    P.finiteCoord v - D.finiteDelta h v
  rw [localCoord_basePoint_change]
  rfl

/-- Base-point change of the archimedean coordinates. -/
theorem rebase_infiniteCoord (hD : D.HasFiniteSupport) (P : TorsorPresentation D)
    (h : Fˣ) (w : NumberField.InfinitePlace F) :
    (rebase hD P h).infiniteCoord w = P.infiniteCoord w - D.infiniteDelta h w := by
  show localCoord (D.infiniteValue w) P.T (h • P.base) (P.infinitePoint w) =
    P.infiniteCoord w - D.infiniteDelta h w
  rw [localCoord_basePoint_change]
  rfl

theorem rebase_rebase_finiteCoord (hD : D.HasFiniteSupport) (P : TorsorPresentation D)
    (h₁ h₂ : Fˣ) (v : HeightOneSpectrum (𝓞 F)) :
    (rebase hD (rebase hD P h₁) h₂).finiteCoord v =
      P.finiteCoord v - D.finiteDelta h₁ v - D.finiteDelta h₂ v := by
  rw [rebase_finiteCoord, rebase_finiteCoord]

theorem rebase_rebase_infiniteCoord (hD : D.HasFiniteSupport) (P : TorsorPresentation D)
    (h₁ h₂ : Fˣ) (w : NumberField.InfinitePlace F) :
    (rebase hD (rebase hD P h₁) h₂).infiniteCoord w =
      P.infiniteCoord w - D.infiniteDelta h₁ w - D.infiniteDelta h₂ w := by
  rw [rebase_infiniteCoord, rebase_infiniteCoord]

end TorsorPresentation

/-! ## Degree-n morphisms of torsor presentations -/

/-- A degree-n morphism of torsor presentations: positive degree, a global
multiplier, and the local integrality conditions at all places relative to the
chosen base points.  Under a change of the base points it transforms by
f' = h_2^{-1} * f * h_1^n (proved below). -/
structure TorsorArrow {D : GlobalPlaceData F} (P₁ P₂ : TorsorPresentation D) where
  /-- The positive integer degree. -/
  degree : ℕ
  /-- The degree is positive. -/
  positive_degree : 0 < degree
  /-- The global multiplier f in F^x. -/
  multiplier : Fˣ
  /-- The finite-place integrality conditions. -/
  finite_incl : ∀ v : HeightOneSpectrum (𝓞 F),
    (D.finiteValue v).localInclusion degree multiplier (P₁.finiteCoord v) (P₂.finiteCoord v)
  /-- The archimedean integrality conditions. -/
  infinite_incl : ∀ w : NumberField.InfinitePlace F,
    (D.infiniteValue w).localInclusion degree multiplier (P₁.infiniteCoord w) (P₂.infiniteCoord w)

namespace TorsorArrow

variable {D : GlobalPlaceData F} {P₁ P₂ P₃ P₄ : TorsorPresentation D}

@[ext]
theorem ext {φ ψ : TorsorArrow P₁ P₂} (hdeg : φ.degree = ψ.degree)
    (hmult : φ.multiplier = ψ.multiplier) : φ = ψ := by
  cases φ
  cases ψ
  simp_all

/-- The identity morphism (1,1). -/
def id (P : TorsorPresentation D) : TorsorArrow P P where
  degree := 1
  positive_degree := Nat.one_pos
  multiplier := 1
  finite_incl v := (D.finiteValue v).localInclusion_one_one (P.finiteCoord v)
  infinite_incl w := (D.infiniteValue w).localInclusion_one_one (P.infiniteCoord w)

/-- Composition, with the Frobenioid rule (m,g) o (n,f) = (nm, g f^m). -/
def comp (φ : TorsorArrow P₁ P₂) (ψ : TorsorArrow P₂ P₃) : TorsorArrow P₁ P₃ where
  degree := ψ.degree * φ.degree
  positive_degree := Nat.mul_pos ψ.positive_degree φ.positive_degree
  multiplier := ψ.multiplier * φ.multiplier ^ ψ.degree
  finite_incl v := by
    have h := LocalValueData.localInclusion_comp (D.finiteValue v)
      (φ.finite_incl v) (ψ.finite_incl v)
    simpa [Nat.mul_comm] using h
  infinite_incl w := by
    have h := LocalValueData.localInclusion_comp (D.infiniteValue w)
      (φ.infinite_incl w) (ψ.infinite_incl w)
    simpa [Nat.mul_comm] using h

theorem id_comp (φ : TorsorArrow P₁ P₂) : comp (id P₁) φ = φ := by
  ext <;> simp [comp, id]

theorem comp_id (φ : TorsorArrow P₁ P₂) : comp φ (id P₂) = φ := by
  ext <;> simp [comp, id]

theorem comp_assoc (φ : TorsorArrow P₁ P₂) (ψ : TorsorArrow P₂ P₃)
    (χ : TorsorArrow P₃ P₄) :
    comp (comp φ ψ) χ = comp φ (comp ψ χ) := by
  ext
  · simp only [comp]
    rw [Nat.mul_assoc]
  · simp only [comp]
    have hpow : (φ.multiplier ^ ψ.degree) ^ χ.degree =
        φ.multiplier ^ (ψ.degree * χ.degree) := (pow_mul _ _ _).symm
    have hcomm : φ.multiplier ^ (ψ.degree * χ.degree) =
        φ.multiplier ^ (χ.degree * ψ.degree) := by rw [Nat.mul_comm]
    rw [mul_pow, hpow, hcomm, ← mul_assoc]

/-- The local coordinate expression of a degree-n morphism at a place. -/
def localExpr {Γ : Type*} [AddCommGroup Γ] {F : Type*} [Field F]
    (D : LocalValueData F Γ) (n : ℕ) (f : Fˣ) (a₁ a₂ : Γ) : Γ :=
  D.deltaAdd f + n • a₁ - a₂

/-- **The change-of-base-point computation** (handoff chapter 1, G3): after
changing the source base point by h_1 and the target base point by h_2, the
transported multiplier h_2^{-1} f h_1^n has the same local coordinate
expression as the original multiplier f. -/
theorem rebase_localExpr {Γ : Type*} [AddCommGroup Γ] {F : Type*} [Field F]
    (D : LocalValueData F Γ) (h₁ h₂ f : Fˣ) (n : ℕ) (a₁ a₂ : Γ) :
    D.deltaAdd (h₂⁻¹ * f * h₁ ^ n) + n • (a₁ - D.deltaAdd h₁) - (a₂ - D.deltaAdd h₂)
      = D.deltaAdd f + n • a₁ - a₂ := by
  simp only [LocalValueData.deltaAdd_mul, LocalValueData.deltaAdd_inv,
    LocalValueData.deltaAdd_pow, smul_sub]
  abel

/-- Transport a morphism under a change of the two base points.  The degree is
unchanged and the multiplier becomes h_2^{-1} f h_1^n; the local integrality
conditions are preserved by the change-of-base-point computation. -/
def rebaseArrow (hD : D.HasFiniteSupport) (h₁ h₂ : Fˣ) (φ : TorsorArrow P₁ P₂) :
    TorsorArrow (TorsorPresentation.rebase hD P₁ h₁)
      (TorsorPresentation.rebase hD P₂ h₂) where
  degree := φ.degree
  positive_degree := φ.positive_degree
  multiplier := h₂⁻¹ * φ.multiplier * h₁ ^ φ.degree
  finite_incl v := by
    have hc₁ := TorsorPresentation.rebase_finiteCoord hD P₁ h₁ v
    have hc₂ := TorsorPresentation.rebase_finiteCoord hD P₂ h₂ v
    have hφ := φ.finite_incl v
    simp only [LocalValueData.localInclusion, hc₁, hc₂] at hφ ⊢
    rw [show (D.finiteValue v).deltaAdd (h₂⁻¹ * φ.multiplier * h₁ ^ φ.degree) +
        φ.degree • (P₁.finiteCoord v - D.finiteDelta h₁ v) -
        (P₂.finiteCoord v - D.finiteDelta h₂ v) =
        (D.finiteValue v).deltaAdd φ.multiplier + φ.degree • P₁.finiteCoord v -
          P₂.finiteCoord v from by
      simp only [GlobalPlaceData.finiteDelta]
      exact rebase_localExpr (D.finiteValue v) h₁ h₂ φ.multiplier φ.degree
        (P₁.finiteCoord v) (P₂.finiteCoord v)]
    exact hφ
  infinite_incl w := by
    have hc₁ := TorsorPresentation.rebase_infiniteCoord hD P₁ h₁ w
    have hc₂ := TorsorPresentation.rebase_infiniteCoord hD P₂ h₂ w
    have hφ := φ.infinite_incl w
    simp only [LocalValueData.localInclusion, hc₁, hc₂] at hφ ⊢
    rw [show (D.infiniteValue w).deltaAdd (h₂⁻¹ * φ.multiplier * h₁ ^ φ.degree) +
        φ.degree • (P₁.infiniteCoord w - D.infiniteDelta h₁ w) -
        (P₂.infiniteCoord w - D.infiniteDelta h₂ w) =
        (D.infiniteValue w).deltaAdd φ.multiplier + φ.degree • P₁.infiniteCoord w -
          P₂.infiniteCoord w from by
      simp only [GlobalPlaceData.infiniteDelta]
      exact rebase_localExpr (D.infiniteValue w) h₁ h₂ φ.multiplier φ.degree
        (P₁.infiniteCoord w) (P₂.infiniteCoord w)]
    exact hφ

@[simp]
theorem rebaseArrow_degree (hD : D.HasFiniteSupport) (h₁ h₂ : Fˣ)
    (φ : TorsorArrow P₁ P₂) :
    (rebaseArrow hD h₁ h₂ φ).degree = φ.degree := rfl

@[simp]
theorem rebaseArrow_multiplier (hD : D.HasFiniteSupport) (h₁ h₂ : Fˣ)
    (φ : TorsorArrow P₁ P₂) :
    (rebaseArrow hD h₁ h₂ φ).multiplier = h₂⁻¹ * φ.multiplier * h₁ ^ φ.degree := rfl

/-- **Base-point change is a bijection on morphisms**: a degree-n morphism
with multiplier f between the presentations exists if and only if a degree-n
morphism with multiplier h_2^{-1} f h_1^n exists between the rebased
presentations.  This is the precise sense in which the arrow condition is
independent of the chosen base points. -/
theorem exists_arrow_rebase_iff (hD : D.HasFiniteSupport) (h₁ h₂ : Fˣ)
    (n : ℕ) (f : Fˣ) :
    (∃ φ : TorsorArrow P₁ P₂, φ.degree = n ∧ φ.multiplier = f) ↔
      (∃ ψ : TorsorArrow (TorsorPresentation.rebase hD P₁ h₁)
          (TorsorPresentation.rebase hD P₂ h₂),
        ψ.degree = n ∧ ψ.multiplier = h₂⁻¹ * f * h₁ ^ n) := by
  constructor
  · rintro ⟨φ, rfl, rfl⟩
    exact ⟨rebaseArrow hD h₁ h₂ φ, rfl, rfl⟩
  · rintro ⟨ψ, hdeg, hmult⟩
    have hf : f = h₂ * ψ.multiplier * (h₁ ^ n)⁻¹ := by
      rw [hmult]
      group
    refine ⟨{ degree := n
              positive_degree := by rw [← hdeg]; exact ψ.positive_degree
              multiplier := f
              finite_incl := ?_
              infinite_incl := ?_ }, rfl, rfl⟩
    · intro v
      have hψ := ψ.finite_incl v
      have hc₁ := TorsorPresentation.rebase_finiteCoord hD P₁ h₁ v
      have hc₂ := TorsorPresentation.rebase_finiteCoord hD P₂ h₂ v
      simp only [LocalValueData.localInclusion, hc₁, hc₂, hdeg, hmult] at hψ
      simp only [LocalValueData.localInclusion]
      rw [show (D.finiteValue v).deltaAdd f + n • P₁.finiteCoord v - P₂.finiteCoord v =
          (D.finiteValue v).deltaAdd (h₂⁻¹ * f * h₁ ^ n) +
            n • (P₁.finiteCoord v - D.finiteDelta h₁ v) -
            (P₂.finiteCoord v - D.finiteDelta h₂ v) from by
        simp only [GlobalPlaceData.finiteDelta]
        rw [rebase_localExpr]]
      exact hψ
    · intro w
      have hψ := ψ.infinite_incl w
      have hc₁ := TorsorPresentation.rebase_infiniteCoord hD P₁ h₁ w
      have hc₂ := TorsorPresentation.rebase_infiniteCoord hD P₂ h₂ w
      simp only [LocalValueData.localInclusion, hc₁, hc₂, hdeg, hmult] at hψ
      simp only [LocalValueData.localInclusion]
      rw [show (D.infiniteValue w).deltaAdd f + n • P₁.infiniteCoord w -
          P₂.infiniteCoord w =
          (D.infiniteValue w).deltaAdd (h₂⁻¹ * f * h₁ ^ n) +
            n • (P₁.infiniteCoord w - D.infiniteDelta h₁ w) -
            (P₂.infiniteCoord w - D.infiniteDelta h₂ w) from by
        simp only [GlobalPlaceData.infiniteDelta]
        rw [rebase_localExpr]]
      exact hψ

/-- Base-point change commutes with composition. -/
theorem rebaseArrow_comp (hD : D.HasFiniteSupport) (h₁ h₂ h₃ : Fˣ)
    (φ : TorsorArrow P₁ P₂) (ψ : TorsorArrow P₂ P₃) :
    rebaseArrow hD h₁ h₃ (comp φ ψ) =
      comp (rebaseArrow hD h₁ h₂ φ) (rebaseArrow hD h₂ h₃ ψ) := by
  ext
  · simp only [rebaseArrow, comp]
  · simp only [rebaseArrow, comp]
    rw [mul_pow, mul_pow, inv_pow, ← pow_mul]
    have hexp : φ.degree * ψ.degree = ψ.degree * φ.degree := Nat.mul_comm _ _
    rw [hexp]
    group

/-- Base-point change preserves identities. -/
theorem rebaseArrow_id (hD : D.HasFiniteSupport) (h : Fˣ) (P : TorsorPresentation D) :
    rebaseArrow hD h h (id P) = id (TorsorPresentation.rebase hD P h) := by
  ext <;> simp [rebaseArrow, id]

end TorsorArrow

end Example36
end LeanFormal.IUT.IUTII.Frobenioid
