import LeanFormal.IUT.IUTII.Frobenioid.Example36GlobalPlaceData

/-!
# The global ideal-family category of IUT III, Example 3.6

This is the Layer-2 core: the category of global ideal families of
Example 3.6 in value-group coordinates.

An object is a family of local integral objects, encoded by its local value
coordinates: at a finite place a finitely supported integer exponent (the
valuation of the fractional ideal), at an archimedean place the real coordinate
delta_w = -log(radius).  The finite part is a Finsupp, so the almost-everywhere
standard condition is built into the type.  Objects are written additively:
addition is multiplication of ideal families in exponent coordinates, and the
standard object is 0.

A morphism from J1 to J2 is a positive integer degree n together with a global
rational-function multiplier f in F^!, subject to the local integrality
conditions delta_v(f) + n a1_v - a2_v in C_v at every place.  The identity is
(1,1), and the composition rule of Example 3.6 is proved:

  (m,g) o (n,f) = (nm, g f^m).

The divisor sign convention is frozen here: the object coordinate is
delta(J) = J, the backend coordinate is d(J) = -J, and for an arrow with
effective part Z we prove the pointwise balance identity

  n d(J1) + Z = d(J2) + div(f).

Isomorphisms are characterized as the degree-one arrows whose effective part
vanishes; the two opposite integrality inequalities force vanishing by
sharpness of the local integral cones.

Boundary: this is the global ideal-family category only.  It does not construct
the torsor category or the equivalence of Example 3.6 (next layer), the source
Hodge theater, or any source theta-pilot identifications.
-/

noncomputable section

namespace LeanFormal.IUT.IUTII.Frobenioid
namespace Example36

open scoped NumberField
open IsDedekindDomain NumberField

universe u

variable {F : Type u} [Field F] [NumberField F]

/-- A global ideal family in value coordinates: finitely supported finite-place
valuations plus archimedean logarithmic radius coordinates. -/
structure GlobalIdealFamily (F : Type u) [Field F] [NumberField F] where
  /-- The finite-place value coordinates (valuation exponents). -/
  finite : HeightOneSpectrum (𝓞 F) →₀ ℤ
  /-- The archimedean value coordinates delta_w = -log(radius). -/
  infinite : NumberField.InfinitePlace F → ℝ

namespace GlobalIdealFamily

variable {J₁ J₂ J₃ : GlobalIdealFamily F}

@[ext]
theorem ext (hf : J₁.finite = J₂.finite) (hi : J₁.infinite = J₂.infinite) :
    J₁ = J₂ := by
  cases J₁
  cases J₂
  simp_all

/-- The standard global object: the integer ring at every finite place and the
radius-one ball at every archimedean place. -/
def standard : GlobalIdealFamily F :=
  ⟨0, fun _ => 0⟩

instance : Zero (GlobalIdealFamily F) := ⟨standard⟩

@[simp]
theorem zero_finite : (0 : GlobalIdealFamily F).finite = 0 := rfl

@[simp]
theorem zero_infinite (w : NumberField.InfinitePlace F) :
    (0 : GlobalIdealFamily F).infinite w = 0 := rfl

/-- Componentwise product of ideal families (addition of value coordinates). -/
def add (J₁ J₂ : GlobalIdealFamily F) : GlobalIdealFamily F :=
  ⟨J₁.finite + J₂.finite, fun w => J₁.infinite w + J₂.infinite w⟩

instance : Add (GlobalIdealFamily F) := ⟨add⟩

@[simp]
theorem add_finite (J₁ J₂ : GlobalIdealFamily F) :
    (J₁ + J₂).finite = J₁.finite + J₂.finite := rfl

@[simp]
theorem add_infinite (J₁ J₂ : GlobalIdealFamily F) (w : NumberField.InfinitePlace F) :
    (J₁ + J₂).infinite w = J₁.infinite w + J₂.infinite w := rfl

/-- Componentwise inverse ideal family. -/
def neg (J : GlobalIdealFamily F) : GlobalIdealFamily F :=
  ⟨-J.finite, fun w => -J.infinite w⟩

instance : Neg (GlobalIdealFamily F) := ⟨neg⟩

@[simp]
theorem neg_finite (J : GlobalIdealFamily F) : (-J).finite = -J.finite := rfl

@[simp]
theorem neg_infinite (J : GlobalIdealFamily F) (w : NumberField.InfinitePlace F) :
    (-J).infinite w = -J.infinite w := rfl

/-- Componentwise natural multiple: the n-th tensor power of an ideal family. -/
def nsmul (n : ℕ) (J : GlobalIdealFamily F) : GlobalIdealFamily F :=
  ⟨n • J.finite, fun w => n • J.infinite w⟩

instance : SMul ℕ (GlobalIdealFamily F) := ⟨nsmul⟩

@[simp]
theorem nsmul_finite (n : ℕ) (J : GlobalIdealFamily F) :
    (n • J).finite = n • J.finite := rfl

@[simp]
theorem nsmul_infinite (n : ℕ) (J : GlobalIdealFamily F)
    (w : NumberField.InfinitePlace F) :
    (n • J).infinite w = n • J.infinite w := rfl

theorem add_assoc_family (J₁ J₂ J₃ : GlobalIdealFamily F) :
    J₁ + J₂ + J₃ = J₁ + (J₂ + J₃) := by
  ext <;> simp [add_assoc]

theorem add_comm_family (J₁ J₂ : GlobalIdealFamily F) : J₁ + J₂ = J₂ + J₁ := by
  ext <;> simp [add_comm]

theorem zero_add_family (J : GlobalIdealFamily F) : 0 + J = J := by
  ext <;> simp

theorem add_zero_family (J : GlobalIdealFamily F) : J + 0 = J := by
  ext <;> simp

theorem neg_add_cancel_family (J : GlobalIdealFamily F) : -J + J = 0 := by
  ext <;> simp

end GlobalIdealFamily

/-- The additive form of the inverse of a local value: delta(f^-1) = -delta(f). -/
theorem LocalValueData.deltaAdd_inv {Gamma : Type*} [AddCommGroup Gamma]
    {F : Type*} [Field F] (D : LocalValueData F Gamma) (x : Fˣ) :
    D.deltaAdd x⁻¹ = -D.deltaAdd x := by
  have h : D.deltaAdd x + D.deltaAdd x⁻¹ = 0 := by
    have hmul : D.deltaAdd (x * x⁻¹) = D.deltaAdd x + D.deltaAdd x⁻¹ :=
      LocalValueData.deltaAdd_mul D x x⁻¹
    rw [mul_inv_cancel, LocalValueData.deltaAdd_one] at hmul
    exact hmul.symm
  exact eq_neg_of_add_eq_zero_right h

namespace GlobalIdealFamily

variable {D : GlobalPlaceData F}

/-- A morphism of global ideal families of Example 3.6: positive degree n, a
global multiplier f, and the local integral inclusion conditions. -/
structure Hom (D : GlobalPlaceData F) (J₁ J₂ : GlobalIdealFamily F) where
  /-- The positive integer degree of the morphism. -/
  degree : ℕ
  /-- The degree is positive (the paper's n > 0). -/
  positive_degree : 0 < degree
  /-- The global rational-function multiplier f in F^!. -/
  multiplier : Fˣ
  /-- The finite-place integrality conditions. -/
  finite_incl : ∀ v : HeightOneSpectrum (𝓞 F),
    (D.finiteValue v).localInclusion degree multiplier (J₁.finite v) (J₂.finite v)
  /-- The archimedean integrality conditions. -/
  infinite_incl : ∀ w : NumberField.InfinitePlace F,
    (D.infiniteValue w).localInclusion degree multiplier (J₁.infinite w) (J₂.infinite w)

namespace Hom

variable {J₁ J₂ J₃ J₄ : GlobalIdealFamily F}

@[ext]
theorem ext {h k : Hom D J₁ J₂} (hdeg : h.degree = k.degree)
    (hmult : h.multiplier = k.multiplier) : h = k := by
  cases h
  cases k
  simp_all

/-- The identity morphism (1,1). -/
def id (J : GlobalIdealFamily F) : Hom D J J where
  degree := 1
  positive_degree := Nat.one_pos
  multiplier := 1
  finite_incl v := (D.finiteValue v).localInclusion_one_one (J.finite v)
  infinite_incl w := (D.infiniteValue w).localInclusion_one_one (J.infinite w)

/-- Composition of morphisms, following the Frobenioid rule
(m,g) o (n,f) = (nm, g f^m): the multiplier of the first arrow is raised to
the degree of the second arrow. -/
def comp (h : Hom D J₁ J₂) (k : Hom D J₂ J₃) : Hom D J₁ J₃ where
  degree := k.degree * h.degree
  positive_degree := Nat.mul_pos k.positive_degree h.positive_degree
  multiplier := k.multiplier * h.multiplier ^ k.degree
  finite_incl v := by
    have hcomp := LocalValueData.localInclusion_comp (D.finiteValue v)
      (h.finite_incl v) (k.finite_incl v)
    simpa [Nat.mul_comm] using hcomp
  infinite_incl w := by
    have hcomp := LocalValueData.localInclusion_comp (D.infiniteValue w)
      (h.infinite_incl w) (k.infinite_incl w)
    simpa [Nat.mul_comm] using hcomp

theorem id_comp (h : Hom D J₁ J₂) : comp (id J₁) h = h := by
  ext <;> simp [comp, id]

theorem comp_id (h : Hom D J₁ J₂) : comp h (id J₂) = h := by
  ext <;> simp [comp, id]

theorem comp_assoc (h : Hom D J₁ J₂) (k : Hom D J₂ J₃) (l : Hom D J₃ J₄) :
    comp (comp h k) l = comp h (comp k l) := by
  ext
  · simp only [comp]
    rw [Nat.mul_assoc]
  · simp only [comp]
    have hpow : (h.multiplier ^ k.degree) ^ l.degree =
        h.multiplier ^ (k.degree * l.degree) := (pow_mul _ _ _).symm
    have hcomm : h.multiplier ^ (k.degree * l.degree) =
        h.multiplier ^ (l.degree * k.degree) := by rw [Nat.mul_comm]
    rw [mul_pow, hpow, hcomm, ← mul_assoc]

/-- The effective (integral) part Z of a morphism at a finite place:
delta_v(f) + n a1_v - a2_v.  The arrow condition says Z lies in the integral
cone at every place. -/
def effectiveFinite (h : Hom D J₁ J₂) (v : HeightOneSpectrum (𝓞 F)) : ℤ :=
  D.finiteDelta h.multiplier v + h.degree • J₁.finite v - J₂.finite v

/-- The effective part Z at an archimedean place. -/
def effectiveInfinite (h : Hom D J₁ J₂) (w : NumberField.InfinitePlace F) : ℝ :=
  D.infiniteDelta h.multiplier w + h.degree • J₁.infinite w - J₂.infinite w

theorem effectiveFinite_mem_cone (h : Hom D J₁ J₂)
    (v : HeightOneSpectrum (𝓞 F)) :
    h.effectiveFinite v ∈ (D.finiteValue v).cone := by
  have := h.finite_incl v
  simpa [LocalValueData.localInclusion, effectiveFinite, GlobalPlaceData.finiteDelta]
    using this

theorem effectiveInfinite_mem_cone (h : Hom D J₁ J₂)
    (w : NumberField.InfinitePlace F) :
    h.effectiveInfinite w ∈ (D.infiniteValue w).cone := by
  have := h.infinite_incl w
  simpa [LocalValueData.localInclusion, effectiveInfinite, GlobalPlaceData.infiniteDelta]
    using this

/-- The backend divisor balance identity at a finite place, with
d(J) = -delta(J):  n d(J1) + Z = d(J2) + div(f). -/
theorem balance_finite (h : Hom D J₁ J₂) (v : HeightOneSpectrum (𝓞 F)) :
    -(h.degree • J₁.finite v) + h.effectiveFinite v =
      -J₂.finite v + D.finiteDelta h.multiplier v := by
  unfold effectiveFinite
  abel

/-- The backend divisor balance identity at an archimedean place. -/
theorem balance_infinite (h : Hom D J₁ J₂)
    (w : NumberField.InfinitePlace F) :
    -(h.degree • J₁.infinite w) + h.effectiveInfinite w =
      -J₂.infinite w + D.infiniteDelta h.multiplier w := by
  unfold effectiveInfinite
  abel

/-- An isomorphism is a morphism with a two-sided inverse. -/
def IsIso (h : Hom D J₁ J₂) : Prop :=
  ∃ k : Hom D J₂ J₁, comp h k = id J₁ ∧ comp k h = id J₂

/-- The pointwise vanishing of the effective part: a2 = a1 + delta(f) at every
place, i.e. J2 = J1 + div(f) in value coordinates. -/
def HasZeroEffectivePart (h : Hom D J₁ J₂) : Prop :=
  (∀ v : HeightOneSpectrum (𝓞 F), h.effectiveFinite v = 0) ∧
    (∀ w : NumberField.InfinitePlace F, h.effectiveInfinite w = 0)

/-- From a two-sided inverse, the degree of the first arrow is one. -/
theorem degree_eq_one_of_comp_eq_id {h : Hom D J₁ J₂} {k : Hom D J₂ J₁}
    (hcomp : comp h k = id J₁) : h.degree = 1 := by
  have hdeg : k.degree * h.degree = 1 := by
    have := congrArg Hom.degree hcomp
    simpa [comp, id] using this
  exact Nat.eq_one_of_mul_eq_one_left hdeg

/-- From the other two-sided composition, the degree of the inverse arrow is one. -/
theorem degree_eq_one_of_comp_eq_id' {h : Hom D J₁ J₂} {k : Hom D J₂ J₁}
    (hcomp : comp k h = id J₂) : k.degree = 1 := by
  have hdeg : h.degree * k.degree = 1 := by
    have := congrArg Hom.degree hcomp
    simpa [comp, id] using this
  exact Nat.eq_one_of_mul_eq_one_left hdeg

/-- From a two-sided inverse, the multiplier of the inverse arrow is the inverse
of the multiplier. -/
theorem multiplier_inv_of_comp_eq_id {h : Hom D J₁ J₂} {k : Hom D J₂ J₁}
    (hcomp : comp h k = id J₁) (hkdeg : k.degree = 1) :
    k.multiplier = h.multiplier⁻¹ := by
  have hmult : k.multiplier * h.multiplier ^ k.degree = 1 := by
    have := congrArg Hom.multiplier hcomp
    simpa [comp, id] using this
  rw [hkdeg, pow_one] at hmult
  exact eq_inv_of_mul_eq_one_left hmult

private theorem effectiveFinite_eq_zero_of_inverse {h : Hom D J₁ J₂}
    (k : Hom D J₂ J₁) (hcomp : comp h k = id J₁)
    (hcomp' : comp k h = id J₂) :
    ∀ v : HeightOneSpectrum (𝓞 F), h.effectiveFinite v = 0 := by
  intro v
  have hdeg : h.degree = 1 := degree_eq_one_of_comp_eq_id hcomp
  have hkdeg : k.degree = 1 := degree_eq_one_of_comp_eq_id' hcomp'
  have hmult : k.multiplier = h.multiplier⁻¹ :=
    multiplier_inv_of_comp_eq_id hcomp hkdeg
  have hx : h.effectiveFinite v ∈ (D.finiteValue v).cone :=
    h.effectiveFinite_mem_cone v
  have hy : -h.effectiveFinite v ∈ (D.finiteValue v).cone := by
    have hk := k.finite_incl v
    have hdel : (D.finiteValue v).deltaAdd k.multiplier =
        -(D.finiteValue v).deltaAdd h.multiplier := by
      rw [hmult, LocalValueData.deltaAdd_inv]
    simp only [LocalValueData.localInclusion, hkdeg, one_nsmul, hdel] at hk
    have hz : -h.effectiveFinite v =
        -(D.finiteValue v).deltaAdd h.multiplier + J₂.finite v - J₁.finite v := by
      simp only [effectiveFinite, GlobalPlaceData.finiteDelta, hdeg, one_nsmul]
      abel
    rw [hz]
    exact hk
  exact (D.finiteValue v).cone_sharp _ hx hy

private theorem effectiveInfinite_eq_zero_of_inverse {h : Hom D J₁ J₂}
    (k : Hom D J₂ J₁) (hcomp : comp h k = id J₁)
    (hcomp' : comp k h = id J₂) :
    ∀ w : NumberField.InfinitePlace F, h.effectiveInfinite w = 0 := by
  intro w
  have hdeg : h.degree = 1 := degree_eq_one_of_comp_eq_id hcomp
  have hkdeg : k.degree = 1 := degree_eq_one_of_comp_eq_id' hcomp'
  have hmult : k.multiplier = h.multiplier⁻¹ :=
    multiplier_inv_of_comp_eq_id hcomp hkdeg
  have hx : h.effectiveInfinite w ∈ (D.infiniteValue w).cone :=
    h.effectiveInfinite_mem_cone w
  have hy : -h.effectiveInfinite w ∈ (D.infiniteValue w).cone := by
    have hk := k.infinite_incl w
    have hdel : (D.infiniteValue w).deltaAdd k.multiplier =
        -(D.infiniteValue w).deltaAdd h.multiplier := by
      rw [hmult, LocalValueData.deltaAdd_inv]
    simp only [LocalValueData.localInclusion, hkdeg, one_nsmul, hdel] at hk
    have hz : -h.effectiveInfinite w =
        -(D.infiniteValue w).deltaAdd h.multiplier + J₂.infinite w - J₁.infinite w := by
      simp only [effectiveInfinite, GlobalPlaceData.infiniteDelta, hdeg, one_nsmul]
      ring
    rw [hz]
    exact hk
  exact (D.infiniteValue w).cone_sharp _ hx hy

/-- **Isomorphism characterization, forward direction.** -/
theorem hasZeroEffectivePart_of_isIso {h : Hom D J₁ J₂} (hiso : h.IsIso) :
    h.HasZeroEffectivePart := by
  obtain ⟨k, hcomp, hcomp'⟩ := hiso
  exact ⟨effectiveFinite_eq_zero_of_inverse k hcomp hcomp',
    effectiveInfinite_eq_zero_of_inverse k hcomp hcomp'⟩

/-- **Isomorphism characterization, converse direction.**  A degree-one
morphism whose effective part vanishes is an isomorphism, with inverse
multiplier f^-1. -/
theorem isIso_of_degree_one_of_effective_zero (h : Hom D J₁ J₂)
    (hdeg : h.degree = 1) (hpart : h.HasZeroEffectivePart) : h.IsIso := by
  obtain ⟨hfin, hinf⟩ := hpart
  have hJf : ∀ v : HeightOneSpectrum (𝓞 F),
      J₂.finite v = J₁.finite v + D.finiteDelta h.multiplier v := by
    intro v
    have hzero := hfin v
    simp only [effectiveFinite, hdeg, one_nsmul] at hzero
    omega
  have hJi : ∀ w : NumberField.InfinitePlace F,
      J₂.infinite w = J₁.infinite w + D.infiniteDelta h.multiplier w := by
    intro w
    have hzero := hinf w
    simp only [effectiveInfinite, hdeg, one_nsmul] at hzero
    linarith
  let k : Hom D J₂ J₁ :=
    { degree := 1
      positive_degree := Nat.one_pos
      multiplier := h.multiplier⁻¹
      finite_incl := fun v => by
        simp only [LocalValueData.localInclusion, one_nsmul]
        rw [LocalValueData.deltaAdd_inv, hJf v]
        have h0 : -(D.finiteValue v).deltaAdd h.multiplier +
            (J₁.finite v + D.finiteDelta h.multiplier v) - J₁.finite v = 0 := by
          simp only [GlobalPlaceData.finiteDelta]
          abel
        rw [h0]
        exact (D.finiteValue v).cone.zero_mem
      infinite_incl := fun w => by
        simp only [LocalValueData.localInclusion, one_nsmul]
        rw [LocalValueData.deltaAdd_inv, hJi w]
        have h0 : -(D.infiniteValue w).deltaAdd h.multiplier +
            (J₁.infinite w + D.infiniteDelta h.multiplier w) - J₁.infinite w = 0 := by
          simp only [GlobalPlaceData.infiniteDelta]
          ring
        rw [h0]
        exact (D.infiniteValue w).cone.zero_mem }
  refine ⟨k, ?_, ?_⟩
  · ext <;> simp [comp, id, k, hdeg]
  · ext <;> simp [comp, id, k, hdeg]

/-- **Isomorphism characterization.**  A morphism is an isomorphism exactly when
its degree is one and its effective part vanishes at every place. -/
theorem isIso_iff (h : Hom D J₁ J₂) :
    h.IsIso ↔ h.degree = 1 ∧ h.HasZeroEffectivePart := by
  constructor
  · rintro ⟨k, hcomp, hcomp'⟩
    exact ⟨degree_eq_one_of_comp_eq_id hcomp,
      hasZeroEffectivePart_of_isIso ⟨k, hcomp, hcomp'⟩⟩
  · rintro ⟨hdeg, hpart⟩
    exact isIso_of_degree_one_of_effective_zero h hdeg hpart

end Hom

end GlobalIdealFamily

end Example36
end LeanFormal.IUT.IUTII.Frobenioid
