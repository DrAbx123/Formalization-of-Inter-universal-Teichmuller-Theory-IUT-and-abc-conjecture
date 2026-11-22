/-
  # Arithmetic local Galois groups at the places of Q(i) and the frozen
  # curve-Pi card

  Task task-47 (review N2 fix) of the Group-1 split.  This module corrects the
  source semantics of the local Galois side: at each place v of the Gaussian
  field Q(i),

  * G_v is the absolute Galois group of the base local field, i.e. of the
    v-adic completion at a finite place or of the real/complex completion at an
    archimedean place;
  * Pi_v is the tempered/etale fundamental group of the once-punctured elliptic
    curve over that local field, with a surjection Pi_v -> G_v whose kernel is
    the geometric fundamental group.

  This module constructs the actual local fields and the actual arithmetic
  groups G_v at every place, together with the certified anabelioid B(G_v)
  (finite continuous G_v-sets), and freezes the genuinely missing curve-side
  data Pi_v as a precise specification card.  No curve fundamental group is
  invented here.

  ## What is constructed and proved

  * The actual local field at each place:
    - at a finite place v (height-one prime of the ring of integers),
      the actual v-adic completion v.adicCompletion Q(i) (a field);
    - at an archimedean place w, the actual archimedean completion: the real
      line R when w is a real place and the complex field C when w is complex.
  * The arithmetic Galois groups: placeArithmeticGalois P is
    Iut.AbsoluteGaloisProfinite of the local field at P, the Krull profinite
    group of the separable closure.  The finite-place and archimedean-place
    components are proved to be these actual groups, including the concrete
    place of Example36SourceTheaterCarrier.
  * The certified anabelioids B(G_v): placeArithmeticAnabelioid P is
    Iut.continuousActionEtaleFundamentalGroup (placeArithmeticGalois P), the
    Galois category of finite continuous G_v-sets; its group field is G_v
    (proved) and its fundamental-group certification is recorded.
  * The arithmetic Galois data: GaussianPlaceArithmeticGaloisData bundles the
    actual G_v family with the certified B(G_v) family.  This is the arithmetic
    side only.  It is NOT a D-prime-strip, and it does not contain the
    geometric fundamental group: no such claim is made.
  * The frozen curve-Pi card: GaussianPlaceCurvePiCard records exactly the data
    the source would have to supply: the once-punctured elliptic curve over the
    local field at every place, its tempered/etale fundamental group Pi_v, a
    surjective morphism Pi_v -> G_v, and the geometric kernel as the kernel of
    that morphism (canonically determined).  No inhabitant is constructed; the
    card is a specification, not a fake group.  The remaining requirements of
    the card (identification of Pi_v with the tempered/etale fundamental group
    of the actual once-punctured elliptic curve, and the Galois action of Pi_v
    on the local value monoid with degree compatibility) are stated in its
    documentation and are not formalized.

  ## Non-substitution

  The identity-projection finite-interval D-strips of the tree
  (finiteLocalDPrimeStrip lower upper) are indexed by the finite set
  FinitePrimePlace lower upper of rational-prime labels, while a place-indexed
  object over the Gaussian field is indexed by GaussianPlaceIndex.  These index
  types are not equivalent (finite versus infinite, the latter proved by
  extending rational primes), so the model strips have a different
  index/carrier and cannot be substituted for the Gaussian place data.  Their
  projection is the identity and their geometric kernel is trivial (recorded in
  Example36GaussianPlaceStrip.lean).  The same remark applies to the
  rational-prime model localDPrimeStrip.  Neither model is used as the curve
  Pi_v or as a D-prime-strip of the Gaussian places.

  ## What is NOT proved (honest boundary)

  The curve-side data is entirely missing from the tree at the places of Q(i):
  no once-punctured elliptic curve over the local fields at those places, no
  tempered/etale fundamental group Pi_v, no surjection Pi_v -> G_v, no geometric
  kernel and no Galois action of Pi_v on the local value monoid with degree
  compatibility are constructed; they are frozen as GaussianPlaceCurvePiCard.
  The value-group/degree layer of Example36GaussianPlaceStrip.lean and the
  arithmetic Galois data here are not claimed to be a D-prime-strip.  No
  theta-pilot, q-pilot, Tate, or further source-identification claim is made.

  Source correspondence: IUT I, p. 4 and Definition 3.1(d)-(e) (the arithmetic
  local Galois group G_v, the curve fundamental group Pi_v, and the surjection
  Pi_v -> G_v with geometric kernel); IUT I, Definition 5.2 (prime strips at the
  places of a number field); IUT III, Example 3.6 (local data).
-/

import LeanFormal.IUT.IUTII.Frobenioid.Example36GaussianPlaceStrip
import Iut.Foundations.Orbicurve
import Iut.Foundations.SourceContinuousAnabelioid
import Mathlib.Data.Nat.PrimeFin
import Mathlib.NumberTheory.Padics.HeightOneSpectrum

set_option relaxedAutoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT.IUTII.Frobenioid.Example36
namespace GaussianLocalGalois

open CategoryTheory
open LeanFormal.IUT
open LeanFormal.IUT.ConcreteSourceFrobenioidBridge
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.IUTII.Frobenioid
open LeanFormal.IUT.IUTII.Frobenioid.Example36
open LeanFormal.IUT.IUTII.Frobenioid.Example36.GaussianPlaceStrip
open Iut
open IsDedekindDomain
open scoped NumberField

local instance gaussianPolynomialIrreducibleFactLocalGalois :
    Fact (Irreducible (Polynomial.X ^ 2 - Polynomial.C (-1) : Polynomial ℚ)) :=
  ⟨gaussianPolynomial_irreducible⟩

local instance fivePrimeFactLocalGalois : Fact (Nat.Prime 5) :=
  ⟨Nat.prime_five⟩

local instance primeFactLocalGalois (l : PrimeGeFive) : Fact (Nat.Prime l.value) :=
  l.factPrime

noncomputable section

/-! ## 1. The actual local field at every place of Q(i) -/

/-- The actual archimedean completion at an infinite place: the real line at a
real place, the complex field at a complex place. -/
noncomputable def archimedeanPlaceLocalField
    (w : NumberField.InfinitePlace GaussianField) : Type := by
  classical
  exact if h : w.IsReal then ℝ else ℂ

noncomputable instance archimedeanPlaceLocalFieldField
    (w : NumberField.InfinitePlace GaussianField) :
    Field (archimedeanPlaceLocalField w) := by
  classical
  unfold archimedeanPlaceLocalField
  split
  · exact inferInstanceAs (Field ℝ)
  · exact inferInstanceAs (Field ℂ)

theorem archimedeanPlaceLocalField_eq_real
    (w : NumberField.InfinitePlace GaussianField) (h : w.IsReal) :
    archimedeanPlaceLocalField w = ℝ := by
  classical
  unfold archimedeanPlaceLocalField
  exact dif_pos h

theorem archimedeanPlaceLocalField_eq_complex
    (w : NumberField.InfinitePlace GaussianField) (h : ¬ w.IsReal) :
    archimedeanPlaceLocalField w = ℂ := by
  classical
  unfold archimedeanPlaceLocalField
  exact dif_neg h

/-- The actual local field at a place of the Gaussian field: the v-adic
completion at a finite place, the real or complex completion at an archimedean
place. -/
noncomputable def placeLocalField (P : GaussianPlaceIndex) : Type :=
  match P with
  | Sum.inl v => v.adicCompletion GaussianField
  | Sum.inr w => archimedeanPlaceLocalField w

noncomputable instance placeLocalFieldField (P : GaussianPlaceIndex) :
    Field (placeLocalField P) := by
  cases P with
  | inl v => exact inferInstanceAs (Field (v.adicCompletion GaussianField))
  | inr w => exact inferInstanceAs (Field (archimedeanPlaceLocalField w))

theorem placeLocalField_finite (v : HeightOneSpectrum (𝓞 GaussianField)) :
    placeLocalField (finiteGaussianPlace v) = v.adicCompletion GaussianField :=
  rfl

theorem placeLocalField_infinite (w : NumberField.InfinitePlace GaussianField) :
    placeLocalField (infiniteGaussianPlace w) = archimedeanPlaceLocalField w :=
  rfl

/-! ## 2. The arithmetic local Galois groups G_v -/

/-- The arithmetic local Galois group G_v at a place of the Gaussian field: the
Krull profinite absolute Galois group of the actual base local field.  This is
the arithmetic side; the curve fundamental group Pi_v is a different, larger
group with a surjection onto G_v. -/
noncomputable def placeArithmeticGalois (P : GaussianPlaceIndex) : ProfiniteGrp.{0} :=
  AbsoluteGaloisProfinite (placeLocalField P)

theorem placeArithmeticGalois_finite
    (v : HeightOneSpectrum (𝓞 GaussianField)) :
    placeArithmeticGalois (finiteGaussianPlace v) =
      AbsoluteGaloisProfinite (v.adicCompletion GaussianField) :=
  rfl

theorem placeArithmeticGalois_infinite
    (w : NumberField.InfinitePlace GaussianField) :
    placeArithmeticGalois (infiniteGaussianPlace w) =
      AbsoluteGaloisProfinite (archimedeanPlaceLocalField w) :=
  rfl

/-- At the concrete finite place of Example36SourceTheaterCarrier, the
arithmetic local Galois group is the absolute Galois group of the actual
concrete completion. -/
theorem concreteGaussianPlace_arithmeticGalois :
    placeArithmeticGalois concreteGaussianPlace =
      AbsoluteGaloisProfinite
        ((underlyingPrime concretePlace).adicCompletion GaussianField) :=
  rfl

/-! ## 3. The certified anabelioid B(G_v) -/

/-- The certified anabelioid B(G_v) at a place: the category of finite discrete
sets with continuous action of the arithmetic local Galois group G_v, together
with its certified fundamental group.  This is a finite-cover category of a
field, not a curve. -/
noncomputable def placeArithmeticAnabelioid
    (P : GaussianPlaceIndex) : EtaleFundamentalGroup.{0} :=
  continuousActionEtaleFundamentalGroup (placeArithmeticGalois P)

/-- The certified group of B(G_v) is the arithmetic local Galois group G_v. -/
theorem placeArithmeticAnabelioid_group (P : GaussianPlaceIndex) :
    (placeArithmeticAnabelioid P).group = placeArithmeticGalois P :=
  rfl

/-- **Certification of B(G_v).**  The anabelioid B(G_v) carries its certified
fundamental-group structure, with the actual arithmetic local Galois group as
the fundamental group. -/
theorem placeArithmeticAnabelioid_certified (P : GaussianPlaceIndex) :
    letI := (placeArithmeticAnabelioid P).coverCategory
    letI := (placeArithmeticAnabelioid P).galoisCategory
    letI := (placeArithmeticAnabelioid P).fiberFunctor
    letI (X : (placeArithmeticAnabelioid P).Cover) :=
      (placeArithmeticAnabelioid P).action X
    PreGaloisCategory.IsFundamentalGroup (placeArithmeticAnabelioid P).fiber
      (placeArithmeticAnabelioid P).group :=
  (placeArithmeticAnabelioid P).isFundamentalGroup

/-! ## 4. The arithmetic Galois data over the Gaussian places -/

/-- The arithmetic Galois data over the Gaussian places: the actual arithmetic
local Galois groups G_v and their certified anabelioids B(G_v).  This is the
arithmetic side only: the curve fundamental group Pi_v, the geometric kernel and
the geometric fundamental group are not part of this structure, and it is not a
D-prime-strip. -/
structure GaussianPlaceArithmeticGaloisData where
  /-- The actual arithmetic local Galois groups G_v at the places of Q(i). -/
  G : GaussianPlaceIndex → ProfiniteGrp.{0}
  /-- The certified anabelioids B(G_v). -/
  anabelioid : GaussianPlaceIndex → EtaleFundamentalGroup.{0}

/-- The arithmetic Galois data assembled from the actual local absolute Galois
groups. -/
noncomputable def gaussianPlaceArithmeticGaloisData :
    GaussianPlaceArithmeticGaloisData where
  G := placeArithmeticGalois
  anabelioid := placeArithmeticAnabelioid

@[simp] theorem gaussianPlaceArithmeticGaloisData_G :
    gaussianPlaceArithmeticGaloisData.G = placeArithmeticGalois :=
  rfl

@[simp] theorem gaussianPlaceArithmeticGaloisData_anabelioid :
    gaussianPlaceArithmeticGaloisData.anabelioid =
      placeArithmeticAnabelioid :=
  rfl

/-- Every component of the arithmetic Galois data is the actual arithmetic
local Galois group of the actual local field. -/
theorem gaussianPlaceArithmeticGaloisData_G_actual
    (P : GaussianPlaceIndex) :
    gaussianPlaceArithmeticGaloisData.G P =
      AbsoluteGaloisProfinite (placeLocalField P) :=
  rfl

/-- Every B(G_v) component of the arithmetic Galois data has the actual
arithmetic local Galois group as its certified fundamental group. -/
theorem gaussianPlaceArithmeticGaloisData_anabelioid_group
    (P : GaussianPlaceIndex) :
    (gaussianPlaceArithmeticGaloisData.anabelioid P).group =
      gaussianPlaceArithmeticGaloisData.G P :=
  rfl

/-! ## 5. The frozen card for the missing curve fundamental group Pi_v -/

/-- **Frozen specification card for the missing curve fundamental group Pi_v
over the Gaussian places.**

At every place of Q(i), the source requires the once-punctured elliptic curve
over the base local field, its tempered (or etale) fundamental group Pi_v, a
surjective morphism Pi_v -> G_v onto the actual arithmetic local Galois group,
and the geometric fundamental group as the kernel of that morphism.  The card
below records the shape of that data.  No inhabitant is constructed in this
file and no theorem consumes one; in particular no curve fundamental group is
invented, and the identity-projection finite model strips are not substituted.
The geometric kernel of any alleged card is nevertheless canonically determined
as the closed kernel of the projection (see
GaussianPlaceCurvePiCard.kernel), so the card cannot hide an unrelated second
group.  The remaining required identifications - that Pi_v is the
tempered/etale fundamental group of the actual once-punctured elliptic curve
over the local field, and that Pi_v acts on the local value monoid compatibly
with the degree - are recorded in this documentation and are not formalized. -/
structure GaussianPlaceCurvePiCard where
  /-- The once-punctured elliptic curve over the base local field at each
  place. -/
  curve : GaussianPlaceIndex → Type
  /-- The tempered/etale fundamental group Pi_v of the curve at each place. -/
  Pi : GaussianPlaceIndex → ProfiniteGrp.{0}
  /-- The surjection Pi_v -> G_v onto the arithmetic local Galois group. -/
  toArithmetic : ∀ P, Pi P ⟶ placeArithmeticGalois P
  /-- The surjection onto the arithmetic Galois group is surjective. -/
  toArithmetic_surjective : ∀ P, Function.Surjective (toArithmetic P)

namespace GaussianPlaceCurvePiCard

variable (card : GaussianPlaceCurvePiCard)

/-- The geometric fundamental group of a card, canonically the closed kernel of
the surjection Pi_v -> G_v.  It is not an independent datum. -/
noncomputable def kernel (P : GaussianPlaceIndex) :
    ClosedSubgroup (card.Pi P) :=
  profiniteKernelClosedSubgroup (card.toArithmetic P)

/-- The exact sequence determined by a card:
1 -> geometric kernel -> Pi_v -> G_v -> 1. -/
noncomputable def exactSequence (P : GaussianPlaceIndex) :
    ProfiniteFundamentalExactSequence
      (closedSubgroupProfiniteGrp (card.kernel P))
      (card.Pi P) (placeArithmeticGalois P) :=
  profiniteKernelExactSequence (card.toArithmetic P)
    (card.toArithmetic_surjective P)

end GaussianPlaceCurvePiCard

/-! ## 6. Infinitude of the Gaussian place index and non-substitution -/

noncomputable instance infiniteRatHeightOneSpectrum :
    Infinite (HeightOneSpectrum (𝓞 ℚ)) :=
  Infinite.of_injective
    (⇑(Rat.HeightOneSpectrum.primesEquiv (R := NumberField.RingOfIntegers ℚ)).symm)
    (EquivLike.injective _)

/-- A chosen extension of a rational finite place to a finite place of the
Gaussian field. -/
noncomputable def ratPlaceToGaussianPrime (p : HeightOneSpectrum (𝓞 ℚ)) :
    HeightOneSpectrum (𝓞 GaussianField) :=
  (Classical.choose (comap_surjective (k := ℚ) (K := GaussianField)
    (NumberField.FinitePlace.mk p))).maximalIdeal

theorem ratPlaceToGaussianPrime_injective :
    Function.Injective ratPlaceToGaussianPrime := by
  intro p q h
  have hchoose :
      Classical.choose (comap_surjective (k := ℚ) (K := GaussianField)
        (NumberField.FinitePlace.mk p)) =
      Classical.choose (comap_surjective (k := ℚ) (K := GaussianField)
        (NumberField.FinitePlace.mk q)) := by
    have hc := congrArg NumberField.FinitePlace.mk h
    simpa only [ratPlaceToGaussianPrime, NumberField.FinitePlace.mk_maximalIdeal] using hc
  have hcomap := congrArg (NumberFieldFinitePlace.comap (k := ℚ)) hchoose
  rw [Classical.choose_spec (comap_surjective (k := ℚ) (K := GaussianField)
        (NumberField.FinitePlace.mk p)),
      Classical.choose_spec (comap_surjective (k := ℚ) (K := GaussianField)
        (NumberField.FinitePlace.mk q))] at hcomap
  have hmax := congrArg NumberField.FinitePlace.maximalIdeal hcomap
  simpa only [NumberField.FinitePlace.maximalIdeal_mk] using hmax

noncomputable instance infiniteGaussianFinitePlaces :
    Infinite (HeightOneSpectrum (𝓞 GaussianField)) :=
  Infinite.of_injective ratPlaceToGaussianPrime ratPlaceToGaussianPrime_injective

noncomputable instance infiniteGaussianPlaceIndex : Infinite GaussianPlaceIndex :=
  Infinite.of_injective (fun v => Sum.inl v) (fun _ _ h => Sum.inl.inj h)

/-- An index type can serve as the Gaussian place index only if it is
equivalent to GaussianPlaceIndex. -/
def IsGaussianPlaceIndexed (V : Type) : Prop :=
  Nonempty (V ≃ GaussianPlaceIndex)

/-- The finite-interval rational-prime label type is not the Gaussian place
index type: it is finite, while the Gaussian place index is infinite. -/
theorem finitePrimePlace_not_gaussianPlaceIndexed (lower upper : ℕ) :
    ¬ IsGaussianPlaceIndexed (FinitePrimePlace lower upper) := by
  rintro ⟨e⟩
  have hfin : Finite GaussianPlaceIndex :=
    Finite.of_equiv (FinitePrimePlace lower upper) e
  exact (Infinite.not_finite (α := GaussianPlaceIndex)) hfin

/-- **The identity-projection finite-interval strips are not the Gaussian place
data.**  Their index type is not equivalent to the Gaussian place index, their
projection is the identity and their geometric kernel is trivial; hence they are
a value-side finite model with a different index/carrier, not the place-indexed
data of Q(i).  They are recorded here, not substituted for the curve Pi_v or for
any D-prime-strip. -/
theorem finiteIntervalStrip_not_gaussianPlaceStrip (lower upper : ℕ) :
    ¬ IsGaussianPlaceIndexed (FinitePrimePlace lower upper) ∧
    (∀ v : FinitePrimePlace lower upper,
      (finiteLocalDPrimeStrip lower upper).proj v =
        MonoidHom.id ((finiteLocalDPrimeStrip lower upper).Pi v)) ∧
    (∀ v : FinitePrimePlace lower upper,
      (finiteLocalDPrimeStrip lower upper).geometric v = ⊥) :=
  ⟨finitePrimePlace_not_gaussianPlaceIndexed lower upper,
    GaussianPlaceStrip.finiteLocalDPrimeStrip_proj_id lower upper,
    GaussianPlaceStrip.finiteLocalDPrimeStrip_geometric_eq_bot lower upper⟩

/-- The rational-prime identity-projection model strip is likewise recorded with
its identity projection and trivial geometric kernel; it is not used as the
Gaussian place data. -/
theorem rationalPrimeStrip_identity_projection_record :
    (∀ v : RationalPrimePlace,
      localDPrimeStrip.proj v = MonoidHom.id (localDPrimeStrip.Pi v)) ∧
    (∀ v : RationalPrimePlace, localDPrimeStrip.geometric v = ⊥) :=
  ⟨GaussianPlaceStrip.localDPrimeStrip_proj_id,
    GaussianPlaceStrip.localDPrimeStrip_geometric_eq_bot⟩

/-! ## 7. Summary -/

/-- **Summary of the arithmetic local Galois side and the frozen curve-Pi
card.**  At every place of Q(i) the actual local field and its actual arithmetic
local Galois group G_v are constructed; the certified anabelioid B(G_v) has G_v
as its fundamental group; the arithmetic Galois data bundles the actual G_v
family with its certified anabelioids; the curve fundamental group Pi_v, its
surjection to G_v and the geometric kernel are frozen as
GaussianPlaceCurvePiCard; and the identity-projection finite-interval strips are
proved not to be the Gaussian place data. -/
theorem gaussianLocalGalois_summary :
    (∀ P : GaussianPlaceIndex,
      placeArithmeticGalois P =
        AbsoluteGaloisProfinite (placeLocalField P)) ∧
    (∀ P : GaussianPlaceIndex,
      (placeArithmeticAnabelioid P).group = placeArithmeticGalois P) ∧
    (placeLocalField (finiteGaussianPlace
        SourceTheaterCarrier.concreteHeightOneSpectrum) =
      (underlyingPrime concretePlace).adicCompletion GaussianField) ∧
    (∀ P : GaussianPlaceIndex,
      gaussianPlaceArithmeticGaloisData.G P =
        AbsoluteGaloisProfinite (placeLocalField P)) ∧
    (¬ IsGaussianPlaceIndexed (FinitePrimePlace 2 7)) ∧
    (∀ v : FinitePrimePlace 2 7,
      (finiteLocalDPrimeStrip 2 7).geometric v = ⊥) :=
  ⟨fun _ => rfl, fun _ => rfl, rfl, fun _ => rfl,
    finitePrimePlace_not_gaussianPlaceIndexed 2 7,
    GaussianPlaceStrip.finiteLocalDPrimeStrip_geometric_eq_bot 2 7⟩

end

end GaussianLocalGalois
end Example36
end Frobenioid
end IUTII
end LeanFormal.IUT

namespace LeanFormal.IUT.Audit

/-- Audit record for the arithmetic local Galois groups at the places of Q(i)
and the frozen curve fundamental group card.  The actual local fields and their
arithmetic absolute Galois groups G_v are constructed at every finite and
archimedean place, each B(G_v) is certified, the arithmetic Galois data is
assembled, the curve fundamental group Pi_v with its surjection to G_v and
geometric kernel is frozen as a card, and the identity-projection finite-interval
strips are proved not to be the Gaussian place data. -/
def example36GaussianLocalGalois : Obligation :=
  { id := "IUT-II.example36-gaussian-local-galois"
    source :=
      "IUT I, p. 4 and Definition 3.1(d)-(e) (arithmetic local Galois group " ++
        "G_v, curve fundamental group Pi_v, surjection Pi_v -> G_v and " ++
        "geometric kernel); IUT I, Definition 5.2 (prime strips at the places " ++
        "of a number field); IUT III, Example 3.6 (local data)"
    status := VerificationStatus.interface
    note :=
      "Source semantics: the actual absolute Galois group of the local field " ++
        "is the arithmetic group G_v, while the curve fundamental group Pi_v " ++
        "(tempered/etale fundamental group of the once-punctured elliptic " ++
        "curve over the local field) is a larger group with a surjection " ++
        "Pi_v -> G_v whose kernel is the geometric fundamental group.  " ++
        "Constructed at every place of Q(i) the actual local field " ++
        "(v.adicCompletion Q(i) at a finite place; R at a real archimedean " ++
        "place, C at a complex one), the actual arithmetic local Galois group " ++
        "G_v := Iut.AbsoluteGaloisProfinite of the local field " ++
        "(placeLocalField, placeArithmeticGalois, with definitional finite and " ++
        "archimedean component lemmas and the concrete-place instance), and the " ++
        "certified anabelioid B(G_v) of finite continuous G_v-sets " ++
        "(placeArithmeticAnabelioid; its group field is proved to be G_v and " ++
        "its certified fundamental-group structure is recorded).  The " ++
        "arithmetic Galois data GaussianPlaceArithmeticGaloisData bundles the " ++
        "actual G_v family with its certified anabelioids; it is the arithmetic " ++
        "side only and is explicitly not a D-prime-strip.  The missing " ++
        "curve-side data is frozen as the card GaussianPlaceCurvePiCard: at " ++
        "each place the once-punctured elliptic curve over the base local " ++
        "field, its tempered/etale fundamental group Pi_v, a surjective " ++
        "morphism Pi_v -> G_v, and the geometric kernel canonically as the " ++
        "closed kernel of that morphism " ++
        "(GaussianPlaceCurvePiCard.kernel, exactSequence); no inhabitant is " ++
        "constructed and no curve group is invented.  The remaining card " ++
        "requirements (identification of Pi_v with the fundamental group of " ++
        "the actual once-punctured elliptic curve; Galois action of Pi_v on " ++
        "the local value monoid with degree compatibility) are documented and " ++
        "not formalized.  Non-substitution: the identity-projection " ++
        "finite-interval strips have identity projection and trivial geometric " ++
        "kernel, and their index type FinitePrimePlace lower upper is finite " ++
        "while the Gaussian place index is infinite (proved by extending " ++
        "rational primes), so they are not the Gaussian place data " ++
        "(finitePrimePlace_not_gaussianPlaceIndexed, " ++
        "finiteIntervalStrip_not_gaussianPlaceStrip); the rational-prime model " ++
        "strip is likewise recorded, not substituted.  No theta-pilot/q-pilot/" ++
        "Tate claim is added."
    dependsOn :=
      [ "IUT-II.example36-gaussian-place-strip",
        "IUT-II.example36-source-theater-carrier",
        "IUT-I-II.concrete-source-frobenioid-bridge",
        "IUT-I.hodge-theater-carrier-and-links" ] }

end LeanFormal.IUT.Audit
