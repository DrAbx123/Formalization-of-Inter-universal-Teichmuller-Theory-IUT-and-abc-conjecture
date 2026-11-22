import LeanFormal.IUT.IUTII.Frobenioid.Example36EllipticCurveAnabelioid
import LeanFormal.IUT.IUTII.Frobenioid.Example36EllipticCurveTateHigherLevel
import Mathlib.Algebra.Group.TypeTags.Basic
import Mathlib.Tactic

/-!
# Source curve Pi card: the true once-punctured-elliptic-curve target and the
# full Tate module vs the pro-2 quotient

Source anchor: review N4 of IUT II, Sections 3-6, boundary item (1).  The two
preceding finite-level files (Example36EllipticCurveAnabelioid.lean and
Example36EllipticCurveTateHigherLevel.lean) are mathematically valid at the
finite levels E[2] and E[4], but their docstrings previously wrote the future
source target as an exact sequence with T_2(E) as the geometric kernel of the
etale fundamental group of the proper elliptic curve.  That target is wrong in
two directions:

* For the proper elliptic curve, the middle term is the full arithmetic etale
  fundamental group, whose geometric kernel is the full Tate module
  prod_l T_l(E) (a product over ALL primes l), not T_2(E); T_2(E) is only the
  pro-2 quotient/factor.
* More importantly, IUT I (printed p. 25) needs the whole nonabelian etale
  fundamental group of the ONCE-PUNCTURED elliptic curve X = E minus O.  An
  inverse limit of the abelian finite groups E[2^n] cannot recover the
  nonabelian punctured-curve fundamental group or the cusp inertia.

This file freezes the corrected target as data cards.  It does NOT construct the
source object, does not produce any inhabitant of the cards, and no theorem in
the tree consumes a card.  The cards are plain structures/PProps over the
existing certified anabelioid API and reuse the concrete finite groups; no
fake group and no axiom is introduced.

## (1) The source Pi card (SourceCurvePiData)

For the concrete once-punctured curve X = (y^2 = x^3 - x, removed origin O) over
Q, the card records: the source anabelioid and its whole (nonabelian) etale
fundamental group Pi = pi1^et(X); the arithmetic projection Pi -> G_Q =
Gal(Qbar/Q) (surjective); the geometric kernel as the kernel of that genuine
projection; the pro-2 completion Pi -> Pi^{pro-2}; and the finite-level E[2] and
E[4] layers as finite abelian pro-2 quotient layers equivalent to the concrete
constructed groups (quotient relations, NOT identifications of Pi with a finite
group).  The card also records that the source anabelioid is not one of the
constructed finite-level split product models.

## (2) The full Tate module vs T_2 card (SourceFullTateModuleData)

For each prime l the l-adic Tate module T_l(E) (profinite, nontrivial), the full
arithmetic Tate module prod_l T_l(E) as a product over all primes, and the pro-2
Tate module T_2(E) as the l = 2 component.  T_2 is therefore a factor/quotient
of the full module, never equal to it.

## (3) Why B(Gal(Qbar/Q) x E[2^n]) is NOT the curve anabelioid

The constructed tateLevelTwoAnabelioidTotal and tateLevelFourAnabelioidTotal are
finite-level split product models: their groups are the direct product of
G_Q with the finite abelian layer E[2] or E[4] (this is proved, not assumed, by
tateLevelTwoAnabelioidTotal_isConstructedFiniteLevelProductModel and
tateLevelFourAnabelioidTotal_isConstructedFiniteLevelProductModel).  They are
NOT the once-punctured curve anabelioid: the source needs (a) the punctured
curve X rather than the proper elliptic curve, (b) the nonabelian geometric
fundamental group of X (free profinite of rank two) rather than the abelian
E[2^n], and (c) cusp inertia at the puncture, none of which is present in a
split product with a finite abelian second factor.  The frozen statement of
this non-identification is
FiniteLevelProductModelIsNotSourceCurve; it is a card, not a theorem.

## Honest boundary

* No inhabitant of SourceCurvePiData, SourceFullTateModuleData or
  SourceCurvePiCard is constructed.  The single declaration SourceCurvePiCard is
  a Prop recording the frozen source obligation; it is not proved and nothing
  consumes it.  In particular the file does not claim that the source curve
  Pi, the full Tate module, or the nonabelian punctured-curve fundamental group
  exist in the tree.
* The genuine finite-level results are only the finite abelian pro-2 layer
  theorems for the constructed E[2] and E[4] (finite, nontrivial, commutative,
  exponent a power of two) and the split product model identification for the
  two constructed total anabelioids.
* Not constructed: the inverse system E[2^(n+1)] -> E[2^n], the pro-2 limit
  T_2(E), the full product prod_l T_l(E), the semidirect extension
  1 -> pi1^geo(X) -> pi1^et(X) -> G_Q -> 1, the punctured-curve anabelioid, its
  cusp inertia, continuity of the Galois action on the source Pi, and the
  identification of the source anabelioid with the curve's etale fundamental
  group anabelioid.
* No theta / q-pilot / Tate identification and no arithmetic degree, log-volume
  or comparison statement is claimed.

## Relation to the existing finite-level files

Example36EllipticCurveAnabelioid.lean (mod-2) and
Example36EllipticCurveTateHigherLevel.lean (mod-4) remain valid as finite
abelian layer computations.  Their docstrings have been corrected to point to
this card and to state the corrected source target instead of the previous
T_2-only exact-sequence wording.  Their proved theorem statements are
unchanged.
-/

noncomputable section

namespace LeanFormal.IUT.IUTII.Frobenioid
namespace Example36

open WeierstrassCurve

/-! ## 1. The constructed finite levels are finite abelian pro-2 layers -/

/-- The concrete 2-torsion group is nontrivial. -/
theorem tateLevelTwoTorsion_nontrivial : Nontrivial tateLevelTwoTorsion :=
  ⟨tateLevelTwoPointZeroZero, 0, tateLevelTwoPointZeroZero_ne_zero⟩

/-- The concrete 4-torsion group is nontrivial. -/
theorem tateLevelFourTorsion_nontrivial : Nontrivial tateLevelFourTorsion :=
  ⟨tateLevelFourPointZeroZero, 0, tateLevelFourPointZeroZero_ne_zero⟩

/-- Every element of the constructed E[2] is killed by 2. -/
theorem tateLevelTwoTorsion_pow_two :
    ∀ x : Multiplicative tateLevelTwoTorsion, x ^ 2 = 1 := by
  intro x
  apply Multiplicative.toAdd.injective
  rw [toAdd_pow, toAdd_one]
  apply Subtype.ext
  simp only [AddSubgroup.coe_nsmul, ZeroMemClass.coe_zero]
  exact tateLevelTwo_mem_iff.mp (Multiplicative.toAdd x).2

/-- Every element of the constructed E[4] is killed by 4. -/
theorem tateLevelFourTorsion_pow_four :
    ∀ x : Multiplicative tateLevelFourTorsion, x ^ 4 = 1 := by
  intro x
  apply Multiplicative.toAdd.injective
  rw [toAdd_pow, toAdd_one]
  apply Subtype.ext
  simp only [AddSubgroup.coe_nsmul, ZeroMemClass.coe_zero]
  exact tateLevelFour_mem_iff.mp (Multiplicative.toAdd x).2

/-- A finite abelian pro-2 group, as a plain group: finite, nontrivial,
commutative, of exponent a power of two. -/
def IsFiniteAbelianProTwoLayer (T : Type) [Group T] : Prop :=
  Finite T ∧ Nontrivial T ∧ (∀ a b : T, a * b = b * a) ∧
    ∃ n : ℕ, ∀ a : T, a ^ (2 ^ n) = 1

/-- The constructed E[2] is a finite abelian pro-2 layer. -/
theorem tateLevelTwoTorsion_isFiniteAbelianProTwoLayer :
    IsFiniteAbelianProTwoLayer (Multiplicative tateLevelTwoTorsion) := by
  haveI : Nontrivial tateLevelTwoTorsion := tateLevelTwoTorsion_nontrivial
  have hN : Nontrivial (Multiplicative tateLevelTwoTorsion) := inferInstance
  refine ⟨inferInstance, hN, ?_, ⟨1, fun a => ?_⟩⟩
  · intro a b
    apply Multiplicative.toAdd.injective
    rw [toAdd_mul, toAdd_mul, add_comm]
  · simpa using tateLevelTwoTorsion_pow_two a

/-- The constructed E[4] is a finite abelian pro-2 layer. -/
theorem tateLevelFourTorsion_isFiniteAbelianProTwoLayer :
    IsFiniteAbelianProTwoLayer (Multiplicative tateLevelFourTorsion) := by
  haveI : Nontrivial tateLevelFourTorsion := tateLevelFourTorsion_nontrivial
  have hN : Nontrivial (Multiplicative tateLevelFourTorsion) := inferInstance
  refine ⟨inferInstance, hN, ?_, ⟨2, fun a => ?_⟩⟩
  · intro a b
    apply Multiplicative.toAdd.injective
    rw [toAdd_mul, toAdd_mul, add_comm]
  · simpa using tateLevelFourTorsion_pow_four a

/-- A finite abelian pro-2 layer as a profinite group. -/
def IsFiniteAbelianProTwoLayerProfinite (B : ProfiniteGrp) : Prop :=
  IsFiniteAbelianProTwoLayer (B : Type)

/-! ## 2. The constructed finite-level split product models -/

/-- The constructed finite-level product models: total group G_Q x E[2] or
G_Q x E[4].  This is a concrete structural predicate on anabelioids, not a
claim about the source curve. -/
def IsConstructedFiniteLevelProductModel (A : Iut.EtaleFundamentalGroup) : Prop :=
  A.group = tateLevelTwoAnabelioidTotalGroup ∨
    A.group = tateLevelFourAnabelioidTotalGroup

theorem tateLevelTwoAnabelioidTotal_isConstructedFiniteLevelProductModel :
    IsConstructedFiniteLevelProductModel tateLevelTwoAnabelioidTotal :=
  Or.inl rfl

theorem tateLevelFourAnabelioidTotal_isConstructedFiniteLevelProductModel :
    IsConstructedFiniteLevelProductModel tateLevelFourAnabelioidTotal :=
  Or.inr rfl

/-! ## 3. The concrete once-punctured curve and the source Pi card -/

/-- The concrete curve y^2 = x^3 - x over Q. -/
def sourceCurve : WeierstrassCurve ℚ := curveY2EqX3SubX

/-- The origin (the identity) of the concrete curve, i.e. the point removed by
the puncture. -/
def sourcePuncture : WeierstrassCurve.Affine.Point sourceCurve := .zero

/-- A once-punctured elliptic curve over Q: an elliptic curve together with a
chosen puncture point (the removed origin). -/
structure OncePuncturedEllipticCurve where
  curve : WeierstrassCurve ℚ
  isElliptic : curve.IsElliptic
  puncture : WeierstrassCurve.Affine.Point curve

/-- The concrete once-punctured curve X = (y^2 = x^3 - x, removed origin). -/
def sourceOncePuncturedEllipticCurve : OncePuncturedEllipticCurve where
  curve := sourceCurve
  isElliptic := curveY2EqX3SubX_isElliptic
  puncture := sourcePuncture

/-- Frozen source card for the once-punctured curve X: the whole nonabelian
etale fundamental group Pi = pi1^et(X), the arithmetic projection Pi -> G_Q,
the geometric kernel, the pro-2 completion, and the finite E[2]/E[4] layers as
quotient layers equivalent to the constructed finite groups.  This is DATA: no
inhabitant is constructed and no theorem consumes it. -/
structure SourceCurvePiData (X : OncePuncturedEllipticCurve) where
  /-- A connected anabelioid for the once-punctured curve X. -/
  sourceAnabelioid : Iut.EtaleFundamentalGroup
  /-- The whole (nonabelian) etale fundamental group of X. -/
  piOne : ProfiniteGrp
  /-- The source group is the group of the source anabelioid. -/
  sourceAnabelioid_group : sourceAnabelioid.group = piOne
  /-- The arithmetic projection to the absolute Galois group of Q. -/
  arithmeticProjection : piOne ⟶ rationalAbsoluteGaloisGroup
  /-- The arithmetic projection is surjective. -/
  arithmeticProjection_surjective : Function.Surjective arithmeticProjection.hom.toMonoidHom
  /-- The geometric kernel, as a subgroup of the source group. -/
  geometricKernel : Subgroup (piOne : Type)
  /-- The geometric kernel is the kernel of the arithmetic projection. -/
  geometricKernel_is_kernel : geometricKernel = arithmeticProjection.hom.toMonoidHom.ker
  /-- The pro-2 completion of the source group. -/
  proTwoCompletion : ProfiniteGrp
  /-- The pro-2 quotient map from the source group. -/
  proTwoQuotient : piOne ⟶ proTwoCompletion
  /-- The pro-2 quotient map is surjective. -/
  proTwoQuotient_surjective : Function.Surjective proTwoQuotient.hom.toMonoidHom
  /-- The mod-2 finite layer (a quotient of the pro-2 completion). -/
  modTwoLayer : ProfiniteGrp
  modTwoLayerQuotient : proTwoCompletion ⟶ modTwoLayer
  modTwoLayerQuotient_surjective : Function.Surjective modTwoLayerQuotient.hom.toMonoidHom
  /-- The mod-2 layer is a finite abelian pro-2 layer. -/
  modTwoLayer_isFiniteAbelian : IsFiniteAbelianProTwoLayerProfinite modTwoLayer
  /-- The mod-2 layer is equivalent to the constructed E[2]: this is a quotient
  relation, not an identification of the source group with E[2]. -/
  modTwoLayer_equiv_constructed : modTwoLayer ≃* Multiplicative tateLevelTwoTorsion
  /-- The mod-4 finite layer (a quotient of the pro-2 completion). -/
  modFourLayer : ProfiniteGrp
  modFourLayerQuotient : proTwoCompletion ⟶ modFourLayer
  modFourLayerQuotient_surjective : Function.Surjective modFourLayerQuotient.hom.toMonoidHom
  /-- The mod-4 layer is a finite abelian pro-2 layer. -/
  modFourLayer_isFiniteAbelian : IsFiniteAbelianProTwoLayerProfinite modFourLayer
  /-- The mod-4 layer is equivalent to the constructed E[4]: this is a quotient
  relation, not an identification of the source group with E[4]. -/
  modFourLayer_equiv_constructed : modFourLayer ≃* Multiplicative tateLevelFourTorsion
  /-- The source anabelioid is not one of the constructed finite-level split
  product models (punctured curve, nonabelian pi1, cusp inertia are missing). -/
  notSplitProductModel : ¬ IsConstructedFiniteLevelProductModel sourceAnabelioid

/-- The source Pi card is realized.  This is a frozen source obligation: it is
not proved here and it has no consumer in the tree. -/
def SourceCurvePiDataRealized (X : OncePuncturedEllipticCurve) : Prop :=
  Nonempty (SourceCurvePiData X)

/-! ## 4. The full Tate module vs the pro-2 Tate module -/

/-- Frozen card for the Tate modules: for every prime l the l-adic Tate module
T_l(E), the full arithmetic Tate module prod_l T_l(E) as a product over all
primes, and the pro-2 Tate module T_2(E) as the l = 2 component.  This is DATA:
no inhabitant is constructed and no theorem consumes it. -/
structure SourceFullTateModuleData (X : OncePuncturedEllipticCurve) where
  /-- The l-adic Tate module T_l(E) for each prime l. -/
  tateComponent : (l : ℕ) → Nat.Prime l → ProfiniteGrp
  /-- Every Tate component is nontrivial. -/
  tateComponent_nontrivial : ∀ (l : ℕ) (hl : Nat.Prime l),
    Nontrivial (tateComponent l hl : Type)
  /-- The pro-2 Tate module T_2(E). -/
  proTwoTateModule : ProfiniteGrp
  /-- T_2 is the l = 2 component of the full product. -/
  proTwoIsComponentTwo : proTwoTateModule ≃* (tateComponent 2 Nat.prime_two : Type)
  /-- The full arithmetic Tate module prod_l T_l(E). -/
  fullTateModule : ProfiniteGrp
  /-- Each prime component is a factor of the full product. -/
  componentToFull : (l : ℕ) → (hl : Nat.Prime l) → (tateComponent l hl ⟶ fullTateModule)
  /-- The pro-2 component is a factor of the full product. -/
  proTwoToFull : proTwoTateModule ⟶ fullTateModule

/-- The full Tate module card is realized.  Frozen source obligation: not
proved here and no consumer in the tree. -/
def SourceFullTateModuleDataRealized (X : OncePuncturedEllipticCurve) : Prop :=
  Nonempty (SourceFullTateModuleData X)

/-! ## 5. The frozen card for the concrete curve and the non-identification -/

/-- The frozen card for the concrete once-punctured curve X = (y^2 = x^3 - x,
removed origin): the source Pi data together with the full Tate module data.
This is a source obligation, not a theorem of this file; it is not proved and
has no consumer. -/
def SourceCurvePiCard : Prop :=
  SourceCurvePiDataRealized sourceOncePuncturedEllipticCurve ∧
    SourceFullTateModuleDataRealized sourceOncePuncturedEllipticCurve

/-- The frozen non-identification statement: no constructed finite-level split
product model is the source anabelioid of a once-punctured elliptic curve.
This is a card, not a theorem; it records why B(Gal(Qbar/Q) x E[2^n]) is NOT the
curve anabelioid (the source needs the punctured curve, its nonabelian pi1, and
its cusp inertia). -/
def FiniteLevelProductModelIsNotSourceCurve : Prop :=
  ∀ (A : Iut.EtaleFundamentalGroup),
    IsConstructedFiniteLevelProductModel A →
      ¬ ∃ (X : OncePuncturedEllipticCurve) (d : SourceCurvePiData X),
        d.sourceAnabelioid = A

end Example36
end LeanFormal.IUT.IUTII.Frobenioid
