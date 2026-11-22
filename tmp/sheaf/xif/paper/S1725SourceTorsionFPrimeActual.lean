import tmp.sheaf.xif.paper.S1724PaperArithmeticActual
import tmp.sheaf.xif.paper.S1722DegreePrimeActual
import LeanFormal.IUT.IUTI.InitialTheta.SourceDefinition31Boundary
import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed
import Mathlib.Algebra.CubicDiscriminant
import Mathlib.RingTheory.Polynomial.Cyclotomic.Expand

/-!
# S1725: the actual D5 source-torsion clause for E'/F'

S1720 constructs the actual number field

  F' = SplittingField (S1687H * (X^2 + 1))

with a genuine square root of -1, the actual curve E' = S1667Punctured.baseChange F',
and actual finite places above 5 and above 7.  S1721 proves the actual torsion
condition Torsion23Rational E' (the paper's 2*3-torsion condition), and S1724
assembles the unconditional paper arithmetic data.  This file constructs the
paper's Definition 3.1(c) record SourceTorsionClause l for E'/F'.

What is actual here:

* torsionCarrier is the literal group mu_6 of sixth roots of unity in the
  algebraic closure of F' (rootsOfUnity 6 (AlgebraicClosure F')).  It has
  cardinality six, and the Fin 6 label is the exponent of a chosen primitive
  sixth root.  No PUnit, no constant label, no fake group.
* representationCarrier is the literal absolute Galois group
  Gal(F'/F') = AlgebraicClosure F' ~= AlgebraicClosure F'.
* representationGroup is the range of the actual mod-l general-linear
  representation of Gal(F'/F') on E'[l]; representation is that representation
  restricted onto its range, hence surjective by construction.
* sixTorsionIndependent is exactly Torsion23Rational E', proved by S1721 and
  re-exported by S1724.
* lTorsionCompatible is the literal residue-characteristic condition at the
  actual selected bad place: for l = 5 the place above 7 is used (residue
  characteristic 7), and for l != 5 the place above 5 is used (residue
  characteristic 5).  In both cases the coprimality is proved.

F' actually contains mu_6.  S1720 supplies sqrt(-1); independently, the
S1687 cubic has discriminant -3 times a rational square, so the product of
the differences of its three F'-rational roots divided by that rational
square root is a genuine sqrt(-3) in F'.  Then (1 + sqrt(-3))/2 is a
primitive sixth root, HasEnoughRootsOfUnity F' 6 and
Nat.card (rootsOfUnity 6 F') = 6 are proved below, and the clause's carrier
rootsOfUnity 6 (AlgebraicClosure F') is exactly the image of this
F'-rational mu_6 (S1725SixTorsionCarrierEquiv).  No roots-of-unity datum is
postulated.

What is *not* proved:

* imageContainsSL2 is the literal containment
  SL_2(F_l) <= image(Gal(F'/F') -> GL_2(F_l)) for the matrix representation
  attached to a rank-two ZMod l-basis of E'[l].  Its first component is the
  rank-two basis; beyond that it is the Serre-style open-image statement for
  this curve.  It is exposed as the explicit source input S1725ImageContainsSL2
  and the clause S1725SourceTorsionClause is constructed conditionally on it.
  No basis, no containment, and no fake True image field is introduced.

No sorry, no axiom, no admit, no True-image placeholder, and no arbitrary basis
is used in this file.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 2000000

namespace LeanFormal.IUT.XiFPaper.S1725SourceTorsionFPrimeActual

open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S1720SourceArithmeticActual
open LeanFormal.IUT.XiFPaper.S1721TorsionBaseChangeActual
open LeanFormal.IUT.XiFPaper.S1724PaperArithmeticActual
open LeanFormal.IUT.XiFPaper.S1722DegreePrimeActual
open LeanFormal.IUT.XiFPaper.S1687Torsion23RealizationActual
open LeanFormal.IUT.XiFPaper.S1712OddResidueActual
open LeanFormal.IUT.XiFPaper.S1717PlaceSevenD5Actual
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.InitialThetaSource.TorsionCarrierReduction

/-! ## 1. The actual field F', the curve E', and the selected bad place -/

/-- The actual base field F'. -/
abbrev S1725F : Type := S1720Field

/-- The actual curve E' = S1667Punctured.baseChange F'. -/
abbrev S1725Curve : PuncturedEllipticCurve S1725F := S1720Curve

/-- The residue characteristic of the actual place of F' above the rational
prime 5 is 5. -/
theorem S1725PlaceAboveFive_residueCharacteristic :
    NumberFieldFinitePlace.residueCharacteristic S1720PlaceAboveFive = 5 := by
  have h := NumberFieldFinitePlace.residueCharacteristic_comap
    (k := ℚ) (K := S1720Field) S1720PlaceAboveFive
  rw [S1720PlaceAboveFive_comap] at h
  rw [← h, S1712ConcreteFivePlace_residueCharacteristic]

/-- The residue characteristic of the actual place of F' above the rational
prime 7 is 7. -/
theorem S1725PlaceAboveSeven_residueCharacteristic :
    NumberFieldFinitePlace.residueCharacteristic S1720PlaceAboveSeven = 7 := by
  have h := NumberFieldFinitePlace.residueCharacteristic_comap
    (k := ℚ) (K := S1720Field) S1720PlaceAboveSeven
  rw [S1720PlaceAboveSeven_comap] at h
  rw [← h, concreteSevenPlace_residueCharacteristic]

/-- The actual bad place used by the D5 clause: the place above 7 when l = 5,
and the place above 5 otherwise. -/
noncomputable def S1725D5Place (l : PrimeGeFive) :
    NumberField.FinitePlace S1720Field :=
  if l.value = 5 then S1720PlaceAboveSeven else S1720PlaceAboveFive

/-- At l = 5 the selected bad place is the actual place above 7. -/
theorem S1725D5Place_of_five (l : PrimeGeFive) (h5 : l.value = 5) :
    S1725D5Place l = S1720PlaceAboveSeven := by
  simp [S1725D5Place, h5]

/-- At l != 5 the selected bad place is the actual place above 5. -/
theorem S1725D5Place_of_ne (l : PrimeGeFive) (h5 : l.value ≠ 5) :
    S1725D5Place l = S1720PlaceAboveFive := by
  simp [S1725D5Place, h5]

/-- The residue characteristic of the selected bad place. -/
theorem S1725D5Place_residueCharacteristic (l : PrimeGeFive) :
    NumberFieldFinitePlace.residueCharacteristic (S1725D5Place l) =
      if l.value = 5 then 7 else 5 := by
  by_cases h5 : l.value = 5
  · rw [S1725D5Place_of_five l h5, if_pos h5,
      S1725PlaceAboveSeven_residueCharacteristic]
  · rw [S1725D5Place_of_ne l h5, if_neg h5,
      S1725PlaceAboveFive_residueCharacteristic]

/-- E' has split multiplicative reduction at the selected bad place. -/
theorem S1725SplitAtPlace (l : PrimeGeFive) :
    S1720Curve.HasSplitMultiplicativeReductionAt (S1725D5Place l) := by
  by_cases h5 : l.value = 5
  · rw [S1725D5Place_of_five l h5]
    exact S1720SplitAtSeven
  · rw [S1725D5Place_of_ne l h5]
    exact S1720SplitAtFive

/-- The selected bad place has odd residue characteristic. -/
theorem S1725OddResidue (l : PrimeGeFive) :
    Odd (NumberFieldFinitePlace.residueCharacteristic (S1725D5Place l)) := by
  by_cases h5 : l.value = 5
  · rw [S1725D5Place_of_five l h5, S1725PlaceAboveSeven_residueCharacteristic]
    exact ⟨3, by norm_num⟩
  · rw [S1725D5Place_of_ne l h5, S1725PlaceAboveFive_residueCharacteristic]
    exact ⟨2, by norm_num⟩

/-- The residue-characteristic half of Definition 3.1(c) at the selected
actual place: l is prime to the residue characteristic of the place. -/
def S1725LTorsionCompatible (l : PrimeGeFive) : Prop :=
  Nat.Coprime l.value
    (NumberFieldFinitePlace.residueCharacteristic (S1725D5Place l))

/-- The actual residue-characteristic condition holds for every l: at l = 5
the selected place is above 7, and otherwise it is above 5. -/
theorem S1725LTorsionCompatible_proved (l : PrimeGeFive) :
    S1725LTorsionCompatible l := by
  unfold S1725LTorsionCompatible
  by_cases h5 : l.value = 5
  · rw [S1725D5Place_of_five l h5,
      S1725PlaceAboveSeven_residueCharacteristic, h5]
    exact (Nat.coprime_primes Nat.prime_five Nat.prime_seven).mpr
      (by norm_num)
  · rw [S1725D5Place_of_ne l h5,
      S1725PlaceAboveFive_residueCharacteristic]
    exact (Nat.coprime_primes l.prime Nat.prime_five).mpr h5

/-- At l = 5 the condition is the explicit coprimality of 5 and 7. -/
theorem S1725LTorsionCompatible_five :
    S1725LTorsionCompatible ⟨5, Nat.prime_five, le_rfl⟩ :=
  S1725LTorsionCompatible_proved _

/-- At l != 5 the condition is the explicit coprimality of l and 5. -/
theorem S1725LTorsionCompatible_of_ne_five (l : PrimeGeFive) (h5 : l.value ≠ 5) :
    S1725LTorsionCompatible l :=
  S1725LTorsionCompatible_proved l

/-! ## 2. The actual mu_6 torsion carrier -/

/-- The literal sixth roots of unity in the algebraic closure of F'. -/
abbrev S1725SixTorsionCarrier : Type :=
  rootsOfUnity 6 (AlgebraicClosure S1720Field)

instance S1725SixTorsionCarrierGroup : Group S1725SixTorsionCarrier :=
  inferInstance

/-- The actual carrier is finite. -/
instance S1725SixTorsionCarrierFinite : Finite S1725SixTorsionCarrier := by
  haveI : NeZero 6 := ⟨by norm_num⟩
  exact HasEnoughRootsOfUnity.finite_rootsOfUnity
    (AlgebraicClosure S1720Field) 6

/-- The actual carrier has exactly six elements. -/
theorem S1725SixTorsionCarrier_card :
    Nat.card S1725SixTorsionCarrier = 6 := by
  haveI : NeZero 6 := ⟨by norm_num⟩
  exact HasEnoughRootsOfUnity.natCard_rootsOfUnity
    (AlgebraicClosure S1720Field) 6

/-- A chosen primitive sixth root of unity in the algebraic closure, as a
unit. -/
noncomputable def S1725SixPrimitiveRootUnit :
    (AlgebraicClosure S1720Field)ˣ :=
  (Classical.choose_spec
    (HasEnoughRootsOfUnity.exists_primitiveRoot
      (AlgebraicClosure S1720Field) 6)).isUnit
    (by norm_num : 6 ≠ 0) |>.unit

/-- The same primitive root as an element of the actual mu_6 carrier. -/
noncomputable def S1725SixPrimitiveRoot : S1725SixTorsionCarrier :=
  (Classical.choose_spec
    (HasEnoughRootsOfUnity.exists_primitiveRoot
      (AlgebraicClosure S1720Field) 6)).toRootsOfUnity

/-- The chosen root is primitive of order six. -/
theorem S1725SixPrimitiveRootUnit_isPrimitive :
    IsPrimitiveRoot S1725SixPrimitiveRootUnit 6 := by
  unfold S1725SixPrimitiveRootUnit
  exact IsPrimitiveRoot.isUnit_unit (by norm_num : 6 ≠ 0)
    (Classical.choose_spec
      (HasEnoughRootsOfUnity.exists_primitiveRoot
        (AlgebraicClosure S1720Field) 6))

/-- The actual six-slot label: the exponent of the chosen primitive root.
This is the primitive-root Fin 6 label of the source clause, not an
arbitrary bijection. -/
noncomputable def S1725SixTorsionLabel
    (x : S1725SixTorsionCarrier) : Fin 6 :=
  let hx : (x : (AlgebraicClosure S1720Field)ˣ) ∈
      rootsOfUnity 6 (AlgebraicClosure S1720Field) := x.property
  let e := Classical.choose
    (S1725SixPrimitiveRootUnit_isPrimitive.eq_pow_of_mem_rootsOfUnity hx)
  ⟨e, (Classical.choose_spec
    (S1725SixPrimitiveRootUnit_isPrimitive.eq_pow_of_mem_rootsOfUnity hx)).1⟩

/-- The primitive-root label hits all six slots. -/
theorem S1725SixTorsionLabel_surjective :
    Function.Surjective S1725SixTorsionLabel := by
  intro k
  refine ⟨S1725SixPrimitiveRoot ^ (k : Nat), ?_⟩
  apply Fin.ext
  change (Classical.choose
    (S1725SixPrimitiveRootUnit_isPrimitive.eq_pow_of_mem_rootsOfUnity
      ((S1725SixPrimitiveRoot ^ (k : Nat)).property)) : Nat) = k
  have hspec := Classical.choose_spec
    (S1725SixPrimitiveRootUnit_isPrimitive.eq_pow_of_mem_rootsOfUnity
      ((S1725SixPrimitiveRoot ^ (k : Nat)).property))
  have hroot : ((S1725SixPrimitiveRoot : S1725SixTorsionCarrier) :
      (AlgebraicClosure S1720Field)ˣ) =
      S1725SixPrimitiveRootUnit := by
    apply Units.ext
    simp [S1725SixPrimitiveRoot, S1725SixPrimitiveRootUnit,
      IsPrimitiveRoot.toRootsOfUnity]
  have hpower : S1725SixPrimitiveRootUnit ^
      (Classical.choose
        (S1725SixPrimitiveRootUnit_isPrimitive.eq_pow_of_mem_rootsOfUnity
          ((S1725SixPrimitiveRoot ^ (k : Nat)).property))) =
      S1725SixPrimitiveRootUnit ^ (k : Nat) := by
    simpa [hroot] using hspec.2
  have hi := S1725SixPrimitiveRootUnit_isPrimitive.pow_inj
    hspec.1 k.isLt hpower
  exact hi

/-! ## 3. F' contains mu_6 -/

/-- The cubic S1687P as a `Cubic`, used to extract sqrt(-3) from its
discriminant. -/
def S1725TorsionCubic : Cubic ℚ :=
  ⟨463856467968, 3973952045056, 1991485440000, 6153500390625⟩

/-- The rational square root of disc(S1687P)/(-3): its square times -3 is the
discriminant of S1687P. -/
def S1725DiscriminantRoot : ℕ := 20897442725089656176640000

theorem S1725TorsionCubic_toPoly : S1725TorsionCubic.toPoly = S1687P := rfl

/-- The discriminant of the S1687 cubic is -3 times a rational square. -/
theorem S1725TorsionCubic_discr :
    S1725TorsionCubic.discr = -3 * (S1725DiscriminantRoot : ℚ) ^ 2 := by
  unfold S1725TorsionCubic S1725DiscriminantRoot Cubic.discr
  norm_num

/-- F' contains an actual square root of -3.  The three roots of S1687P lie
in the splitting field F'; the product of their differences is a square root
of disc(S1687P)/a^4, and the discriminant computation above exhibits that as
-3 times a rational square.  Dividing by the rational square root gives
sqrt(-3) in F'. -/
theorem S1725ExistsSqrtNegThree : ∃ u : S1725F, u ^ 2 = (-3 : S1725F) := by
  have ha : S1725TorsionCubic.a ≠ 0 := by norm_num [S1725TorsionCubic]
  have hsplit : (S1725TorsionCubic.toPoly.map (algebraMap ℚ S1725F)).Splits := by
    rw [S1725TorsionCubic_toPoly]
    exact S1687P_splits_F
  have hcard : (S1725TorsionCubic.toPoly.map (algebraMap ℚ S1725F)).roots.card = 3 := by
    have h := (Polynomial.splits_iff_card_roots
      (f := S1725TorsionCubic.toPoly.map (algebraMap ℚ S1725F))).mp hsplit
    rw [Polynomial.natDegree_map_eq_of_injective
      (algebraMap ℚ S1725F).injective] at h
    rw [S1725TorsionCubic_toPoly, S1687P_natDegree] at h
    exact h
  obtain ⟨x, y, z, hxyz⟩ := Multiset.card_eq_three.mp hcard
  rw [S1725TorsionCubic_toPoly] at hxyz
  have h3 : (Cubic.map (algebraMap ℚ S1725F) S1725TorsionCubic).roots = {x, y, z} := by
    change (Cubic.map (algebraMap ℚ S1725F) S1725TorsionCubic).toPoly.roots =
      {x, y, z}
    rw [Cubic.map_toPoly, S1725TorsionCubic_toPoly]
    exact hxyz
  have hdisc := Cubic.discr_eq_prod_three_roots
    (P := S1725TorsionCubic) (φ := algebraMap ℚ S1725F) ha h3
  have hT2 : (algebraMap ℚ S1725F S1725TorsionCubic.a *
      algebraMap ℚ S1725F S1725TorsionCubic.a *
      (x - y) * (x - z) * (y - z)) ^ 2 =
      (-3 : S1725F) * (S1725DiscriminantRoot : S1725F) ^ 2 := by
    rw [← hdisc, S1725TorsionCubic_discr]
    push_cast
    norm_num
  have hS : (S1725DiscriminantRoot : S1725F) ≠ 0 := by
    unfold S1725DiscriminantRoot
    norm_num
  refine ⟨(algebraMap ℚ S1725F S1725TorsionCubic.a *
    algebraMap ℚ S1725F S1725TorsionCubic.a *
    (x - y) * (x - z) * (y - z)) / (S1725DiscriminantRoot : S1725F), ?_⟩
  rw [div_pow, hT2]
  exact mul_div_cancel_right₀ (-3 : S1725F) (pow_ne_zero 2 hS)

/-- F' contains a primitive sixth root of unity, namely (1 + sqrt(-3))/2. -/
theorem S1725ExistsPrimitiveSixthRoot :
    ∃ ζ : S1725F, IsPrimitiveRoot ζ 6 := by
  obtain ⟨u, hu⟩ := S1725ExistsSqrtNegThree
  refine ⟨(1 + u) / 2, ?_⟩
  have hζ2 : ((1 + u) / 2) ^ 2 - (1 + u) / 2 + 1 = 0 := by
    field_simp
    linear_combination hu
  rw [← Polynomial.isRoot_cyclotomic_iff_charZero
    (R := S1725F) (μ := (1 + u) / 2) (by norm_num : 0 < 6)]
  rw [Polynomial.cyclotomic_six]
  simpa [Polynomial.IsRoot] using hζ2

/-- F' contains all sixth roots of unity.  This is the field-theoretic content
behind using mu_6 as the D5 torsion carrier. -/
theorem S1725HasMu6 : HasEnoughRootsOfUnity S1725F 6 := by
  obtain ⟨ζ, hζ⟩ := S1725ExistsPrimitiveSixthRoot
  exact HasEnoughRootsOfUnity.of_card_le (le_of_eq hζ.card_rootsOfUnity.symm)

/-- The group of sixth roots of unity in F' has exactly six elements. -/
theorem S1725Mu6Card : Nat.card (rootsOfUnity 6 S1725F) = 6 := by
  haveI := S1725HasMu6
  exact HasEnoughRootsOfUnity.natCard_rootsOfUnity S1725F 6

/-- The clause's carrier mu_6 of the algebraic closure is exactly the image of
the F'-rational sixth roots of unity. -/
noncomputable def S1725SixTorsionCarrierEquiv :
    rootsOfUnity 6 S1725F ≃* S1725SixTorsionCarrier :=
  rootsOfUnityEquivOfPrimitiveRoots
    (R := S1725F) (S := AlgebraicClosure S1725F)
    (f := algebraMap S1725F (AlgebraicClosure S1725F))
    (algebraMap S1725F (AlgebraicClosure S1725F)).injective
    (let ζ := Classical.choose S1725ExistsPrimitiveSixthRoot
     let hζ := Classical.choose_spec S1725ExistsPrimitiveSixthRoot
     ⟨ζ, (mem_primitiveRoots (by norm_num : 0 < 6)).mpr hζ⟩)

/-! ## 4. The actual absolute Galois group and mod-l representation -/

/-- The literal absolute Galois group of F'. -/
abbrev S1725AbsoluteGalois : Type :=
  AlgebraicClosure S1720Field ≃ₐ[S1720Field] AlgebraicClosure S1720Field

instance S1725AbsoluteGaloisGroup : Group S1725AbsoluteGalois :=
  inferInstance

/-- The actual mod-l general-linear representation of Gal(F'/F') on E'[l],
constructed without any basis hypothesis. -/
noncomputable abbrev S1725GeneralLinearRepresentation (l : PrimeGeFive) :
    S1725AbsoluteGalois →*
      LinearMap.GeneralLinearGroup (ZMod l.value)
        (S1720Curve.LTorsion l) :=
  S1720Curve.galoisActionOnLTorsionGeneralLinearRepresentation l

/-- The actual representation group: the range of the mod-l
representation. -/
abbrev S1725RepresentationGroup (l : PrimeGeFive) : Type :=
  (S1725GeneralLinearRepresentation l).range

instance S1725RepresentationGroupGroup (l : PrimeGeFive) :
    Group (S1725RepresentationGroup l) :=
  inferInstance

/-- The actual surjection onto the representation range. -/
noncomputable abbrev S1725Representation (l : PrimeGeFive) :
    S1725AbsoluteGalois →* S1725RepresentationGroup l :=
  (S1725GeneralLinearRepresentation l).rangeRestrict

/-- The representation is surjective onto its range by construction. -/
theorem S1725Representation_surjective (l : PrimeGeFive) :
    Function.Surjective (S1725Representation l) :=
  (S1725GeneralLinearRepresentation l).rangeRestrict_surjective

/-! ## 5. The explicit SL_2 image source input -/

/-- The exact rank-two torsion basis type: a ZMod l-linear equivalence
from (Fin 2 -> ZMod l) to the actual E'[l]. -/
abbrev S1725TorsionBasis (l : PrimeGeFive) : Type :=
  (Fin 2 → ZMod l.value) ≃ₗ[ZMod l.value] (S1720Curve.LTorsion l)

/-- The literal SL_2(F_l) containment for the matrix representation attached
to a chosen rank-two basis. -/
def S1725ImageTail (l : PrimeGeFive) (b : S1725TorsionBasis l) : Prop :=
  Subgroup.map Matrix.SpecialLinearGroup.toGL
    (⊤ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) (ZMod l.value))) ≤
    (S1720Curve.galoisLTorsionMatrixRepresentation l b).range

/-- The explicit source input S1725ImageContainsSL2: there exists a
rank-two basis for which the literal SL_2(F_l) containment holds.  This is
not proved and no inhabitant is asserted. -/
def S1725ImageContainsSL2 (l : PrimeGeFive) : Prop :=
  ∃ b : S1725TorsionBasis l, S1725ImageTail l b

/-- The matrix representation is literally the actual general-linear
representation transported along the chosen basis. -/
theorem S1725MatrixRepresentation_eq_transport (l : PrimeGeFive)
    (b : S1725TorsionBasis l) :
    S1720Curve.galoisLTorsionMatrixRepresentation l b =
      Matrix.GeneralLinearGroup.toLin.symm.toMonoidHom.comp
        ((LinearMap.GeneralLinearGroup.congrLinearEquiv b).symm.toMonoidHom.comp
          (S1725GeneralLinearRepresentation l)) := rfl

/-- The containment is the same in the every-SL_2-element-is-hit shape. -/
theorem S1725ImageTail_iff_forall (l : PrimeGeFive)
    (b : S1725TorsionBasis l) :
    S1725ImageTail l b ↔
      LargeImageContainsSL2
        (S1720Curve.galoisLTorsionMatrixRepresentation l b) :=
  largeImageSL2_iff_forall _

/-- The source input is literally the frozen Serre-style large-image
statement for the actual curve E'. -/
theorem S1725ImageContainsSL2_iff_serre (l : PrimeGeFive) :
    S1725ImageContainsSL2 l ↔
      SerreStyleLargeImageStatement S1720Curve l :=
  Iff.rfl

/-- The exact rank-two basis gap, in the frozen D5 vocabulary. -/
def S1725RankTwoBasisGap (l : PrimeGeFive) : Prop :=
  Nonempty (S1725TorsionBasis l)

theorem S1725RankTwoBasisGap_iff (l : PrimeGeFive) :
    S1725RankTwoBasisGap l ↔
      RankTwoTorsionBasisGap S1720Curve l :=
  Iff.rfl

/-- The image input supplies the rank-two basis: it is the first missing
component. -/
theorem S1725ImageContainsSL2_basis (l : PrimeGeFive)
    (h : S1725ImageContainsSL2 l) : S1725RankTwoBasisGap l :=
  ⟨h.choose⟩

/-- The exact first missing object of the faithful clause. -/
def S1725FirstMissing (l : PrimeGeFive) : Prop :=
  S1725ImageContainsSL2 l

theorem S1725FirstMissing_iff (l : PrimeGeFive) :
    S1725FirstMissing l ↔ S1725ImageContainsSL2 l :=
  Iff.rfl

/-- The first missing object decomposes as basis plus tail. -/
theorem S1725FirstMissing_decomposition (l : PrimeGeFive) :
    S1725FirstMissing l ↔
      ∃ b : S1725TorsionBasis l, S1725ImageTail l b :=
  Iff.rfl

/-! ## 6. The actual 2 * 3-torsion content from S1721/S1724 -/

/-- The paper's condition (b) for E'/F': all 2 * 3-torsion points are
rational over F'. -/
def S1725SixTorsionIndependent : Prop :=
  PuncturedEllipticCurve.Torsion23Rational S1720Curve

/-- The S1721/S1724 content: Torsion23Rational E' is a theorem. -/
theorem S1725SixTorsionIndependent_proved :
    S1725SixTorsionIndependent :=
  S1724Torsion23

/-- The clause's field is definitionally the S1721 statement. -/
theorem S1725SixTorsionIndependent_eq_S1721 :
    S1725SixTorsionIndependent =
      PuncturedEllipticCurve.Torsion23Rational S1720Curve :=
  rfl

/-! ## 7. The actual D5 clause -/

/-- The actual D5 clause for E'/F', conditional on the explicit source input
S1725ImageContainsSL2 l.  The carrier, label, absolute Galois group, mod-l
representation, surjection, six-torsion rationality, and l-compatibility are
the actual objects constructed above.  No image or SL_2 content is assumed
beyond hI. -/
noncomputable def S1725SourceTorsionClause (l : PrimeGeFive)
    (hI : S1725ImageContainsSL2 l) :
    SourceTorsionClause.{0, 0, 0} l where
  torsionCarrier := S1725SixTorsionCarrier
  torsionCarrierLaw := inferInstance
  torsionLabel := S1725SixTorsionLabel
  torsionNonempty := ⟨1⟩
  representationCarrier := S1725AbsoluteGalois
  representationCarrierLaw := inferInstance
  representationGroup := S1725RepresentationGroup l
  representationGroupLaw := inferInstance
  representation := S1725Representation l
  representation_surjective := S1725Representation_surjective l
  imageContainsSL2 := S1725ImageContainsSL2 l
  imageContainsSL2_proved := hI
  sixTorsionIndependent := S1725SixTorsionIndependent
  sixTorsionIndependent_proved := S1725SixTorsionIndependent_proved
  lTorsionCompatible := S1725LTorsionCompatible l
  lTorsionCompatible_proved := S1725LTorsionCompatible_proved l

@[simp] theorem S1725SourceTorsionClause_torsionCarrier (l : PrimeGeFive)
    (hI : S1725ImageContainsSL2 l) :
    (S1725SourceTorsionClause l hI).torsionCarrier =
      S1725SixTorsionCarrier := rfl

@[simp] theorem S1725SourceTorsionClause_torsionLabel (l : PrimeGeFive)
    (hI : S1725ImageContainsSL2 l) :
    (S1725SourceTorsionClause l hI).torsionLabel =
      S1725SixTorsionLabel := rfl

@[simp] theorem S1725SourceTorsionClause_representationCarrier
    (l : PrimeGeFive) (hI : S1725ImageContainsSL2 l) :
    (S1725SourceTorsionClause l hI).representationCarrier =
      S1725AbsoluteGalois := rfl

@[simp] theorem S1725SourceTorsionClause_representationGroup
    (l : PrimeGeFive) (hI : S1725ImageContainsSL2 l) :
    (S1725SourceTorsionClause l hI).representationGroup =
      S1725RepresentationGroup l := rfl

@[simp] theorem S1725SourceTorsionClause_representation
    (l : PrimeGeFive) (hI : S1725ImageContainsSL2 l) :
    (S1725SourceTorsionClause l hI).representation =
      S1725Representation l := rfl

@[simp] theorem S1725SourceTorsionClause_imageContainsSL2
    (l : PrimeGeFive) (hI : S1725ImageContainsSL2 l) :
    (S1725SourceTorsionClause l hI).imageContainsSL2 =
      S1725ImageContainsSL2 l := rfl

@[simp] theorem S1725SourceTorsionClause_sixTorsionIndependent
    (l : PrimeGeFive) (hI : S1725ImageContainsSL2 l) :
    (S1725SourceTorsionClause l hI).sixTorsionIndependent =
      PuncturedEllipticCurve.Torsion23Rational S1720Curve := rfl

@[simp] theorem S1725SourceTorsionClause_lTorsionCompatible
    (l : PrimeGeFive) (hI : S1725ImageContainsSL2 l) :
    (S1725SourceTorsionClause l hI).lTorsionCompatible =
      S1725LTorsionCompatible l := rfl

/-- The clause's label is the actual primitive-root label, hence surjective. -/
theorem S1725SourceTorsionClause_label_surjective (l : PrimeGeFive)
    (hI : S1725ImageContainsSL2 l) :
    Function.Surjective (S1725SourceTorsionClause l hI).torsionLabel := by
  simpa using S1725SixTorsionLabel_surjective

/-- The clause's representation is the actual mod-l representation, hence
surjective onto its range. -/
theorem S1725SourceTorsionClause_representation_surjective
    (l : PrimeGeFive) (hI : S1725ImageContainsSL2 l) :
    Function.Surjective (S1725SourceTorsionClause l hI).representation :=
  (S1725SourceTorsionClause l hI).representation_surjective

/-- The three source clause fields of the constructed clause. -/
theorem S1725SourceTorsionClause_fields (l : PrimeGeFive)
    (hI : S1725ImageContainsSL2 l) :
    (S1725SourceTorsionClause l hI).imageContainsSL2 ∧
      (S1725SourceTorsionClause l hI).sixTorsionIndependent ∧
      (S1725SourceTorsionClause l hI).lTorsionCompatible :=
  ⟨hI, S1725SixTorsionIndependent_proved,
    S1725LTorsionCompatible_proved l⟩

/-- The clause's six-torsion proof is literally the S1724 theorem. -/
theorem S1725SourceTorsionClause_sixTorsion_proof_eq (l : PrimeGeFive)
    (hI : S1725ImageContainsSL2 l) :
    (S1725SourceTorsionClause l hI).sixTorsionIndependent_proved =
      S1724Torsion23 := rfl

/-- The clause's l-compatibility field is literally the actual
residue-characteristic condition at the selected bad place. -/
theorem S1725SourceTorsionClause_lTorsionCompatible_place
    (l : PrimeGeFive) (hI : S1725ImageContainsSL2 l) :
    (S1725SourceTorsionClause l hI).lTorsionCompatible =
      S1725LTorsionCompatible l := rfl

/-- Conditional existence of the actual D5 clause from the explicit image
input. -/
theorem S1725SourceTorsionClause_nonempty_of_image (l : PrimeGeFive)
    (hI : S1725ImageContainsSL2 l) :
    Nonempty (SourceTorsionClause.{0, 0, 0} l) :=
  ⟨S1725SourceTorsionClause l hI⟩

/-- The clause exists at every l for which the explicit image source input is
supplied. -/
theorem S1725D5_exists_of_image (l : PrimeGeFive)
    (hI : S1725ImageContainsSL2 l) :
    ∃ T : SourceTorsionClause.{0, 0, 0} l,
      T.torsionCarrier = S1725SixTorsionCarrier ∧
        T.sixTorsionIndependent =
          PuncturedEllipticCurve.Torsion23Rational S1720Curve ∧
        T.lTorsionCompatible = S1725LTorsionCompatible l :=
  ⟨S1725SourceTorsionClause l hI, rfl, rfl, rfl⟩

/-! ## 8. The D5 slot of SourceDefinition31Data -/

/-- At universe u = 0, filling the torsion (D5) slot of a source contract with
the actual E'/F' clause. -/
noncomputable def S1725FillD5 (l : PrimeGeFive)
    (S : SourceDefinition31Data.{0} l)
    (hI : S1725ImageContainsSL2 l) :
    SourceDefinition31Data.{0} l :=
  { S with torsion := S1725SourceTorsionClause l hI }

/-- The D5 slot of the filled contract is the actual clause. -/
@[simp] theorem S1725FillD5_torsion (l : PrimeGeFive)
    (S : SourceDefinition31Data.{0} l)
    (hI : S1725ImageContainsSL2 l) :
    (S1725FillD5 l S hI).torsion =
      S1725SourceTorsionClause l hI := rfl

/-! ## 9. Axiom footprint -/

#print axioms S1725PlaceAboveFive_residueCharacteristic
#print axioms S1725PlaceAboveSeven_residueCharacteristic
#print axioms S1725D5Place_residueCharacteristic
#print axioms S1725SplitAtPlace
#print axioms S1725OddResidue
#print axioms S1725LTorsionCompatible_proved
#print axioms S1725SixTorsionCarrier_card
#print axioms S1725TorsionCubic_discr
#print axioms S1725ExistsSqrtNegThree
#print axioms S1725ExistsPrimitiveSixthRoot
#print axioms S1725HasMu6
#print axioms S1725Mu6Card
#print axioms S1725SixTorsionCarrierEquiv
#print axioms S1725SixTorsionLabel_surjective
#print axioms S1725Representation_surjective
#print axioms S1725ImageContainsSL2_iff_serre
#print axioms S1725ImageContainsSL2_basis
#print axioms S1725SixTorsionIndependent_proved
#print axioms S1725SourceTorsionClause
#print axioms S1725SourceTorsionClause_fields
#print axioms S1725SourceTorsionClause_sixTorsion_proof_eq
#print axioms S1725D5_exists_of_image
#print axioms S1725FillD5

end LeanFormal.IUT.XiFPaper.S1725SourceTorsionFPrimeActual
