import tmp.sheaf.xif.paper.S1714AdmissibleActual
import tmp.sheaf.xif.paper.S1708NinePointInjectionActual
import LeanFormal.IUT.IUTI.InitialTheta.SourceDefinition31Boundary
import LeanFormal.IUT.IUTI.InitialTheta.SourceTorsionCarrierReduction
import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed

/-!
# S1715: the actual D5 source-torsion clause for the S1714 admissible curve

The S1714 input is the actual curve

  E : y^2 = x^3 + (61/64) x^2 - (125/64) x

base-changed to the actual number field F = S1687Field, with the actual
place above 5, actual rational 2*3-torsion (S1708Torsion23Rational),
actual split multiplicative reduction at that place (S1713), and actual odd
residue characteristic (S1712).  This file constructs the paper's
Definition 3.1(c) record SourceTorsionClause l for that actual data.

What is actual here:

* torsionCarrier is the literal group mu_6 of sixth roots of unity in the
  algebraic closure of F (rootsOfUnity 6 (AlgebraicClosure F)).  It has
  cardinality six, and the Fin 6 label is the exponent of the chosen
  primitive sixth root.  No PUnit, no constant label, no fake group.
* representationCarrier is the literal absolute Galois group
  Gal(Fbar/F) = AlgebraicClosure F ~= AlgebraicClosure F.
* representationGroup is the range of the actual mod-l general-linear
  representation of Gal(Fbar/F) on E[l]; representation is that
  representation restricted onto its range, hence surjective by construction.
  No basis and no large-image statement is assumed for this field.
* sixTorsionIndependent is exactly Torsion23Rational of the actual
  base-changed curve, proved by S1708Torsion23Rational (which rests on the
  nine-point injection, the F-rational 3-torsion cardinality, and the actual
  S1687 splitting field).
* lTorsionCompatible is the literal residue-characteristic half of
  Definition 3.1(c) at the actual place above 5: the residue characteristic
  is 5, so coprimality with l is exactly l != 5.  The iff is proved and
  identified with the S1637 criterion; for every l != 5 the condition is
  actual.

What is *not* proved:

* imageContainsSL2 is the literal containment
  SL_2(F_l) <= image(Gal(Fbar/F) -> GL_2(F_l)) for the matrix
  representation attached to a rank-two ZMod l-basis of E[l].  Its first
  component is the rank-two basis; beyond that it is the Serre-style
  open-image statement for this curve.  Neither is available in the tree.
  No basis, no containment, and no fake True image field is introduced.
  Instead S1715ImageContainsSL2 is an explicit source input, and the clause
  S1715SourceTorsionClause is constructed conditionally on it.

The exact first missing object is therefore

  S1715ImageContainsSL2 l
    = exists basis : (Fin 2 -> ZMod l) ~= E[l], SL_2(F_l) <= rho_{l,basis}.range.

At l = 5 the actual residue-characteristic condition is false (the bad
place has characteristic 5), so the faithful clause cannot exist at l = 5;
this is the same arithmetic obstruction recorded in S1637.  For every
l != 5 the only remaining input is S1715ImageContainsSL2 l.

No sorry, no axiom, no admit, no True-image placeholder, and no
arbitrary basis is used in this file.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 1000000

namespace LeanFormal.IUT.XiFPaper.S1715SourceTorsionClauseActual

open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S1667AdmissibleCurveActual
open LeanFormal.IUT.XiFPaper.S1687Torsion23RealizationActual
open LeanFormal.IUT.XiFPaper.S1708NinePointInjectionActual
open LeanFormal.IUT.XiFPaper.S1712OddResidueActual
open LeanFormal.IUT.XiFPaper.S1714AdmissibleActual
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.InitialThetaSource.TorsionCarrierReduction

/-! ## 1. The actual admissible arithmetic input -/

/-- The actual curve of S1687/S1714: the S1667 Legendre curve base-changed to
the actual splitting field S1687Field. -/
abbrev S1715Curve : PuncturedEllipticCurve S1687Field :=
  S1667Punctured.baseChange S1687Field

/-- S1714's actual admissibility statement, re-exported at this interface. -/
theorem S1715Admissible : S1667Admissible :=
  S1714Admissible

/-- The actual place above 5 has odd residue characteristic. -/
theorem S1715OddResidue :
    Odd (NumberFieldFinitePlace.residueCharacteristic S1687PlaceAboveFive) := by
  simpa
    [LeanFormal.IUT.XiFPaper.S1711AdmissibleRealizationActual.S1711OddResidueCharacteristic]
    using S1712Odd

/-- The actual curve has split multiplicative reduction at the actual place
above 5 (S1713 transported to the actual field, S1687). -/
theorem S1715SplitReduction :
    S1715Curve.HasSplitMultiplicativeReductionAt S1687PlaceAboveFive :=
  S1687Split_of_rational S1714Split

/-! ## 2. The actual mu_6 torsion carrier -/

/-- The actual sixth roots of unity in the algebraic closure of the actual
base field.  This is the literal group mu_6, not an abstract placeholder. -/
abbrev S1715SixTorsionCarrier : Type :=
  rootsOfUnity 6 (AlgebraicClosure S1687Field)

instance S1715SixTorsionCarrierGroup : Group S1715SixTorsionCarrier :=
  inferInstance

/-- The actual carrier is finite, with the cardinality computed below. -/
instance S1715SixTorsionCarrierFinite : Finite S1715SixTorsionCarrier := by
  haveI : NeZero 6 := ⟨by norm_num⟩
  exact HasEnoughRootsOfUnity.finite_rootsOfUnity
    (AlgebraicClosure S1687Field) 6

/-- The actual carrier has exactly six elements. -/
theorem S1715SixTorsionCarrier_card :
    Nat.card S1715SixTorsionCarrier = 6 := by
  haveI : NeZero 6 := ⟨by norm_num⟩
  exact HasEnoughRootsOfUnity.natCard_rootsOfUnity
    (AlgebraicClosure S1687Field) 6

/-- A chosen primitive sixth root of unity in the algebraic closure, as a
unit. -/
noncomputable def S1715SixPrimitiveRootUnit :
    (AlgebraicClosure S1687Field)ˣ :=
  (Classical.choose_spec
    (HasEnoughRootsOfUnity.exists_primitiveRoot
      (AlgebraicClosure S1687Field) 6)).isUnit
    (by norm_num : 6 ≠ 0) |>.unit

/-- The same primitive root as an element of the actual mu_6 carrier. -/
noncomputable def S1715SixPrimitiveRoot : S1715SixTorsionCarrier :=
  (Classical.choose_spec
    (HasEnoughRootsOfUnity.exists_primitiveRoot
      (AlgebraicClosure S1687Field) 6)).toRootsOfUnity

/-- The chosen root is primitive of order six. -/
theorem S1715SixPrimitiveRootUnit_isPrimitive :
    IsPrimitiveRoot S1715SixPrimitiveRootUnit 6 := by
  unfold S1715SixPrimitiveRootUnit
  exact IsPrimitiveRoot.isUnit_unit (by norm_num : 6 ≠ 0)
    (Classical.choose_spec
      (HasEnoughRootsOfUnity.exists_primitiveRoot
        (AlgebraicClosure S1687Field) 6))

/-- The actual six-slot label: the exponent of the chosen primitive root.
This is the primitive-root Fin 6 label of the source clause, not an
arbitrary bijection. -/
noncomputable def S1715SixTorsionLabel
    (x : S1715SixTorsionCarrier) : Fin 6 :=
  let hx : (x : (AlgebraicClosure S1687Field)ˣ) ∈
      rootsOfUnity 6 (AlgebraicClosure S1687Field) := x.property
  let e := Classical.choose
    (S1715SixPrimitiveRootUnit_isPrimitive.eq_pow_of_mem_rootsOfUnity hx)
  ⟨e, (Classical.choose_spec
    (S1715SixPrimitiveRootUnit_isPrimitive.eq_pow_of_mem_rootsOfUnity hx)).1⟩

/-- The primitive-root label hits all six slots. -/
theorem S1715SixTorsionLabel_surjective :
    Function.Surjective S1715SixTorsionLabel := by
  intro k
  refine ⟨S1715SixPrimitiveRoot ^ (k : Nat), ?_⟩
  apply Fin.ext
  change (Classical.choose
    (S1715SixPrimitiveRootUnit_isPrimitive.eq_pow_of_mem_rootsOfUnity
      ((S1715SixPrimitiveRoot ^ (k : Nat)).property)) : Nat) = k
  have hspec := Classical.choose_spec
    (S1715SixPrimitiveRootUnit_isPrimitive.eq_pow_of_mem_rootsOfUnity
      ((S1715SixPrimitiveRoot ^ (k : Nat)).property))
  have hroot : ((S1715SixPrimitiveRoot : S1715SixTorsionCarrier) :
      (AlgebraicClosure S1687Field)ˣ) =
      S1715SixPrimitiveRootUnit := by
    apply Units.ext
    simp [S1715SixPrimitiveRoot, S1715SixPrimitiveRootUnit,
      IsPrimitiveRoot.toRootsOfUnity]
  have hpower : S1715SixPrimitiveRootUnit ^
      (Classical.choose
        (S1715SixPrimitiveRootUnit_isPrimitive.eq_pow_of_mem_rootsOfUnity
          ((S1715SixPrimitiveRoot ^ (k : Nat)).property))) =
      S1715SixPrimitiveRootUnit ^ (k : Nat) := by
    simpa [hroot] using hspec.2
  have hi := S1715SixPrimitiveRootUnit_isPrimitive.pow_inj
    hspec.1 k.isLt hpower
  exact hi

/-! ## 3. The actual absolute Galois group and mod-l representation -/

/-- The literal absolute Galois group of the actual base field. -/
abbrev S1715AbsoluteGalois : Type :=
  AlgebraicClosure S1687Field ≃ₐ[S1687Field] AlgebraicClosure S1687Field

instance S1715AbsoluteGaloisGroup : Group S1715AbsoluteGalois :=
  inferInstance

/-- The actual mod-l general-linear representation of Gal(Fbar/F) on E[l],
constructed without any basis hypothesis. -/
noncomputable abbrev S1715GeneralLinearRepresentation (l : PrimeGeFive) :
    S1715AbsoluteGalois →*
      LinearMap.GeneralLinearGroup (ZMod l.value)
        (S1715Curve.LTorsion l) :=
  S1715Curve.galoisActionOnLTorsionGeneralLinearRepresentation l

/-- The actual representation group: the range of the mod-l
representation. -/
abbrev S1715RepresentationGroup (l : PrimeGeFive) : Type :=
  (S1715GeneralLinearRepresentation l).range

instance S1715RepresentationGroupGroup (l : PrimeGeFive) :
    Group (S1715RepresentationGroup l) :=
  inferInstance

/-- The actual surjection onto the representation range. -/
noncomputable abbrev S1715Representation (l : PrimeGeFive) :
    S1715AbsoluteGalois →* S1715RepresentationGroup l :=
  (S1715GeneralLinearRepresentation l).rangeRestrict

/-- The representation is surjective onto its range by construction. -/
theorem S1715Representation_surjective (l : PrimeGeFive) :
    Function.Surjective (S1715Representation l) :=
  (S1715GeneralLinearRepresentation l).rangeRestrict_surjective

/-! ## 4. The literal SL_2 image source input and its exact content -/

/-- The exact rank-two torsion basis type: a ZMod l-linear equivalence
from (Fin 2 -> ZMod l) to the actual E[l]. -/
abbrev S1715TorsionBasis (l : PrimeGeFive) : Type :=
  (Fin 2 → ZMod l.value) ≃ₗ[ZMod l.value] (S1715Curve.LTorsion l)

/-- The literal SL_2(F_l) containment for the matrix representation attached
to a chosen rank-two basis.  This is the second D5 field, with its first
component (the basis) exposed separately below. -/
def S1715ImageTail (l : PrimeGeFive) (b : S1715TorsionBasis l) : Prop :=
  Subgroup.map Matrix.SpecialLinearGroup.toGL
    (⊤ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) (ZMod l.value))) ≤
    (S1715Curve.galoisLTorsionMatrixRepresentation l b).range

/-- The explicit source input S1715ImageContainsSL2: there exists a
rank-two basis for which the literal SL_2(F_l) containment holds.  This is
not proved and no inhabitant is asserted. -/
def S1715ImageContainsSL2 (l : PrimeGeFive) : Prop :=
  ∃ b : S1715TorsionBasis l, S1715ImageTail l b

/-- The matrix representation is literally the actual general-linear
representation transported along the chosen basis.  Thus the image statement
is about the same actual mod-l representation, not a second unrelated
one. -/
theorem S1715MatrixRepresentation_eq_transport (l : PrimeGeFive)
    (b : S1715TorsionBasis l) :
    S1715Curve.galoisLTorsionMatrixRepresentation l b =
      Matrix.GeneralLinearGroup.toLin.symm.toMonoidHom.comp
        ((LinearMap.GeneralLinearGroup.congrLinearEquiv b).symm.toMonoidHom.comp
          (S1715GeneralLinearRepresentation l)) := rfl

/-- The containment is the same in the every-SL_2-element-is-hit shape. -/
theorem S1715ImageTail_iff_forall (l : PrimeGeFive)
    (b : S1715TorsionBasis l) :
    S1715ImageTail l b ↔
      LargeImageContainsSL2
        (S1715Curve.galoisLTorsionMatrixRepresentation l b) :=
  largeImageSL2_iff_forall _

/-- Unfolded form of the source input. -/
theorem S1715ImageContainsSL2_iff_exists_tail (l : PrimeGeFive) :
    S1715ImageContainsSL2 l ↔
      ∃ b : S1715TorsionBasis l, S1715ImageTail l b :=
  Iff.rfl

/-- The source input is literally the frozen Serre-style large-image
statement for the actual curve. -/
theorem S1715ImageContainsSL2_iff_serre (l : PrimeGeFive) :
    S1715ImageContainsSL2 l ↔
      SerreStyleLargeImageStatement S1715Curve l :=
  Iff.rfl

/-- The exact rank-two basis gap, in the frozen D5 vocabulary. -/
def S1715RankTwoBasisGap (l : PrimeGeFive) : Prop :=
  Nonempty (S1715TorsionBasis l)

theorem S1715RankTwoBasisGap_iff (l : PrimeGeFive) :
    S1715RankTwoBasisGap l ↔
      RankTwoTorsionBasisGap S1715Curve l :=
  Iff.rfl

/-- The image input supplies the rank-two basis: it is the first missing
component. -/
theorem S1715ImageContainsSL2_basis (l : PrimeGeFive)
    (h : S1715ImageContainsSL2 l) : S1715RankTwoBasisGap l :=
  ⟨h.choose⟩

/-- The exact first missing object of the faithful clause.  It is the literal
SL_2 containment; its first component is the rank-two basis, and after
that the remaining content is the Serre large-image statement for the actual
curve. -/
def S1715FirstMissing (l : PrimeGeFive) : Prop :=
  S1715ImageContainsSL2 l

theorem S1715FirstMissing_iff (l : PrimeGeFive) :
    S1715FirstMissing l ↔ S1715ImageContainsSL2 l :=
  Iff.rfl

/-- The first missing object decomposes as basis plus tail. -/
theorem S1715FirstMissing_decomposition (l : PrimeGeFive) :
    S1715FirstMissing l ↔
      ∃ b : S1715TorsionBasis l, S1715ImageTail l b :=
  Iff.rfl

/-- A witness of the rank-two basis together with the tail for that basis
supplies the source input.  This is the exact shape of the remaining
obligation; no witness is produced here. -/
theorem S1715ImageContainsSL2_of_basis_and_tail (l : PrimeGeFive)
    (hb : S1715RankTwoBasisGap l) (ht : S1715ImageTail l hb.some) :
    S1715ImageContainsSL2 l :=
  ⟨hb.some, ht⟩

/-! ## 5. The actual 2 * 3-torsion content from S1708 -/

/-- The paper's condition (b) for the actual curve: all 2 * 3-torsion
points are rational over the actual base field. -/
def S1715SixTorsionIndependent : Prop :=
  PuncturedEllipticCurve.Torsion23Rational S1715Curve

/-- The S1708 content: Torsion23Rational of the actual base-changed curve
is a theorem, not an input. -/
theorem S1715SixTorsionIndependent_proved :
    S1715SixTorsionIndependent :=
  S1708Torsion23Rational

/-- The clause's field is definitionally the S1708 statement. -/
theorem S1715SixTorsionIndependent_eq_S1708 :
    S1715SixTorsionIndependent =
      PuncturedEllipticCurve.Torsion23Rational S1715Curve :=
  rfl

/-! ## 6. The actual l-compatibility at the place above 5 -/

/-- The actual bad residue characteristic: the residue characteristic of the
place above 5 in the actual field. -/
def S1715BadResidueCharacteristic : Nat :=
  NumberFieldFinitePlace.residueCharacteristic S1687PlaceAboveFive

/-- It is 5, by the S1712 computation and residueCharacteristic_comap. -/
theorem S1715BadResidueCharacteristic_eq_five :
    S1715BadResidueCharacteristic = 5 := by
  unfold S1715BadResidueCharacteristic
  have h := NumberFieldFinitePlace.residueCharacteristic_comap
    (k := ℚ) (K := S1687Field) S1687PlaceAboveFive
  rw [S1687PlaceAboveFive_comap] at h
  rw [← h, S1712ConcreteFivePlace_residueCharacteristic]

/-- The residue-characteristic half of Definition 3.1(c) at the actual bad
place: l is prime to the actual residue characteristic. -/
def S1715LTorsionCompatible (l : PrimeGeFive) : Prop :=
  Nat.Coprime l.value S1715BadResidueCharacteristic

/-- Since the actual place has residue characteristic 5, the condition is
exactly l != 5; this is the S1637 criterion at the actual S1714 place. -/
theorem S1715LTorsionCompatible_iff (l : PrimeGeFive) :
    S1715LTorsionCompatible l ↔ l.value ≠ 5 := by
  unfold S1715LTorsionCompatible
  rw [S1715BadResidueCharacteristic_eq_five]
  exact Nat.coprime_primes l.prime Nat.prime_five

/-- The actual proof for every l != 5. -/
theorem S1715LTorsionCompatible_of_ne_five (l : PrimeGeFive)
    (h5 : l.value ≠ 5) : S1715LTorsionCompatible l :=
  (S1715LTorsionCompatible_iff l).mpr h5

/-- The actual S1714 place condition and the S1637 Gaussian-place condition
are the same l != 5 criterion, so the S1637 iff transfers verbatim. -/
theorem S1715LTorsionCompatible_iff_s1637 (l : PrimeGeFive) :
    S1715LTorsionCompatible l ↔
      LeanFormal.IUT.XiFPaper.S1637D5TorsionClauseActual.S1637LTorsionCompatible l := by
  rw [S1715LTorsionCompatible_iff,
    LeanFormal.IUT.XiFPaper.S1637D5TorsionClauseActual.s1637LTorsionCompatible_iff]

/-- The concrete l = 5 label. -/
def S1715Five : PrimeGeFive where
  value := 5
  prime := Nat.prime_five
  ge_five := le_rfl

@[simp] theorem S1715Five_value : S1715Five.value = 5 := rfl

/-- At l = 5 the actual condition is false. -/
theorem S1715LTorsionCompatible_five_false :
    ¬ S1715LTorsionCompatible S1715Five := by
  intro h
  exact (S1715LTorsionCompatible_iff S1715Five).mp h S1715Five_value

/-! ## 7. The conditional actual clause -/

/-- The actual D5 clause, conditional on the explicit source input
S1715ImageContainsSL2 l and the actual residue-characteristic condition
l != 5.  The carrier, label, absolute Galois group, mod-l representation,
surjection, six-torsion rationality, and l-compatibility are the actual
objects constructed above.  No image or SL_2 content is assumed beyond
hI. -/
noncomputable def S1715SourceTorsionClause (l : PrimeGeFive)
    (hI : S1715ImageContainsSL2 l) (h5 : l.value ≠ 5) :
    SourceTorsionClause.{0, 0, 0} l where
  torsionCarrier := S1715SixTorsionCarrier
  torsionCarrierLaw := inferInstance
  torsionLabel := S1715SixTorsionLabel
  torsionNonempty := ⟨1⟩
  representationCarrier := S1715AbsoluteGalois
  representationCarrierLaw := inferInstance
  representationGroup := S1715RepresentationGroup l
  representationGroupLaw := inferInstance
  representation := S1715Representation l
  representation_surjective := S1715Representation_surjective l
  imageContainsSL2 := S1715ImageContainsSL2 l
  imageContainsSL2_proved := hI
  sixTorsionIndependent := S1715SixTorsionIndependent
  sixTorsionIndependent_proved := S1715SixTorsionIndependent_proved
  lTorsionCompatible := S1715LTorsionCompatible l
  lTorsionCompatible_proved := S1715LTorsionCompatible_of_ne_five l h5

@[simp] theorem S1715SourceTorsionClause_torsionCarrier (l : PrimeGeFive)
    (hI : S1715ImageContainsSL2 l) (h5 : l.value ≠ 5) :
    (S1715SourceTorsionClause l hI h5).torsionCarrier =
      S1715SixTorsionCarrier := rfl

@[simp] theorem S1715SourceTorsionClause_torsionLabel (l : PrimeGeFive)
    (hI : S1715ImageContainsSL2 l) (h5 : l.value ≠ 5) :
    (S1715SourceTorsionClause l hI h5).torsionLabel =
      S1715SixTorsionLabel := rfl

@[simp] theorem S1715SourceTorsionClause_representationCarrier
    (l : PrimeGeFive) (hI : S1715ImageContainsSL2 l) (h5 : l.value ≠ 5) :
    (S1715SourceTorsionClause l hI h5).representationCarrier =
      S1715AbsoluteGalois := rfl

@[simp] theorem S1715SourceTorsionClause_representationGroup
    (l : PrimeGeFive) (hI : S1715ImageContainsSL2 l) (h5 : l.value ≠ 5) :
    (S1715SourceTorsionClause l hI h5).representationGroup =
      S1715RepresentationGroup l := rfl

@[simp] theorem S1715SourceTorsionClause_representation (l : PrimeGeFive)
    (hI : S1715ImageContainsSL2 l) (h5 : l.value ≠ 5) :
    (S1715SourceTorsionClause l hI h5).representation =
      S1715Representation l := rfl

@[simp] theorem S1715SourceTorsionClause_imageContainsSL2 (l : PrimeGeFive)
    (hI : S1715ImageContainsSL2 l) (h5 : l.value ≠ 5) :
    (S1715SourceTorsionClause l hI h5).imageContainsSL2 =
      S1715ImageContainsSL2 l := rfl

@[simp] theorem S1715SourceTorsionClause_sixTorsionIndependent
    (l : PrimeGeFive) (hI : S1715ImageContainsSL2 l) (h5 : l.value ≠ 5) :
    (S1715SourceTorsionClause l hI h5).sixTorsionIndependent =
      PuncturedEllipticCurve.Torsion23Rational S1715Curve := rfl

@[simp] theorem S1715SourceTorsionClause_lTorsionCompatible
    (l : PrimeGeFive) (hI : S1715ImageContainsSL2 l) (h5 : l.value ≠ 5) :
    (S1715SourceTorsionClause l hI h5).lTorsionCompatible =
      S1715LTorsionCompatible l := rfl

/-- The clause's label is the actual primitive-root label, hence surjective. -/
theorem S1715SourceTorsionClause_label_surjective (l : PrimeGeFive)
    (hI : S1715ImageContainsSL2 l) (h5 : l.value ≠ 5) :
    Function.Surjective (S1715SourceTorsionClause l hI h5).torsionLabel := by
  simpa using S1715SixTorsionLabel_surjective

/-- The clause's representation is the actual mod-l representation, hence
surjective onto its range. -/
theorem S1715SourceTorsionClause_representation_surjective
    (l : PrimeGeFive) (hI : S1715ImageContainsSL2 l) (h5 : l.value ≠ 5) :
    Function.Surjective (S1715SourceTorsionClause l hI h5).representation :=
  (S1715SourceTorsionClause l hI h5).representation_surjective

/-- The three source clause fields of the constructed clause. -/
theorem S1715SourceTorsionClause_fields (l : PrimeGeFive)
    (hI : S1715ImageContainsSL2 l) (h5 : l.value ≠ 5) :
    (S1715SourceTorsionClause l hI h5).imageContainsSL2 ∧
      (S1715SourceTorsionClause l hI h5).sixTorsionIndependent ∧
      (S1715SourceTorsionClause l hI h5).lTorsionCompatible :=
  ⟨hI, S1715SixTorsionIndependent_proved,
    S1715LTorsionCompatible_of_ne_five l h5⟩

/-- The clause's six-torsion proof is literally the S1708 theorem. -/
theorem S1715SourceTorsionClause_sixTorsion_proof_eq (l : PrimeGeFive)
    (hI : S1715ImageContainsSL2 l) (h5 : l.value ≠ 5) :
    (S1715SourceTorsionClause l hI h5).sixTorsionIndependent_proved =
      S1708Torsion23Rational := rfl

/-- The exact input shape of the conditional clause: the image source input
together with the actual l != 5 condition. -/
def S1715D5ConstructionInput (l : PrimeGeFive) : Prop :=
  S1715ImageContainsSL2 l ∧ l.value ≠ 5

theorem S1715D5ConstructionInput_iff (l : PrimeGeFive) :
    S1715D5ConstructionInput l ↔
      S1715ImageContainsSL2 l ∧ l.value ≠ 5 :=
  Iff.rfl

/-- Conditional existence of the actual D5 clause from the exact input. -/
theorem S1715SourceTorsionClause_nonempty_of_input (l : PrimeGeFive)
    (h : S1715D5ConstructionInput l) :
    Nonempty (SourceTorsionClause.{0, 0, 0} l) :=
  ⟨S1715SourceTorsionClause l h.1 h.2⟩

/-- The clause as a function of the exact packaged input. -/
noncomputable def S1715SourceTorsionClauseOfInput (l : PrimeGeFive)
    (h : S1715D5ConstructionInput l) :
    SourceTorsionClause.{0, 0, 0} l :=
  S1715SourceTorsionClause l h.1 h.2

@[simp] theorem S1715SourceTorsionClauseOfInput_imageContainsSL2
    (l : PrimeGeFive) (h : S1715D5ConstructionInput l) :
    (S1715SourceTorsionClauseOfInput l h).imageContainsSL2 =
      S1715ImageContainsSL2 l := rfl

/-- The clause exists at every l != 5 for which the explicit image source
input is supplied. -/
theorem S1715D5_exists_of_image (l : PrimeGeFive) (h5 : l.value ≠ 5)
    (hI : S1715ImageContainsSL2 l) :
    ∃ T : SourceTorsionClause.{0, 0, 0} l,
      T.imageContainsSL2 = S1715ImageContainsSL2 l ∧
        T.sixTorsionIndependent =
          PuncturedEllipticCurve.Torsion23Rational S1715Curve ∧
        T.lTorsionCompatible = S1715LTorsionCompatible l :=
  ⟨S1715SourceTorsionClause l hI h5, rfl, rfl, rfl⟩

/-! ## 8. The D5 slot of SourceDefinition31Data -/

/-- At the universe instance u = 0, filling the torsion (D5) slot of a
source contract with the actual clause.  This is the literal consumer of the
construction: the torsion field of SourceDefinition31Data has exactly the
type built here. -/
noncomputable def S1715FillD5 (l : PrimeGeFive)
    (S : SourceDefinition31Data.{0} l)
    (hI : S1715ImageContainsSL2 l) (h5 : l.value ≠ 5) :
    SourceDefinition31Data.{0} l :=
  { S with torsion := S1715SourceTorsionClause l hI h5 }

/-- The D5 slot of the filled contract is the actual clause. -/
@[simp] theorem S1715FillD5_torsion (l : PrimeGeFive)
    (S : SourceDefinition31Data.{0} l)
    (hI : S1715ImageContainsSL2 l) (h5 : l.value ≠ 5) :
    (S1715FillD5 l S hI h5).torsion =
      S1715SourceTorsionClause l hI h5 := rfl

/-! ## 9. The obstruction at l = 5 -/

/-- No clause whose lTorsionCompatible field is the actual
residue-characteristic condition can exist at l = 5, because that actual
condition is false there.  The statement is deliberately restricted to the
faithful condition; it does not claim that the bare structure type is empty
for an unfaithful choice of the field. -/
theorem S1715NoActualClauseAtFive :
    ¬ ∃ T : SourceTorsionClause.{0, 0, 0} S1715Five,
        T.lTorsionCompatible = S1715LTorsionCompatible S1715Five := by
  rintro ⟨T, hT⟩
  have h : S1715LTorsionCompatible S1715Five :=
    hT ▸ T.lTorsionCompatible_proved
  exact S1715LTorsionCompatible_five_false h

/-! ## 10. Axiom footprint -/

#print axioms S1715SixTorsionCarrierFinite
#print axioms S1715SixTorsionCarrier_card
#print axioms S1715SixTorsionLabel_surjective
#print axioms S1715Representation_surjective
#print axioms S1715ImageContainsSL2_iff_serre
#print axioms S1715ImageContainsSL2_basis
#print axioms S1715SixTorsionIndependent_proved
#print axioms S1715BadResidueCharacteristic_eq_five
#print axioms S1715LTorsionCompatible_iff
#print axioms S1715LTorsionCompatible_iff_s1637
#print axioms S1715LTorsionCompatible_five_false
#print axioms S1715SourceTorsionClause
#print axioms S1715SourceTorsionClauseOfInput
#print axioms S1715SourceTorsionClause_fields
#print axioms S1715SourceTorsionClause_sixTorsion_proof_eq
#print axioms S1715FillD5
#print axioms S1715NoActualClauseAtFive

end LeanFormal.IUT.XiFPaper.S1715SourceTorsionClauseActual
