import tmp.sheaf.xif.paper.S1280SourceDefinition31Actual
import LeanFormal.IUT.IUTI.InitialTheta.SourceTorsionCarrierReduction
import LeanFormal.IUT.IUTII.Frobenioid.Example36TateModuleProfinite
import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed

/-!
# S1298: the actual D5 torsion field from the concrete Gaussian data

S1280SourceDefinition31Actual constructs the actual D3 and D4 fields of
Definition 3.1 over the concrete Gaussian arithmetic input
concreteGaussianInitialThetaArithmeticData l.  Its first missing field is

  torsion : SourceTorsionClause l.

This file does not fabricate that clause.  It records the exact mathematical
field that is missing and constructs every clause field that the actual
concrete curve, its actual l-torsion, and its actual absolute-Galois
representation do determine.

Main points:

* The source-faithful D5 datum SourceTorsionDatum l A has first field
  torsion_basis : (Fin 2 -> ZMod l) = E_F[l].  This is the exact rank-two
  torsion basis.  It is equivalent to RankTwoTorsionBasisGap, to
  finrank = 2 under finiteness, and to the numerical cardinality
  card E[l] = l^2.  No inhabitant is asserted; the tree has no rank-two
  theorem for the concrete split curve at any level l >= 5.
* SourceTorsionDatum is equivalent to a sigma type whose first component is
  exactly this basis; the other two components are the literal SL2 image
  containment and the kernel-field identification.  This is the exact
  first-field decomposition of D5.
* The abstract SourceTorsionClause has seven actual fields that can be built
  from the concrete data: the six-roots-of-unity carrier, its primitive-root
  Fin 6 label, the absolute Galois group, the actual general-linear
  representation on E[l], its range, and the range-restricted surjection.
  The first genuinely missing field is then
  imageContainsSL2_proved : SerreStyleLargeImageStatement E l.
  That statement itself begins with the rank-two basis.  We therefore give
  an actual clause constructor from an explicit large-image statement and
  two source conditions, and no unconditional SourceTorsionClause.
* The only unconditional odd-level rank-two basis in the tree is for the
  different curve y^2 = x^3 - x at l = 3.  PrimeGeFive excludes l = 3, and
  the concrete Gaussian curve is y^2 + xy = x^3 + 5, so that donor cannot
  fill this field without a new transport theorem.

No PUnit, True, constant label, arbitrary basis, or extra axiom is used.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 1000000

noncomputable section

namespace LeanFormal.IUT.XiFPaper.S1298TorsionClauseActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.TorsionCarrierReduction
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.XiFPaper.S1280SourceDefinition31Actual

local instance s1298GaussianIrreducible :
    Fact (Irreducible (Polynomial.X ^ 2 - Polynomial.C (-1) : Polynomial ℚ)) :=
  ⟨gaussianPolynomial_irreducible⟩

local instance s1298FivePrime : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩

/-! ## 1. The exact first field of the D5 datum -/

/-- The actual l-torsion carrier of the concrete Gaussian curve. -/
abbrev S1298TorsionCarrier (l : PrimeGeFive) : Type :=
  (S1280Arithmetic l).curve.LTorsion l

/-- The exact first field of SourceTorsionDatum l (S1280Arithmetic l): a
rank-two ZMod l-basis of the actual l-torsion.  This is a type, not an
inhabitant assertion. -/
abbrev S1298TorsionBasisType (l : PrimeGeFive) : Type :=
  (Fin 2 → ZMod l.value) ≃ₗ[ZMod l.value] S1298TorsionCarrier l

/-- The D5 datum over the actual S1280 arithmetic input. -/
abbrev S1298D5Datum (l : PrimeGeFive) : Type :=
  SourceTorsionDatum l (S1280Arithmetic l)

/-- The exact basis field is literally the frozen rank-two gap. -/
theorem s1298TorsionBasisType_iff_rankTwoGap (l : PrimeGeFive) :
    Nonempty (S1298TorsionBasisType l) ↔
      RankTwoTorsionBasisGap (S1280Arithmetic l).curve l :=
  Iff.rfl

/-- The exact basis field is a finite-dimensional rank-two statement, once
finiteness of the torsion carrier is supplied.  Finiteness is a separate
missing hypothesis, not a consequence of the other fields. -/
theorem s1298TorsionBasisType_iff_finrank_eq_two (l : PrimeGeFive)
    [Module.Finite (ZMod l.value) (S1298TorsionCarrier l)] :
    Nonempty (S1298TorsionBasisType l) ↔
      Module.finrank (ZMod l.value) (S1298TorsionCarrier l) = 2 := by
  rw [s1298TorsionBasisType_iff_rankTwoGap]
  exact rankTwoTorsionBasisGap_iff_finrank_eq_two (S1280Arithmetic l).curve l

/-- The exact numerical form of the first field: finiteness together with
card E[l] = l^2.  The finiteness half is essential because Nat.card of an
infinite type is the junk value 0. -/
def S1298TorsionCardinalityCard (l : PrimeGeFive) : Prop :=
  Finite (S1298TorsionCarrier l) ∧ Nat.card (S1298TorsionCarrier l) = l.value ^ 2

/-- The numerical form implies the rank-two basis, through the existing
ZMod-l cardinality engine. -/
theorem s1298TorsionBasisType_of_cardinalityCard (l : PrimeGeFive)
    (h : S1298TorsionCardinalityCard l) :
    Nonempty (S1298TorsionBasisType l) := by
  haveI : Finite (S1298TorsionCarrier l) := h.1
  haveI : Fact (Nat.Prime l.value) := l.factPrime
  haveI : Module.Finite (ZMod l.value) (S1298TorsionCarrier l) :=
    Module.Finite.of_finite
  have hfr : Module.finrank (ZMod l.value) (S1298TorsionCarrier l) = 2 :=
    LeanFormal.IUT.IUTII.Frobenioid.Example36.TateModuleProfinite.zmod_finrank_eq_two_of_natCard_eq_sq
      (S1298TorsionCarrier l) h.2
  exact rankTwoBasis_of_finrank_eq_two (S1280Arithmetic l).curve l hfr

/-- Conversely, a rank-two basis forces the numerical cardinality. -/
theorem s1298TorsionCardinalityCard_of_basis (l : PrimeGeFive)
    (b : S1298TorsionBasisType l) : S1298TorsionCardinalityCard l := by
  haveI : Fact (Nat.Prime l.value) := l.factPrime
  constructor
  · exact Finite.of_equiv _ b.toEquiv
  · calc Nat.card (S1298TorsionCarrier l)
        = Nat.card (Fin 2 → ZMod l.value) := Nat.card_congr b.toEquiv.symm
      _ = l.value ^ 2 := by simp

/-- Exact equivalence: the first field is the numerical cardinality card. -/
theorem s1298TorsionBasisType_nonempty_iff_cardinalityCard (l : PrimeGeFive) :
    Nonempty (S1298TorsionBasisType l) ↔ S1298TorsionCardinalityCard l := by
  constructor
  · rintro ⟨b⟩
    exact s1298TorsionCardinalityCard_of_basis l b
  · exact s1298TorsionBasisType_of_cardinalityCard l

/-! ## 2. The exact first-field decomposition of SourceTorsionDatum -/

/-- The two fields of SourceTorsionDatum after the first: the literal SL2
image containment for the matrix representation attached to the chosen
basis, and the identification of the source field K with the kernel field. -/
structure S1298D5Tail (l : PrimeGeFive) (b : S1298TorsionBasisType l) where
  image_contains_SL2 :
    Subgroup.map Matrix.SpecialLinearGroup.toGL
      (⊤ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) (ZMod l.value))) ≤
      ((S1280Arithmetic l).curve.galoisLTorsionMatrixRepresentation l b).range
  kernel_field_identification :
    (S1280Arithmetic l).K ≃ₐ[(S1280Arithmetic l).F]
      (S1280Arithmetic l).curve.galoisLTorsionKernelField l b

/-- Assemble the D5 datum from the exact first field and the tail. -/
noncomputable def s1298D5DatumOfBasisAndTail (l : PrimeGeFive)
    (b : S1298TorsionBasisType l) (t : S1298D5Tail l b) :
    S1298D5Datum l where
  torsion_basis := b
  image_contains_SL2 := t.image_contains_SL2
  kernel_field_identification := t.kernel_field_identification

/-- The first field of a D5 datum. -/
noncomputable def s1298D5Basis (l : PrimeGeFive) (D : S1298D5Datum l) :
    S1298TorsionBasisType l :=
  D.torsion_basis

/-- The tail of a D5 datum. -/
noncomputable def s1298D5TailOfDatum (l : PrimeGeFive) (D : S1298D5Datum l) :
    S1298D5Tail l (s1298D5Basis l D) where
  image_contains_SL2 := D.image_contains_SL2
  kernel_field_identification := D.kernel_field_identification

@[simp] theorem s1298D5DatumOfBasisAndTail_basis (l : PrimeGeFive)
    (b : S1298TorsionBasisType l) (t : S1298D5Tail l b) :
    s1298D5Basis l (s1298D5DatumOfBasisAndTail l b t) = b :=
  rfl

@[simp] theorem s1298D5DatumOfBasisAndTail_tail (l : PrimeGeFive)
    (b : S1298TorsionBasisType l) (t : S1298D5Tail l b) :
    s1298D5TailOfDatum l (s1298D5DatumOfBasisAndTail l b t) = t :=
  rfl

/-- Exact decomposition: a D5 datum is a basis together with the two tail
fields.  This is the formal meaning of "the first field is the basis". -/
noncomputable def s1298D5DatumEquiv (l : PrimeGeFive) :
    S1298D5Datum l ≃ Σ b : S1298TorsionBasisType l, S1298D5Tail l b where
  toFun D := ⟨D.torsion_basis,
    ⟨D.image_contains_SL2, D.kernel_field_identification⟩⟩
  invFun p := s1298D5DatumOfBasisAndTail l p.1 p.2
  left_inv D := by cases D; rfl
  right_inv p := by rcases p with ⟨b, t⟩; cases t; rfl

/-- The first field of D5 is literally the first component of the exact
decomposition. -/
theorem s1298D5Datum_firstField (l : PrimeGeFive) (D : S1298D5Datum l) :
    D.torsion_basis = (s1298D5DatumEquiv l D).1 :=
  rfl

/-- Nonempty D5 datum is exactly a basis with a nonempty tail. -/
theorem s1298D5Datum_nonempty_iff (l : PrimeGeFive) :
    Nonempty (S1298D5Datum l) ↔
      ∃ b : S1298TorsionBasisType l, Nonempty (S1298D5Tail l b) := by
  constructor
  · rintro ⟨D⟩
    exact ⟨D.torsion_basis,
      ⟨⟨D.image_contains_SL2, D.kernel_field_identification⟩⟩⟩
  · rintro ⟨b, ⟨t⟩⟩
    exact ⟨s1298D5DatumOfBasisAndTail l b t⟩

/-! ## 3. The actual SourceTorsionClause prefix -/

/-- The actual six-roots-of-unity carrier in the algebraic closure of the
source base field.  This is the corrected carrier for the Fin 6 label; it is
not the l^2-element l-torsion group. -/
abbrev S1298SixTorsionCarrier (l : PrimeGeFive) : Type :=
  rootsOfUnity 6 (AlgebraicClosure (S1280Arithmetic l).F)

instance s1298SixTorsionCarrierGroup (l : PrimeGeFive) :
    Group (S1298SixTorsionCarrier l) :=
  inferInstance

/-- A chosen primitive sixth root in the algebraic closure. -/
noncomputable def s1298SixPrimitiveRootUnit (l : PrimeGeFive) :
    (AlgebraicClosure (S1280Arithmetic l).F)ˣ :=
  (Classical.choose_spec
    (HasEnoughRootsOfUnity.exists_primitiveRoot
      (AlgebraicClosure (S1280Arithmetic l).F) 6)).isUnit
    (by norm_num : 6 ≠ 0) |>.unit

/-- The chosen primitive root as an element of the six-roots carrier. -/
noncomputable def s1298SixPrimitiveRoot (l : PrimeGeFive) :
    S1298SixTorsionCarrier l :=
  (Classical.choose_spec
    (HasEnoughRootsOfUnity.exists_primitiveRoot
      (AlgebraicClosure (S1280Arithmetic l).F) 6)).toRootsOfUnity

/-- The chosen root is primitive of order six. -/
theorem s1298SixPrimitiveRootUnit_isPrimitive (l : PrimeGeFive) :
    IsPrimitiveRoot (s1298SixPrimitiveRootUnit l) 6 := by
  unfold s1298SixPrimitiveRootUnit
  exact IsPrimitiveRoot.isUnit_unit (by norm_num : 6 ≠ 0)
    (Classical.choose_spec
      (HasEnoughRootsOfUnity.exists_primitiveRoot
        (AlgebraicClosure (S1280Arithmetic l).F) 6))

/-- The actual six-slot label: the exponent of the chosen primitive root. -/
noncomputable def s1298SixTorsionLabel (l : PrimeGeFive)
    (x : S1298SixTorsionCarrier l) : Fin 6 :=
  let hx : (x : (AlgebraicClosure (S1280Arithmetic l).F)ˣ) ∈
      rootsOfUnity 6 (AlgebraicClosure (S1280Arithmetic l).F) := x.property
  let e := Classical.choose
    (s1298SixPrimitiveRootUnit_isPrimitive l |>.eq_pow_of_mem_rootsOfUnity hx)
  ⟨e, (Classical.choose_spec
    (s1298SixPrimitiveRootUnit_isPrimitive l |>.eq_pow_of_mem_rootsOfUnity hx)).1⟩

/-- The actual label is surjective onto the six slots. -/
theorem s1298SixTorsionLabel_surjective (l : PrimeGeFive) :
    Function.Surjective (s1298SixTorsionLabel l) := by
  intro k
  refine ⟨s1298SixPrimitiveRoot l ^ (k : Nat), ?_⟩
  apply Fin.ext
  change (Classical.choose
    (s1298SixPrimitiveRootUnit_isPrimitive l |>.eq_pow_of_mem_rootsOfUnity
      ((s1298SixPrimitiveRoot l ^ (k : Nat)).property)) : Nat) = k
  have hspec := Classical.choose_spec
    (s1298SixPrimitiveRootUnit_isPrimitive l |>.eq_pow_of_mem_rootsOfUnity
      ((s1298SixPrimitiveRoot l ^ (k : Nat)).property))
  have hroot : ((s1298SixPrimitiveRoot l : S1298SixTorsionCarrier l) :
      (AlgebraicClosure (S1280Arithmetic l).F)ˣ) =
      s1298SixPrimitiveRootUnit l := by
    apply Units.ext
    simp [s1298SixPrimitiveRoot, s1298SixPrimitiveRootUnit,
      IsPrimitiveRoot.toRootsOfUnity]
  have hpower : (s1298SixPrimitiveRootUnit l) ^
      (Classical.choose
        (s1298SixPrimitiveRootUnit_isPrimitive l |>.eq_pow_of_mem_rootsOfUnity
          ((s1298SixPrimitiveRoot l ^ (k : Nat)).property))) =
      (s1298SixPrimitiveRootUnit l) ^ (k : Nat) := by
    simpa [hroot] using hspec.2
  have hi := (s1298SixPrimitiveRootUnit_isPrimitive l).pow_inj
    hspec.1 k.isLt hpower
  exact hi

/-- The actual general-linear Galois representation on the concrete curve's
ZMod l-torsion, constructed without any basis hypothesis. -/
noncomputable abbrev S1298GeneralLinearRepresentation (l : PrimeGeFive) :
    SourceAbsoluteGalois (S1280Arithmetic l) →*
      LinearMap.GeneralLinearGroup (ZMod l.value)
        ((S1280Arithmetic l).curve.LTorsion l) :=
  (S1280Arithmetic l).curve.galoisActionOnLTorsionGeneralLinearRepresentation l

/-- The actual group is the range of the general-linear representation. -/
abbrev S1298RepresentationGroup (l : PrimeGeFive) : Type :=
  (S1298GeneralLinearRepresentation l).range

/-- The actual surjective representation onto its range. -/
noncomputable abbrev S1298Representation (l : PrimeGeFive) :
    SourceAbsoluteGalois (S1280Arithmetic l) →*
      S1298RepresentationGroup l :=
  (S1298GeneralLinearRepresentation l).rangeRestrict

/-- The exact first missing field of the clause, after the actual carrier,
label, and general-linear representation are constructed.  Its first
component is the rank-two basis. -/
def S1298LargeImageField (l : PrimeGeFive) : Prop :=
  SerreStyleLargeImageStatement (S1280Arithmetic l).curve l

/-- The large-image statement, unfolded: its first field is literally the
rank-two basis. -/
theorem s1298LargeImageField_iff_exists_basis (l : PrimeGeFive) :
    S1298LargeImageField l ↔
      ∃ b : S1298TorsionBasisType l,
        Subgroup.map Matrix.SpecialLinearGroup.toGL
          (⊤ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) (ZMod l.value))) ≤
          ((S1280Arithmetic l).curve.galoisLTorsionMatrixRepresentation l b).range :=
  Iff.rfl

/-- The large-image statement begins with the rank-two basis: every witness
has a basis as its first component. -/
theorem s1298LargeImageField_firstField (l : PrimeGeFive)
    (h : S1298LargeImageField l) : Nonempty (S1298TorsionBasisType l) :=
  ⟨h.choose⟩

/-- The remaining source-side fields of the clause: the large-image proof and
the two supplied source conditions. -/
structure S1298TorsionSourceGap (l : PrimeGeFive) where
  imageContainsSL2_proved : S1298LargeImageField l
  sixTorsionIndependent : Prop
  sixTorsionIndependent_proved : sixTorsionIndependent
  lTorsionCompatible : Prop
  lTorsionCompatible_proved : lTorsionCompatible

/-- Actual clause constructor: fields 1-7 are the concrete six-roots carrier,
its primitive-root label, the actual absolute Galois group, the actual
general-linear representation, its range, and the range-restricted
surjection.  The remaining fields are exactly the gap. -/
noncomputable def s1298SourceTorsionClauseOfGap (l : PrimeGeFive)
    (G : S1298TorsionSourceGap l) : SourceTorsionClause.{0, 0, 0} l where
  torsionCarrier := S1298SixTorsionCarrier l
  torsionCarrierLaw := inferInstance
  torsionLabel := s1298SixTorsionLabel l
  torsionNonempty := ⟨1⟩
  representationCarrier := SourceAbsoluteGalois (S1280Arithmetic l)
  representationCarrierLaw := inferInstance
  representationGroup := S1298RepresentationGroup l
  representationGroupLaw := inferInstance
  representation := S1298Representation l
  representation_surjective :=
    (S1298GeneralLinearRepresentation l).rangeRestrict_surjective
  imageContainsSL2 := S1298LargeImageField l
  imageContainsSL2_proved := G.imageContainsSL2_proved
  sixTorsionIndependent := G.sixTorsionIndependent
  sixTorsionIndependent_proved := G.sixTorsionIndependent_proved
  lTorsionCompatible := G.lTorsionCompatible
  lTorsionCompatible_proved := G.lTorsionCompatible_proved

@[simp] theorem s1298SourceTorsionClauseOfGap_torsionCarrier (l : PrimeGeFive)
    (G : S1298TorsionSourceGap l) :
    (s1298SourceTorsionClauseOfGap l G).torsionCarrier =
      S1298SixTorsionCarrier l :=
  rfl

@[simp] theorem s1298SourceTorsionClauseOfGap_torsionLabel (l : PrimeGeFive)
    (G : S1298TorsionSourceGap l) :
    (s1298SourceTorsionClauseOfGap l G).torsionLabel =
      s1298SixTorsionLabel l :=
  rfl

@[simp] theorem s1298SourceTorsionClauseOfGap_representation (l : PrimeGeFive)
    (G : S1298TorsionSourceGap l) :
    (s1298SourceTorsionClauseOfGap l G).representation =
      S1298Representation l :=
  rfl

@[simp] theorem s1298SourceTorsionClauseOfGap_imageContainsSL2
    (l : PrimeGeFive) (G : S1298TorsionSourceGap l) :
    (s1298SourceTorsionClauseOfGap l G).imageContainsSL2 =
      S1298LargeImageField l :=
  rfl

/-- The gap's first field is still exactly a rank-two basis. -/
theorem s1298TorsionSourceGap_firstField (l : PrimeGeFive)
    (G : S1298TorsionSourceGap l) : Nonempty (S1298TorsionBasisType l) :=
  s1298LargeImageField_firstField l G.imageContainsSL2_proved

/-! ## 4. The existing D5 bridge, with the exact first field isolated -/

/-- The source-faithful D5 supply, assembled from the exact basis, the tail,
the actual six-torsion carrier and label, and the two source conditions. -/
noncomputable def s1298D5TorsionSupplyOfBasis (l : PrimeGeFive)
    (b : S1298TorsionBasisType l) (t : S1298D5Tail l b)
    (sixTorsionIndependent : Prop) (hsix : sixTorsionIndependent)
    (lTorsionCompatible : Prop) (hlc : lTorsionCompatible) :
    InitialThetaSource.Definition31D4D9Supply.D5TorsionSupply l
      (S1280Arithmetic l) where
  datum := s1298D5DatumOfBasisAndTail l b t
  torsionCarrier := S1298SixTorsionCarrier l
  torsionCarrierLaw := inferInstance
  torsionLabel := s1298SixTorsionLabel l
  torsionNonempty := ⟨1⟩
  sixTorsionIndependent := sixTorsionIndependent
  sixTorsionIndependent_proved := hsix
  lTorsionCompatible := lTorsionCompatible
  lTorsionCompatible_proved := hlc

/-- The D5 bridge to SourceTorsionClause keeps the actual six-torsion carrier. -/
theorem s1298D5TorsionSupplyOfBasis_toTorsionClause_torsionCarrier
    (l : PrimeGeFive) (b : S1298TorsionBasisType l) (t : S1298D5Tail l b)
    (sixTorsionIndependent : Prop) (hsix : sixTorsionIndependent)
    (lTorsionCompatible : Prop) (hlc : lTorsionCompatible) :
    (s1298D5TorsionSupplyOfBasis l b t sixTorsionIndependent hsix
      lTorsionCompatible hlc).toTorsionClause.torsionCarrier =
      S1298SixTorsionCarrier l :=
  rfl

/-- Exact first-field chain: the D5 clause produced by the standard bridge
has the actual six-torsion carrier, and its D5 datum's first field is the
rank-two basis. -/
theorem s1298D5TorsionSupplyOfBasis_toTorsionClause_firstField
    (l : PrimeGeFive) (b : S1298TorsionBasisType l) (t : S1298D5Tail l b)
    (sixTorsionIndependent : Prop) (hsix : sixTorsionIndependent)
    (lTorsionCompatible : Prop) (hlc : lTorsionCompatible) :
    (s1298D5TorsionSupplyOfBasis l b t sixTorsionIndependent hsix
      lTorsionCompatible hlc).datum.torsion_basis = b :=
  rfl

/-! ## 5. The exact barrier at the existing tree donor -/

/-- No PrimeGeFive label is 3.  The tree's one unconditional odd-level
rank-two basis is at level 3 (the theorem
LeanFormal.IUT.IUTII.Frobenioid.Example36.TateModuleProfinite.tateLevelThree_nonempty_basis,
for the different curve y^2 = x^3 - x), so it cannot be a D5 level. -/
theorem s1298PrimeGeFive_ne_three (l : PrimeGeFive) : l.value ≠ 3 := by
  intro h
  have h5 := l.ge_five
  rw [h] at h5
  norm_num at h5

-- The exact donor is present in the tree, at level 3 and for y^2 = x^3 - x.
#check LeanFormal.IUT.IUTII.Frobenioid.Example36.TateModuleProfinite.tateLevelThree_nonempty_basis

/-! ## 6. Exact first-field chain -/

/-- The S1280 target field is unchanged: it is still literally the clause. -/
theorem s1298S1280FirstMissingField_eq_clause (l : PrimeGeFive) :
    S1280FirstMissingField l = SourceTorsionClause.{0, 0, 0} l :=
  rfl

/-- The exact first-field chain in one statement.  The basis is equivalent to
the frozen rank-two gap; the large-image statement supplies the basis; and the
D5 datum is exactly a basis together with its two tail fields. -/
theorem s1298FirstFieldChain (l : PrimeGeFive) :
    (Nonempty (S1298TorsionBasisType l) ↔
      RankTwoTorsionBasisGap (S1280Arithmetic l).curve l) ∧
    (S1298LargeImageField l → Nonempty (S1298TorsionBasisType l)) ∧
    (Nonempty (S1298D5Datum l) ↔
      ∃ b : S1298TorsionBasisType l, Nonempty (S1298D5Tail l b)) :=
  ⟨s1298TorsionBasisType_iff_rankTwoGap l,
    s1298LargeImageField_firstField l,
    s1298D5Datum_nonempty_iff l⟩

/-! ## 7. Axiom footprint -/

#print axioms s1298TorsionBasisType_iff_rankTwoGap
#print axioms s1298TorsionBasisType_iff_finrank_eq_two
#print axioms s1298TorsionBasisType_nonempty_iff_cardinalityCard
#print axioms s1298D5DatumEquiv
#print axioms s1298D5Datum_firstField
#print axioms s1298D5Datum_nonempty_iff
#print axioms s1298SixTorsionLabel_surjective
#print axioms s1298SourceTorsionClauseOfGap
#print axioms s1298LargeImageField_iff_exists_basis
#print axioms s1298TorsionSourceGap_firstField
#print axioms s1298D5TorsionSupplyOfBasis_toTorsionClause_firstField
#print axioms s1298S1280FirstMissingField_eq_clause
#print axioms s1298FirstFieldChain

end LeanFormal.IUT.XiFPaper.S1298TorsionClauseActual

end
