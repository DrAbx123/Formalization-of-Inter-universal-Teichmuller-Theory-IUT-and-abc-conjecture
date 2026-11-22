import tmp.sheaf.xif.paper.S1280SourceDefinition31Actual
import LeanFormal.IUT.IUTI.InitialTheta.SourceDefinition31D4D9Supply
import LeanFormal.IUT.IUTII.Frobenioid.Example36SourceTheaterCarrier

/-!
# S1320: actual D7 section prefix and D8 cusp boundary over the S1280 Gaussian data

S1280 constructs the actual Definition 3.1 D3/D4 prefix over

  concreteGaussianInitialThetaArithmeticData l

(the actual field Q(i), the actual base-changed split multiplicative curve
y^2 + xy = x^3 + 5, the actual finite place above 5, the actual bad-place
selection, and the actual place partition and reduction clause).  This file is
the next field-level package: it constructs every part of the D7 section clause
and D8 cusp clause that the actual Gaussian curve determines, and it states the
exact first field that remains a genuine source input.

## D7: actual place section, exact local-group field

The D7a place-section half is constructed unconditionally by

  SourceValuationSectionLayer.canonical (S1280Arithmetic l).

Its carrier pair and section map are the actual restriction/lift data of the
identity tower Q(i) = F_mod = F = K.  The fields

  valuationCarrier, modifiedValuationCarrier,
  sectionMap, sectionRightInverse, section_left_inverse, section_right_inverse

of 'SourceSectionClause' are therefore actual.  The fully assembled clause is
'd7SectionLayerBridge L G', where 'G' is the exact D7b intake.

The first field of 'SourceSectionClause' that the actual arithmetic data does
not determine is field 3,

  localGroupCarrier : L.valuationCarrier -> Type.

The exact D7b object bundle is 'D7LocalGroupSectionSupply L'.  This file:
* constructs the actual section prefix and proves its six fields are the
  canonical layer's fields;
* decomposes D7b as 'localGroupCarrier' together with a tail
  ('S1320D7SupplyEquiv');
* constructs the full 'SourceSectionClause' conditionally on exactly D7b;
* proves the constructed clause's section and local-group fields are the
  supplied/actual ones;
* feeds the clause into the S1280 remaining-clause assembly and shows it is
  literally the 'sections' field of the Definition 3.1 data.

The actual local field/arithmetic Galois group/unit group at the concrete
Gaussian place are *not* the curve-side Pi_Xv/Pi_Cv local group of Definition
3.1(e).  They are therefore not substituted into 'localGroupCarrier'.  The
curve-side D7b object needs the D6 orbicurve and its etale fundamental groups,
which the tree does not construct.

## D8: exact real cusp coordinate

The source cusp of Definition 3.1(f) is geometric.  The current contract
'SourceCuspClause' encodes it by a real 'epsilon' and a positive 'cuspScale'.
The actual Gaussian curve gives an actual geometric cusp point, proved below to
have projective coordinates [0 : 1 : 0], and an actual q-parameter norm
'gaussianFiveThetaQ = 1/5'.  Neither is a real cusp coordinate: the first is a
projective point of the curve, and the second is the norm of the Tate
q-parameter, not the selected cusp epsilon.

The first field of 'SourceCuspClause' is

  epsilon : Real.

This file:
* constructs the actual geometric cusp point and its coordinates;
* constructs the actual q-parameter norm and proves it is 1/5;
* decomposes 'SourceCuspClause' exactly as 'epsilon' plus a tail
  ('S1320CuspClauseEquiv');
* constructs the cusp clause conditionally on explicit real cusp data;
* proves every cusp clause has its first field 'epsilon' and that a cusp clause
  is exactly a real first field plus the remaining tail;
* feeds the conditional clause into the S1280 assembly and shows it is
  literally the 'cusp' field of the Definition 3.1 data.

No arbitrary real, no True/PUnit/trivial group, no fake cusp coordinate, and no
new axiom is introduced.  The exact first fields are stated, not filled.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 1000000

noncomputable section

namespace LeanFormal.IUT.XiFPaper.S1320SectionsCuspActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.Definition31D4D9Supply
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.XiFPaper.S1280SourceDefinition31Actual
open LeanFormal.IUT.IUTII.Frobenioid.Example36.SourceTheaterCarrier

local instance s1320GaussianIrreducible :
    Fact (Irreducible (Polynomial.X ^ 2 - Polynomial.C (-1) : Polynomial ℚ)) :=
  ⟨gaussianPolynomial_irreducible⟩

local instance s1320FivePrime : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩

/-! ## 1. The actual D7a place-section layer -/

/-- The canonical D7a place-section layer of the S1280 Gaussian arithmetic
input.  This is the actual section V -> V_mod of Definition 3.1(e): the
selected places of K = Q(i) and the restriction/lift maps of the identity
tower. -/
abbrev S1320Layer (l : PrimeGeFive) :
    SourceValuationSectionLayer (S1280Arithmetic l) :=
  SourceValuationSectionLayer.canonical (S1280Arithmetic l)

/-- The actual upstairs carrier: the selected places of K = Q(i). -/
theorem S1320ValuationCarrier_eq (l : PrimeGeFive) :
    (S1320Layer l).valuationCarrier =
      {v : NumberFieldPlace (S1280Arithmetic l).K //
        v ∈ (SourceArithmeticPrelude.canonical
          (S1280Arithmetic l)).selectedPlaces} := rfl

/-- The actual downstairs carrier: the places of F_mod = Q(i). -/
theorem S1320ModifiedValuationCarrier_eq (l : PrimeGeFive) :
    (S1320Layer l).modifiedValuationCarrier =
      NumberFieldPlace (S1280Arithmetic l).Fmod := rfl

/-- The section map is the actual place restriction, not an arbitrary map. -/
theorem S1320SectionMap_apply (l : PrimeGeFive)
    (v : (S1320Layer l).valuationCarrier) :
    (S1320Layer l).sectionMap v =
      NumberFieldPlace.comap (k := (S1280Arithmetic l).Fmod) v.1 :=
  valuationSectionMap_eq_comap
    (SourceArithmeticPrelude.canonical (S1280Arithmetic l)) v

/-- The right inverse is the actual place lift, not an arbitrary map. -/
theorem S1320SectionRightInverse_apply (l : PrimeGeFive)
    (w : (S1320Layer l).modifiedValuationCarrier) :
    ((S1320Layer l).sectionRightInverse w).1 =
      (SourceArithmeticPrelude.canonical
        (S1280Arithmetic l)).placeSection.lift w :=
  valuationSectionRightInverse_apply
    (SourceArithmeticPrelude.canonical (S1280Arithmetic l)) w

/-- The actual place restriction is bijective: this is the Definition 3.1(e)
section property. -/
theorem S1320SectionMap_bijective (l : PrimeGeFive) :
    Function.Bijective (S1320Layer l).sectionMap :=
  valuationSectionMap_bijective
    (SourceArithmeticPrelude.canonical (S1280Arithmetic l))

/-- The actual place lift is bijective. -/
theorem S1320SectionRightInverse_bijective (l : PrimeGeFive) :
    Function.Bijective (S1320Layer l).sectionRightInverse :=
  valuationSectionRightInverse_bijective
    (SourceArithmeticPrelude.canonical (S1280Arithmetic l))

/-- The left round trip V -> V_mod -> V. -/
theorem S1320Section_left_inverse (l : PrimeGeFive)
    (v : (S1320Layer l).valuationCarrier) :
    (S1320Layer l).sectionRightInverse ((S1320Layer l).sectionMap v) = v :=
  (S1320Layer l).section_left_inverse v

/-- The right round trip V_mod -> V -> V_mod. -/
theorem S1320Section_right_inverse (l : PrimeGeFive)
    (w : (S1320Layer l).modifiedValuationCarrier) :
    (S1320Layer l).sectionMap ((S1320Layer l).sectionRightInverse w) = w :=
  (S1320Layer l).section_right_inverse w

/-! ## 2. The exact D7 section prefix -/

/-- The six place-section fields of 'SourceSectionClause', as a record. -/
structure S1320SectionPrefix where
  valuationCarrier : Type
  modifiedValuationCarrier : Type
  sectionMap : valuationCarrier → modifiedValuationCarrier
  sectionRightInverse : modifiedValuationCarrier → valuationCarrier
  section_left_inverse : ∀ x, sectionRightInverse (sectionMap x) = x
  section_right_inverse : ∀ y, sectionMap (sectionRightInverse y) = y

/-- The prefix of any D7 clause. -/
def S1320ClausePrefix (S : SourceSectionClause.{0, 0, 0}) : S1320SectionPrefix where
  valuationCarrier := S.valuationCarrier
  modifiedValuationCarrier := S.modifiedValuationCarrier
  sectionMap := S.sectionMap
  sectionRightInverse := S.sectionRightInverse
  section_left_inverse := S.section_left_inverse
  section_right_inverse := S.section_right_inverse

/-- The actual prefix determined by the Gaussian place-section layer. -/
def S1320ActualPrefix (l : PrimeGeFive) : S1320SectionPrefix where
  valuationCarrier := (S1320Layer l).valuationCarrier
  modifiedValuationCarrier := (S1320Layer l).modifiedValuationCarrier
  sectionMap := (S1320Layer l).sectionMap
  sectionRightInverse := (S1320Layer l).sectionRightInverse
  section_left_inverse := (S1320Layer l).section_left_inverse
  section_right_inverse := (S1320Layer l).section_right_inverse

/-! ## 3. D7b: exact first field and the conditional clause -/

universe w

/-- Everything in 'D7LocalGroupSectionSupply' after the first field
'localGroupCarrier'.  This is the exact tail of D7b once its first field is
chosen. -/
structure S1320D7Tail (l : PrimeGeFive)
    (G0 : (S1320Layer l).valuationCarrier → Type w) where
  modifiedLocalGroupCarrier :
    (S1320Layer l).modifiedValuationCarrier → Type w
  localGroupSection :
    ∀ x, G0 x → modifiedLocalGroupCarrier ((S1320Layer l).sectionMap x)
  localGroupSection_injective :
    ∀ x, Function.Injective (localGroupSection x)
  localGroupSection_surjective :
    ∀ x, Function.Surjective (localGroupSection x)
  finitePlaceData : Prop
  finitePlaceData_proved : finitePlaceData
  infinitePlaceData : Prop
  infinitePlaceData_proved : infinitePlaceData

/-- Exact decomposition of the D7b intake: it is first field
'localGroupCarrier' together with the exact tail.  This is the formal statement
that the first missing field is the local-group carrier family. -/
noncomputable def S1320D7SupplyEquiv (l : PrimeGeFive) :
    D7LocalGroupSectionSupply.{0, 0} (S1320Layer l) ≃
      Σ G0 : (S1320Layer l).valuationCarrier → Type,
        S1320D7Tail l G0 where
  toFun G :=
    ⟨G.localGroupCarrier,
      { modifiedLocalGroupCarrier := G.modifiedLocalGroupCarrier
        localGroupSection := G.localGroupSection
        localGroupSection_injective := G.localGroupSection_injective
        localGroupSection_surjective := G.localGroupSection_surjective
        finitePlaceData := G.finitePlaceData
        finitePlaceData_proved := G.finitePlaceData_proved
        infinitePlaceData := G.infinitePlaceData
        infinitePlaceData_proved := G.infinitePlaceData_proved }⟩
  invFun p :=
    { localGroupCarrier := p.1
      modifiedLocalGroupCarrier := p.2.modifiedLocalGroupCarrier
      localGroupSection := p.2.localGroupSection
      localGroupSection_injective := p.2.localGroupSection_injective
      localGroupSection_surjective := p.2.localGroupSection_surjective
      finitePlaceData := p.2.finitePlaceData
      finitePlaceData_proved := p.2.finitePlaceData_proved
      infinitePlaceData := p.2.infinitePlaceData
      infinitePlaceData_proved := p.2.infinitePlaceData_proved }
  left_inv G := by cases G; rfl
  right_inv p := by rcases p with ⟨G0, t⟩; cases t; rfl

@[simp] theorem S1320D7SupplyEquiv_fst (l : PrimeGeFive)
    (G : D7LocalGroupSectionSupply.{0, 0} (S1320Layer l)) :
    (S1320D7SupplyEquiv l G).1 = G.localGroupCarrier := rfl

/-- The exact first field of D7b: the local-group carrier family over the
actual place-section carrier.  This is the first ray of the curve-side
Pi_Xv/Pi_Cv data.  It is not the arithmetic local Galois group G_v. -/
abbrev S1320D7FirstField (l : PrimeGeFive) : Type 1 :=
  (S1320Layer l).valuationCarrier → Type

/-- Any D7b supply projects to its first field. -/
def S1320D7FirstFieldOfSupply (l : PrimeGeFive)
    (G : D7LocalGroupSectionSupply.{0, 0} (S1320Layer l)) :
    S1320D7FirstField l :=
  G.localGroupCarrier

/-- The first D7b field is necessary for any supply. -/
theorem S1320D7FirstField_needed (l : PrimeGeFive)
    (G : D7LocalGroupSectionSupply.{0, 0} (S1320Layer l)) :
    Nonempty (S1320D7FirstField l) :=
  ⟨S1320D7FirstFieldOfSupply l G⟩

/-- Exact first-field decomposition of D7b. -/
theorem S1320D7Supply_nonempty_iff_firstField_tail (l : PrimeGeFive) :
    Nonempty (D7LocalGroupSectionSupply.{0, 0} (S1320Layer l)) ↔
      ∃ G0 : S1320D7FirstField l,
        Nonempty (S1320D7Tail l G0) := by
  constructor
  · rintro ⟨G⟩
    exact ⟨G.localGroupCarrier,
      ⟨{ modifiedLocalGroupCarrier := G.modifiedLocalGroupCarrier
         localGroupSection := G.localGroupSection
         localGroupSection_injective := G.localGroupSection_injective
         localGroupSection_surjective := G.localGroupSection_surjective
         finitePlaceData := G.finitePlaceData
         finitePlaceData_proved := G.finitePlaceData_proved
         infinitePlaceData := G.infinitePlaceData
         infinitePlaceData_proved := G.infinitePlaceData_proved }⟩⟩
  · rintro ⟨G0, ⟨t⟩⟩
    exact ⟨{ localGroupCarrier := G0
             modifiedLocalGroupCarrier := t.modifiedLocalGroupCarrier
             localGroupSection := t.localGroupSection
             localGroupSection_injective := t.localGroupSection_injective
             localGroupSection_surjective := t.localGroupSection_surjective
             finitePlaceData := t.finitePlaceData
             finitePlaceData_proved := t.finitePlaceData_proved
             infinitePlaceData := t.infinitePlaceData
             infinitePlaceData_proved := t.infinitePlaceData_proved }⟩

/-- The full 'SourceSectionClause' assembled from the actual place-section
layer and exactly the D7b intake. -/
noncomputable def S1320SectionClauseOfSupply (l : PrimeGeFive)
    (G : D7LocalGroupSectionSupply.{0, 0} (S1320Layer l)) :
    SourceSectionClause.{0, 0, 0} :=
  d7SectionLayerBridge (S1320Layer l) G

@[simp] theorem S1320SectionClauseOfSupply_valuationCarrier
    (l : PrimeGeFive)
    (G : D7LocalGroupSectionSupply.{0, 0} (S1320Layer l)) :
    (S1320SectionClauseOfSupply l G).valuationCarrier =
      (S1320Layer l).valuationCarrier := rfl

@[simp] theorem S1320SectionClauseOfSupply_modifiedValuationCarrier
    (l : PrimeGeFive)
    (G : D7LocalGroupSectionSupply.{0, 0} (S1320Layer l)) :
    (S1320SectionClauseOfSupply l G).modifiedValuationCarrier =
      (S1320Layer l).modifiedValuationCarrier := rfl

@[simp] theorem S1320SectionClauseOfSupply_localGroupCarrier
    (l : PrimeGeFive)
    (G : D7LocalGroupSectionSupply.{0, 0} (S1320Layer l)) :
    (S1320SectionClauseOfSupply l G).localGroupCarrier =
      G.localGroupCarrier := rfl

@[simp] theorem S1320SectionClauseOfSupply_modifiedLocalGroupCarrier
    (l : PrimeGeFive)
    (G : D7LocalGroupSectionSupply.{0, 0} (S1320Layer l)) :
    (S1320SectionClauseOfSupply l G).modifiedLocalGroupCarrier =
      G.modifiedLocalGroupCarrier := rfl

@[simp] theorem S1320SectionClauseOfSupply_sectionMap
    (l : PrimeGeFive)
    (G : D7LocalGroupSectionSupply.{0, 0} (S1320Layer l)) :
    (S1320SectionClauseOfSupply l G).sectionMap =
      (S1320Layer l).sectionMap := rfl

@[simp] theorem S1320SectionClauseOfSupply_sectionRightInverse
    (l : PrimeGeFive)
    (G : D7LocalGroupSectionSupply.{0, 0} (S1320Layer l)) :
    (S1320SectionClauseOfSupply l G).sectionRightInverse =
      (S1320Layer l).sectionRightInverse := rfl

@[simp] theorem S1320SectionClauseOfSupply_localGroupSection
    (l : PrimeGeFive)
    (G : D7LocalGroupSectionSupply.{0, 0} (S1320Layer l)) :
    (S1320SectionClauseOfSupply l G).localGroupSection =
      G.localGroupSection := rfl

@[simp] theorem S1320SectionClauseOfSupply_localGroupSection_injective
    (l : PrimeGeFive)
    (G : D7LocalGroupSectionSupply.{0, 0} (S1320Layer l)) :
    (S1320SectionClauseOfSupply l G).localGroupSection_injective =
      G.localGroupSection_injective := rfl

@[simp] theorem S1320SectionClauseOfSupply_localGroupSection_surjective
    (l : PrimeGeFive)
    (G : D7LocalGroupSectionSupply.{0, 0} (S1320Layer l)) :
    (S1320SectionClauseOfSupply l G).localGroupSection_surjective =
      G.localGroupSection_surjective := rfl

@[simp] theorem S1320SectionClauseOfSupply_finitePlaceData
    (l : PrimeGeFive)
    (G : D7LocalGroupSectionSupply.{0, 0} (S1320Layer l)) :
    (S1320SectionClauseOfSupply l G).finitePlaceData =
      G.finitePlaceData := rfl

@[simp] theorem S1320SectionClauseOfSupply_finitePlaceData_proved
    (l : PrimeGeFive)
    (G : D7LocalGroupSectionSupply.{0, 0} (S1320Layer l)) :
    (S1320SectionClauseOfSupply l G).finitePlaceData_proved =
      G.finitePlaceData_proved := rfl

@[simp] theorem S1320SectionClauseOfSupply_infinitePlaceData
    (l : PrimeGeFive)
    (G : D7LocalGroupSectionSupply.{0, 0} (S1320Layer l)) :
    (S1320SectionClauseOfSupply l G).infinitePlaceData =
      G.infinitePlaceData := rfl

@[simp] theorem S1320SectionClauseOfSupply_infinitePlaceData_proved
    (l : PrimeGeFive)
    (G : D7LocalGroupSectionSupply.{0, 0} (S1320Layer l)) :
    (S1320SectionClauseOfSupply l G).infinitePlaceData_proved =
      G.infinitePlaceData_proved := rfl

/-- The six-field prefix of the constructed clause is exactly the actual
place-section prefix. -/
theorem S1320SectionClauseOfSupply_prefix
    (l : PrimeGeFive)
    (G : D7LocalGroupSectionSupply.{0, 0} (S1320Layer l)) :
    S1320ClausePrefix (S1320SectionClauseOfSupply l G) =
      S1320ActualPrefix l := rfl

/-! ## 4. D8: exact first field and the conditional clause -/

/-- Everything in 'SourceCuspClause' after the first field 'epsilon'. -/
structure S1320CuspTail (epsilon : Real) where
  epsilon_positive : 0 < epsilon
  epsilon_nonzero : epsilon ≠ 0
  epsilon_compatibility : Prop
  epsilon_compatibility_proved : epsilon_compatibility
  cuspScale : Real
  cuspScale_positive : 0 < cuspScale
  epsilon_scale_relation : epsilon * cuspScale ≠ 0

/-- The exact first field of D8: a real cusp coordinate. -/
abbrev S1320CuspFirstField : Type := Real

/-- Exact decomposition of 'SourceCuspClause': the first field 'epsilon'
together with its tail. -/
abbrev S1320CuspDecomposition : Type :=
  Σ e : S1320CuspFirstField, S1320CuspTail e

/-- The cusp clause is exactly a real first field plus the exact tail.  This
records both that the first field is 'epsilon' and that the current contract
does not determine its value. -/
noncomputable def S1320CuspClauseEquiv :
    SourceCuspClause ≃ S1320CuspDecomposition where
  toFun C :=
    ⟨C.epsilon,
      { epsilon_positive := C.epsilon_positive
        epsilon_nonzero := C.epsilon_nonzero
        epsilon_compatibility := C.epsilon_compatibility
        epsilon_compatibility_proved := C.epsilon_compatibility_proved
        cuspScale := C.cuspScale
        cuspScale_positive := C.cuspScale_positive
        epsilon_scale_relation := C.epsilon_scale_relation }⟩
  invFun p :=
    { epsilon := p.1
      epsilon_positive := p.2.epsilon_positive
      epsilon_nonzero := p.2.epsilon_nonzero
      epsilon_compatibility := p.2.epsilon_compatibility
      epsilon_compatibility_proved := p.2.epsilon_compatibility_proved
      cuspScale := p.2.cuspScale
      cuspScale_positive := p.2.cuspScale_positive
      epsilon_scale_relation := p.2.epsilon_scale_relation }
  left_inv C := by cases C; rfl
  right_inv p := by rcases p with ⟨e, t⟩; cases t; rfl

@[simp] theorem S1320CuspClauseEquiv_fst (C : SourceCuspClause) :
    (S1320CuspClauseEquiv C).1 = C.epsilon := rfl

/-- Conditional cusp clause from an explicit real cusp coordinate and its exact
tail.  The real value is the input, never an arbitrary constant of this file. -/
noncomputable def S1320CuspClauseOfData
    (e : Real) (t : S1320CuspTail e) : SourceCuspClause where
  epsilon := e
  epsilon_positive := t.epsilon_positive
  epsilon_nonzero := t.epsilon_nonzero
  epsilon_compatibility := t.epsilon_compatibility
  epsilon_compatibility_proved := t.epsilon_compatibility_proved
  cuspScale := t.cuspScale
  cuspScale_positive := t.cuspScale_positive
  epsilon_scale_relation := t.epsilon_scale_relation

@[simp] theorem S1320CuspClauseOfData_epsilon
    (e : Real) (t : S1320CuspTail e) :
    (S1320CuspClauseOfData e t).epsilon = e := rfl

@[simp] theorem S1320CuspClauseOfData_epsilon_positive
    (e : Real) (t : S1320CuspTail e) :
    0 < (S1320CuspClauseOfData e t).epsilon :=
  t.epsilon_positive

@[simp] theorem S1320CuspClauseOfData_epsilon_nonzero
    (e : Real) (t : S1320CuspTail e) :
    (S1320CuspClauseOfData e t).epsilon ≠ 0 :=
  t.epsilon_nonzero

@[simp] theorem S1320CuspClauseOfData_cuspScale
    (e : Real) (t : S1320CuspTail e) :
    (S1320CuspClauseOfData e t).cuspScale = t.cuspScale := rfl

@[simp] theorem S1320CuspClauseOfData_cuspScale_positive
    (e : Real) (t : S1320CuspTail e) :
    0 < (S1320CuspClauseOfData e t).cuspScale :=
  t.cuspScale_positive

/-- The first field of a cusp clause. -/
def S1320CuspFirstFieldOfClause (C : SourceCuspClause) :
    S1320CuspFirstField :=
  C.epsilon

/-- Exact first-field decomposition of D8. -/
theorem S1320CuspClause_nonempty_iff_firstField_tail :
    Nonempty SourceCuspClause ↔
      ∃ e : S1320CuspFirstField, Nonempty (S1320CuspTail e) := by
  constructor
  · rintro ⟨C⟩
    exact ⟨C.epsilon,
      ⟨{ epsilon_positive := C.epsilon_positive
         epsilon_nonzero := C.epsilon_nonzero
         epsilon_compatibility := C.epsilon_compatibility
         epsilon_compatibility_proved := C.epsilon_compatibility_proved
         cuspScale := C.cuspScale
         cuspScale_positive := C.cuspScale_positive
         epsilon_scale_relation := C.epsilon_scale_relation }⟩⟩
  · rintro ⟨e, ⟨t⟩⟩
    exact ⟨S1320CuspClauseOfData e t⟩

/-! ## 5. Actual Gaussian cusp point and q-parameter norm -/

/-- The actual geometric cusp point of the S1280 curve: the puncture of the
base-changed split multiplicative curve. -/
abbrev S1320ActualCuspPoint (l : PrimeGeFive) :
    (S1280Arithmetic l).curve.curve.toProjective.Point :=
  (S1280Arithmetic l).curve.puncture

/-- The actual cusp point is the puncture of the concrete base-changed split
curve. -/
theorem S1320ActualCuspPoint_eq_baseChange (l : PrimeGeFive) :
    S1320ActualCuspPoint l =
      (concreteSplitPuncturedCurve.baseChange GaussianField).puncture := rfl

/-- The actual cusp point has projective coordinates [0 : 1 : 0]: it is the
cusp at infinity, not an affine chart choice. -/
theorem S1320ActualCuspPoint_point (l : PrimeGeFive) :
    (S1320ActualCuspPoint l).point =
      (⟦![0, 1, 0]⟧ :
        WeierstrassCurve.Projective.PointClass (S1280Arithmetic l).F) := by
  rw [S1320ActualCuspPoint, concreteGaussianInitialThetaArithmeticData_curve]
  simp only [PuncturedEllipticCurve.baseChange, PuncturedEllipticCurve.map,
    concreteSplitPuncturedCurve]
  rw [PuncturedEllipticCurve.projectivePointMap_point,
    PuncturedEllipticCurve.projectivePointClassMap_mk]
  congr 1
  funext i
  fin_cases i <;> simp <;> rfl

/-- The actual q-parameter norm of the Gaussian source: the norm of the local
q-parameter at 5.  This is an actual real number determined by the curve and
its split multiplicative place. -/
noncomputable def S1320ActualQ (l : PrimeGeFive) : Real :=
  gaussianFiveThetaQ

theorem S1320ActualQ_pos (l : PrimeGeFive) : 0 < S1320ActualQ l :=
  gaussianFiveThetaQ_pos

/-- The actual value is 1/5. -/
theorem S1320ActualQ_eq (l : PrimeGeFive) :
    S1320ActualQ l = (5 : ℝ)⁻¹ :=
  gaussianFiveThetaQ_eq_inv_five

theorem S1320ActualQ_ne_zero (l : PrimeGeFive) :
    S1320ActualQ l ≠ 0 :=
  ne_of_gt (S1320ActualQ_pos l)

theorem S1320ActualQ_lt_one (l : PrimeGeFive) :
    S1320ActualQ l < 1 := by
  rw [S1320ActualQ_eq]
  norm_num

theorem S1320ActualQ_ne_one (l : PrimeGeFive) :
    S1320ActualQ l ≠ 1 :=
  ne_of_lt (S1320ActualQ_lt_one l)

/-! ## 6. Consumer: the S1280 Definition 3.1 assembly -/

/-- The S1280 remaining-clause package with the actual D7 section prefix and
the supplied D5/D6/D7b/D8 data. -/
noncomputable def S1320RemainingClauses (l : PrimeGeFive)
    (T : SourceTorsionClause.{0, 0, 0} l)
    (O : SourceOrbicurveClause.{0, 0, 0})
    (G : D7LocalGroupSectionSupply.{0, 0} (S1320Layer l))
    (C : SourceCuspClause) : S1280RemainingClauses l where
  torsion := T
  orbicurve := O
  sections := S1320SectionClauseOfSupply l G
  cusp := C

@[simp] theorem S1320RemainingClauses_sections (l : PrimeGeFive)
    (T : SourceTorsionClause.{0, 0, 0} l)
    (O : SourceOrbicurveClause.{0, 0, 0})
    (G : D7LocalGroupSectionSupply.{0, 0} (S1320Layer l))
    (C : SourceCuspClause) :
    (S1320RemainingClauses l T O G C).sections =
      S1320SectionClauseOfSupply l G := rfl

@[simp] theorem S1320RemainingClauses_cusp (l : PrimeGeFive)
    (T : SourceTorsionClause.{0, 0, 0} l)
    (O : SourceOrbicurveClause.{0, 0, 0})
    (G : D7LocalGroupSectionSupply.{0, 0} (S1320Layer l))
    (C : SourceCuspClause) :
    (S1320RemainingClauses l T O G C).cusp = C := rfl

/-- The constructed D7 clause is literally the 'sections' field of the
Definition 3.1 data assembled by S1280 from the actual D3/D4 prefix. -/
theorem S1320SourceData_sections (l : PrimeGeFive)
    (T : SourceTorsionClause.{0, 0, 0} l)
    (O : SourceOrbicurveClause.{0, 0, 0})
    (G : D7LocalGroupSectionSupply.{0, 0} (S1320Layer l))
    (C : SourceCuspClause)
    (redCompat : Prop) (hredCompat : redCompat)
    (torCompat : Prop) (htorCompat : torCompat)
    (orbCompat : Prop) (horbCompat : orbCompat)
    (secCompat : Prop) (hsecCompat : secCompat)
    (cusCompat : Prop) (hcusCompat : cusCompat) :
    (S1280SourceData_of_remaining l (S1320RemainingClauses l T O G C)
      redCompat hredCompat torCompat htorCompat orbCompat horbCompat
      secCompat hsecCompat cusCompat hcusCompat).sections =
        S1320SectionClauseOfSupply l G := rfl

/-- The supplied D8 clause is literally the 'cusp' field of the assembled
Definition 3.1 data. -/
theorem S1320SourceData_cusp (l : PrimeGeFive)
    (T : SourceTorsionClause.{0, 0, 0} l)
    (O : SourceOrbicurveClause.{0, 0, 0})
    (G : D7LocalGroupSectionSupply.{0, 0} (S1320Layer l))
    (C : SourceCuspClause)
    (redCompat : Prop) (hredCompat : redCompat)
    (torCompat : Prop) (htorCompat : torCompat)
    (orbCompat : Prop) (horbCompat : orbCompat)
    (secCompat : Prop) (hsecCompat : secCompat)
    (cusCompat : Prop) (hcusCompat : cusCompat) :
    (S1280SourceData_of_remaining l (S1320RemainingClauses l T O G C)
      redCompat hredCompat torCompat htorCompat orbCompat horbCompat
      secCompat hsecCompat cusCompat hcusCompat).cusp = C := rfl

/-! ## 7. Axiom footprint -/

#print axioms S1320Layer
#print axioms S1320SectionMap_apply
#print axioms S1320SectionMap_bijective
#print axioms S1320D7SupplyEquiv
#print axioms S1320D7FirstFieldOfSupply
#print axioms S1320D7Supply_nonempty_iff_firstField_tail
#print axioms S1320SectionClauseOfSupply
#print axioms S1320SectionClauseOfSupply_prefix
#print axioms S1320CuspClauseEquiv
#print axioms S1320CuspClauseOfData
#print axioms S1320CuspClause_nonempty_iff_firstField_tail
#print axioms S1320ActualCuspPoint_point
#print axioms S1320ActualQ_eq
#print axioms S1320SourceData_sections
#print axioms S1320SourceData_cusp

end LeanFormal.IUT.XiFPaper.S1320SectionsCuspActual

end