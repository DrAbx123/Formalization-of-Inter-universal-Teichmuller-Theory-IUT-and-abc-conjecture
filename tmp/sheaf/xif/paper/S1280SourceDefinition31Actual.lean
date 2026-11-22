import LeanFormal.IUT.IUTI.InitialTheta.ConcreteFinitePlaceBoundary
import LeanFormal.IUT.IUTII.Frobenioid.Example36GaussianSplitPlaceArithmetic
import LeanFormal.IUT.IUTI.InitialTheta.SourceDefinition31D4D9Supply

/-!
# S1280: the actual Definition 3.1 prefix from the concrete Gaussian data

This file constructs, from data already present and proved in the tree (no new
source hypothesis, no PUnit/True placeholder, no arbitrary Classical.choice of
a clause field):

* the arithmetic input S1280Arithmetic l, the concrete Gaussian initial Theta
  data concreteGaussianInitialThetaArithmeticData l (actual Q(i), actual
  base-changed split multiplicative curve);
* the actual finite place concreteGaussianFivePlace above 5, with proved
  residue characteristic 5 and hence oddness;
* the Definition 3.1(b) source place selection S1280Selection l
  (SourcePlaceSelection) and the finiteness of its bad index;
* the Definition 3.1(b) reduction cards S1280ReductionCards l
  (BadPlaceReductionCards) at the actual bad fibre, from the proved
  split-multiplicative reduction of the concrete curve at that place;
* the Definition 3.1(a)(b)(e) place partition S1280PlacePartition l and the
  Definition 3.1(b) reduction clause S1280ReductionClause l through the
  existing assemblies toSourcePlacePartition / toSourceReductionClause.

The exact boundary is also stated:

* the first field of SourceDefinition31Data l that the tree actual data does
  not determine is torsion : SourceTorsionClause l (D5: rank-two l-torsion
  basis and the SL_2 large-image statement are open cards);
* S1280SourceData_of_remaining shows that the four constructed components are
  literally the arithmetic/selectedPlaces/badPlaces/reduction fields of the
  assembled contract, the remaining inputs being exactly the D5/D6/D7/D8
  clause values and the D9 compatibility pairs;
* Clause (c) coprimality: the bad residue characteristic is 5, so the
  residue-characteristic half of BadPlaceQParameterCards for this selection
  holds exactly when l.value != 5; at l = 5 the clause-(c) card is refuted
  (S1280_clauseC_refuted_at_five).  This is the paper condition: l is prime to
  the residue characteristics of the elements of V^bad_mod (IUT I, Def. 3.1(c)).

Boundary kept explicit (not claimed): the real qParameter of the assembled
reduction clause is the completed-DVR proxy badPlaceQProxy; its identification
with the Tate q-parameter of the curve is the recorded D4 boundary.  No
torsion, orbicurve, section, cusp or compatibility data is invented.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 1000000

noncomputable section

namespace LeanFormal.IUT.XiFPaper.S1280SourceDefinition31Actual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.Theorem311Source

local instance s1280GaussianIrreducible :
    Fact (Irreducible (Polynomial.X ^ 2 - Polynomial.C (-1) : Polynomial ℚ)) :=
  ⟨gaussianPolynomial_irreducible⟩

local instance s1280FivePrime : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩

/-! ## 1. The actual arithmetic input and place -/

/-- The actual Definition 3.1 arithmetic input: the concrete Gaussian data with
the base-changed split multiplicative curve. -/
abbrev S1280Arithmetic (l : PrimeGeFive) := concreteGaussianInitialThetaArithmeticData l

/-- The actual finite place above 5 (Mathlib lying-over, concreteFivePlace
transported to Q(i)). -/
abbrev S1280Place (l : PrimeGeFive) :
    NumberField.FinitePlace (S1280Arithmetic l).Fmod :=
  concreteGaussianFivePlace

/-- The residue characteristic of the actual place is 5 (proved in
Example36GaussianSplitPlaceArithmetic). -/
theorem S1280Place_residueCharacteristic (l : PrimeGeFive) :
    NumberFieldFinitePlace.residueCharacteristic (S1280Place l) = 5 :=
  LeanFormal.IUT.IUTII.Frobenioid.Example36.concreteGaussianFivePlace_residueCharacteristic

/-- Clause (b) source condition on the actual place: its residue characteristic
is odd. -/
theorem S1280Place_odd (l : PrimeGeFive) :
    Odd (NumberFieldFinitePlace.residueCharacteristic (S1280Place l)) := by
  rw [S1280Place_residueCharacteristic]
  decide

/-! ## 2. The actual source place selection (Definition 3.1(b)) -/

/-- The bad moduli set of Definition 3.1(b): the singleton {place above 5}, an
actual nonempty set of finite places of odd residue characteristic. -/
def S1280Selection (l : PrimeGeFive) : SourcePlaceSelection (S1280Arithmetic l) :=
  SourcePlaceSelection.singleton (S1280Arithmetic l) (S1280Place l) (S1280Place_odd l)

@[simp] theorem S1280Selection_V_mod_bad (l : PrimeGeFive) :
    (S1280Selection l).V_mod_bad = {concreteGaussianFivePlace} := by
  rw [S1280Selection, SourcePlaceSelection.singleton_V_mod_bad]
  rfl

theorem S1280Selection_V_mod_bad_nonempty (l : PrimeGeFive) :
    (S1280Selection l).V_mod_bad.Nonempty :=
  (S1280Selection l).V_mod_bad_nonempty

theorem S1280Selection_odd (l : PrimeGeFive)
    (p : NumberField.FinitePlace (S1280Arithmetic l).Fmod)
    (hp : p ∈ (S1280Selection l).V_mod_bad) :
    Odd (NumberFieldFinitePlace.residueCharacteristic p) :=
  (S1280Selection l).V_mod_bad_odd_residue_characteristic p hp

/-- The bad moduli set of the actual selection is finite: it is a singleton. -/
theorem S1280Selection_V_mod_bad_finite (l : PrimeGeFive) :
    (S1280Selection l).V_mod_bad.Finite := by
  rw [S1280Selection_V_mod_bad]
  exact Set.finite_singleton _

/-- Finiteness of the bad moduli index (Bad P is the subtype of V^bad_mod). -/
@[reducible] noncomputable def S1280BadFintype (l : PrimeGeFive) :
    Fintype (Bad (S1280Selection l)) :=
  (S1280Selection_V_mod_bad_finite l).fintype

instance S1280BadFintypeInstance (l : PrimeGeFive) :
    Fintype (Bad (S1280Selection l)) :=
  S1280BadFintype l

/-- The bad index has at most one element: the bad moduli fibre is a single
moduli place. -/
theorem S1280Bad_subsingleton (l : PrimeGeFive) :
    Subsingleton (Bad (S1280Selection l)) := by
  constructor
  intro a b
  obtain ⟨a1, ha1⟩ := a
  obtain ⟨b1, hb1⟩ := b
  have ha : a1 = concreteGaussianFivePlace := by
    have h := ha1
    rw [S1280Selection_V_mod_bad] at h
    exact Set.eq_of_mem_singleton h
  have hb : b1 = concreteGaussianFivePlace := by
    have h := hb1
    rw [S1280Selection_V_mod_bad] at h
    exact Set.eq_of_mem_singleton h
  exact Subtype.ext (ha.trans hb.symm)

/-! ## 3. The actual Definition 3.1(b) reduction cards -/

/-- For the identity tower Fmod = F = K = Q(i) of the concrete data, finite
place restriction is the identity: comap of a finite place of Q(i) to Q(i) is
that place itself. -/
theorem S1280_comap_eq_self (l : PrimeGeFive)
    (w : NumberField.FinitePlace (S1280Arithmetic l).F) :
    NumberFieldFinitePlace.comap (k := (S1280Arithmetic l).Fmod) w = w := by
  apply NumberField.FinitePlace.maximalIdeal_injective
  apply IsDedekindDomain.HeightOneSpectrum.ext
  rw [NumberFieldFinitePlace.comap_maximalIdeal]
  exact Ideal.comap_id _

/-- The actual bad fibre: every finite place of F = Q(i) restricting to the
selected bad moduli place is the selected place itself. -/
theorem S1280_bad_fibre_eq (l : PrimeGeFive)
    (w : NumberField.FinitePlace (S1280Arithmetic l).F)
    (hw : NumberFieldFinitePlace.comap (k := (S1280Arithmetic l).Fmod) w ∈
      (S1280Selection l).V_mod_bad) :
    w = concreteGaussianFivePlace := by
  have hbad := hw
  rw [S1280Selection_V_mod_bad] at hbad
  have hcomap : NumberFieldFinitePlace.comap (k := (S1280Arithmetic l).Fmod) w =
      concreteGaussianFivePlace := by
    exact Set.eq_of_mem_singleton hbad
  rw [← hcomap]
  exact (S1280_comap_eq_self l w).symm

/-- The actual reduction cards.  Stable, multiplicative, and split
multiplicative reduction hold at the actual bad fibre, because the concrete
base-changed curve has split multiplicative reduction at the place above 5 and
every bad-fibre place is that place. -/
theorem S1280ReductionCards (l : PrimeGeFive) :
    BadPlaceReductionCards (S1280Selection l) where
  stableReduction := fun w hw => by
    rw [S1280_bad_fibre_eq l w hw]
    exact Or.inr (concreteGaussianFivePlace_hasMultiplicativeReduction l)
  multiplicativeReduction := fun w hw => by
    rw [S1280_bad_fibre_eq l w hw]
    exact concreteGaussianFivePlace_hasMultiplicativeReduction l
  splitMultiplicativeReduction := fun w hw => by
    rw [S1280_bad_fibre_eq l w hw]
    exact concreteGaussianFivePlace_hasSplitMultiplicativeReduction l

theorem S1280ReductionCards_split (l : PrimeGeFive)
    (w : NumberField.FinitePlace (S1280Arithmetic l).F)
    (hw : NumberFieldFinitePlace.comap (k := (S1280Arithmetic l).Fmod) w ∈
      (S1280Selection l).V_mod_bad) :
    (S1280Arithmetic l).curve.HasSplitMultiplicativeReductionAt w :=
  (S1280ReductionCards l).splitMultiplicativeReduction w hw

/-! ## 4. The actual place partition and the actual reduction clause -/

/-- Definition 3.1(a)(b)(e): the actual source place partition. -/
noncomputable def S1280PlacePartition (l : PrimeGeFive) :
    SourcePlacePartition (Selected (S1280Selection l)) (Bad (S1280Selection l)) :=
  toSourcePlacePartition (S1280Selection l)

/-- Definition 3.1(b)(c)-assembled reduction clause: the curve has stable /
multiplicative / split multiplicative reduction at every bad place, and the
real q-parameter is the completed-DVR proxy badPlaceQProxy. -/
noncomputable def S1280ReductionClause (l : PrimeGeFive) :
    SourceReductionClause (Selected (S1280Selection l)) (Bad (S1280Selection l)) :=
  toSourceReductionClause (S1280Selection l) (S1280ReductionCards l)

@[simp] theorem S1280PlacePartition_badIncluded (l : PrimeGeFive)
    (b : Bad (S1280Selection l)) :
    (S1280PlacePartition l).badIncluded b = badIncluded (S1280Selection l) b :=
  rfl

@[simp] theorem S1280PlacePartition_badLabel (l : PrimeGeFive)
    (b : Bad (S1280Selection l)) :
    (S1280PlacePartition l).badLabel b =
      NumberFieldFinitePlace.residueCharacteristic b.1 :=
  rfl

@[simp] theorem S1280PlacePartition_badLabel_compatible (l : PrimeGeFive)
    (b : Bad (S1280Selection l)) :
    (S1280PlacePartition l).selectedLabel
        ((S1280PlacePartition l).badIncluded b) =
      (S1280PlacePartition l).badLabel b :=
  (S1280PlacePartition l).badLabel_compatible b

@[simp] theorem S1280ReductionClause_qParameter (l : PrimeGeFive) :
    (S1280ReductionClause l).qParameter = badPlaceQProxy (S1280Selection l) :=
  rfl

theorem S1280ReductionClause_stable (l : PrimeGeFive)
    (b : Bad (S1280Selection l)) :
    (S1280ReductionClause l).stableReduction b :=
  (S1280ReductionClause l).stableReduction_proved b

theorem S1280ReductionClause_multiplicative (l : PrimeGeFive)
    (b : Bad (S1280Selection l)) :
    (S1280ReductionClause l).multiplicativeReduction b :=
  (S1280ReductionClause l).multiplicativeReduction_proved b

theorem S1280ReductionClause_split (l : PrimeGeFive)
    (b : Bad (S1280Selection l)) :
    (S1280ReductionClause l).splitMultiplicativeReduction b :=
  (S1280ReductionClause l).splitMultiplicativeReduction_proved b

theorem S1280ReductionClause_qParameter_nonzero (l : PrimeGeFive)
    (b : Bad (S1280Selection l)) :
    (S1280ReductionClause l).qParameter b ≠ 0 :=
  (S1280ReductionClause l).qParameter_nonzero b

theorem S1280ReductionClause_qParameter_contracting (l : PrimeGeFive)
    (b : Bad (S1280Selection l)) :
    ‖(S1280ReductionClause l).qParameter b‖ < 1 :=
  (S1280ReductionClause l).qParameter_contracting b

theorem S1280ReductionClause_qParameter_ne_one (l : PrimeGeFive)
    (b : Bad (S1280Selection l)) :
    (S1280ReductionClause l).qParameter b ≠ 1 :=
  (S1280ReductionClause l).qParameter_reduction_compatibility b
    ((S1280ReductionClause l).stableReduction_proved b)

/-- The actual numeric value of the assembled q-parameter: (1/5) ^ order,
where order is the order of the completed-DVR q-candidate at the bad place.
This is an actual computation, not a normalized or constant q. -/
theorem S1280ReductionClause_qParameter_eq (l : PrimeGeFive)
    (b : Bad (S1280Selection l)) :
    (S1280ReductionClause l).qParameter b =
      ((5 : ℝ)⁻¹) ^ (badPlaceQCandidate (S1280Selection l) b).order := by
  rw [S1280ReductionClause_qParameter]
  obtain ⟨b1, hb1⟩ := b
  unfold badPlaceQProxy
  set n := (badPlaceQCandidate (S1280Selection l) ⟨b1, hb1⟩).order
  have hb : b1 = concreteGaussianFivePlace := by
    have hmem := hb1
    rw [S1280Selection_V_mod_bad] at hmem
    exact Set.eq_of_mem_singleton hmem
  change ((NumberFieldFinitePlace.residueCharacteristic b1 : Nat) : ℝ)⁻¹ ^ n =
    ((5 : ℝ)⁻¹) ^ n
  rw [hb, S1280Place_residueCharacteristic]
  norm_num

/-! ## 5. The exact remaining fields of SourceDefinition31Data -/

/-- The first field of SourceDefinition31Data l that the actual data of this
file does not determine: the D5 torsion clause.  Its content (rank-two
l-torsion basis, SL_2 large-image containment, kernel-field identification) is
the open SourceTorsionDatum card of the tree. -/
abbrev S1280FirstMissingField (l : PrimeGeFive) : Type 1 :=
  SourceTorsionClause.{0, 0, 0} l

/-- Every SourceDefinition31Data l over the actual arithmetic data has an
S1280FirstMissingField: the field is a genuine projection, not a new
assumption. -/
theorem S1280FirstMissingField_of_sourceData {l : PrimeGeFive}
    (S : SourceDefinition31Data.{0} l) : Nonempty (S1280FirstMissingField l) :=
  ⟨S.torsion⟩

/-- The remaining clause values of Definition 3.1 over the actual data, as one
exact obligation type: D5 torsion, D6 orbicurve, D7 sections, D8 cusp. -/
structure S1280RemainingClauses (l : PrimeGeFive) where
  torsion : SourceTorsionClause.{0, 0, 0} l
  orbicurve : SourceOrbicurveClause.{0, 0, 0}
  sections : SourceSectionClause.{0, 0, 0}
  cusp : SourceCuspClause

/-- Conditional assembly.  Given exactly the four remaining source clauses and
the five D9 compatibility (Prop, proof) pairs, the Definition 3.1 data is
assembled by the existing entry d11EntryData; its arithmetic, selected, bad,
and reduction fields are the actual ones constructed above. -/
noncomputable def S1280SourceData_of_remaining (l : PrimeGeFive)
    (R : S1280RemainingClauses l)
    (redCompat : Prop) (hredCompat : redCompat)
    (torCompat : Prop) (htorCompat : torCompat)
    (orbCompat : Prop) (horbCompat : orbCompat)
    (secCompat : Prop) (hsecCompat : secCompat)
    (cusCompat : Prop) (hcusCompat : cusCompat) :
    SourceDefinition31Data l :=
  Definition31PlacePartition.d11EntryData (S1280Selection l)
    (S1280ReductionCards l) R.torsion R.orbicurve R.sections R.cusp
    redCompat hredCompat torCompat htorCompat orbCompat horbCompat
    secCompat hsecCompat cusCompat hcusCompat

@[simp] theorem S1280SourceData_of_remaining_arithmetic (l : PrimeGeFive)
    (R : S1280RemainingClauses l)
    (redCompat : Prop) (hredCompat : redCompat)
    (torCompat : Prop) (htorCompat : torCompat)
    (orbCompat : Prop) (horbCompat : orbCompat)
    (secCompat : Prop) (hsecCompat : secCompat)
    (cusCompat : Prop) (hcusCompat : cusCompat) :
    (S1280SourceData_of_remaining l R redCompat hredCompat torCompat htorCompat
      orbCompat horbCompat secCompat hsecCompat cusCompat hcusCompat).arithmetic =
        S1280Arithmetic l :=
  rfl

@[simp] theorem S1280SourceData_of_remaining_selectedPlaces (l : PrimeGeFive)
    (R : S1280RemainingClauses l)
    (redCompat : Prop) (hredCompat : redCompat)
    (torCompat : Prop) (htorCompat : torCompat)
    (orbCompat : Prop) (horbCompat : orbCompat)
    (secCompat : Prop) (hsecCompat : secCompat)
    (cusCompat : Prop) (hcusCompat : cusCompat) :
    (S1280SourceData_of_remaining l R redCompat hredCompat torCompat htorCompat
      orbCompat horbCompat secCompat hsecCompat cusCompat hcusCompat).selectedPlaces =
        Selected (S1280Selection l) :=
  rfl

@[simp] theorem S1280SourceData_of_remaining_badPlaces (l : PrimeGeFive)
    (R : S1280RemainingClauses l)
    (redCompat : Prop) (hredCompat : redCompat)
    (torCompat : Prop) (htorCompat : torCompat)
    (orbCompat : Prop) (horbCompat : orbCompat)
    (secCompat : Prop) (hsecCompat : secCompat)
    (cusCompat : Prop) (hcusCompat : cusCompat) :
    (S1280SourceData_of_remaining l R redCompat hredCompat torCompat htorCompat
      orbCompat horbCompat secCompat hsecCompat cusCompat hcusCompat).badPlaces =
        Bad (S1280Selection l) :=
  rfl

@[simp] theorem S1280SourceData_of_remaining_torsion (l : PrimeGeFive)
    (R : S1280RemainingClauses l)
    (redCompat : Prop) (hredCompat : redCompat)
    (torCompat : Prop) (htorCompat : torCompat)
    (orbCompat : Prop) (horbCompat : orbCompat)
    (secCompat : Prop) (hsecCompat : secCompat)
    (cusCompat : Prop) (hcusCompat : cusCompat) :
    (S1280SourceData_of_remaining l R redCompat hredCompat torCompat htorCompat
      orbCompat horbCompat secCompat hsecCompat cusCompat hcusCompat).torsion =
        R.torsion :=
  rfl

/-- Consumer-chain spec: the assembled Definition 3.1 data feeds the Theorem
3.11 input chain with the actual arithmetic input. -/
theorem S1280_assembled_initialThetaInput_arithmetic (l : PrimeGeFive)
    (R : S1280RemainingClauses l)
    (redCompat : Prop) (hredCompat : redCompat)
    (torCompat : Prop) (htorCompat : torCompat)
    (orbCompat : Prop) (horbCompat : orbCompat)
    (secCompat : Prop) (hsecCompat : secCompat)
    (cusCompat : Prop) (hcusCompat : cusCompat) :
    (S1280SourceData_of_remaining l R redCompat hredCompat torCompat htorCompat
      orbCompat horbCompat secCompat hsecCompat cusCompat hcusCompat).toInitialThetaInput.arithmetic =
        S1280Arithmetic l :=
  rfl

/-- Consumer-chain spec: the assembled Definition 3.1 data feeds the Theorem
3.11 input chain with the actual bad-place index Bad (S1280Selection l). -/
theorem S1280_assembled_initialThetaInput_badPlaces (l : PrimeGeFive)
    (R : S1280RemainingClauses l)
    (redCompat : Prop) (hredCompat : redCompat)
    (torCompat : Prop) (htorCompat : torCompat)
    (orbCompat : Prop) (horbCompat : orbCompat)
    (secCompat : Prop) (hsecCompat : secCompat)
    (cusCompat : Prop) (hcusCompat : cusCompat) :
    (S1280SourceData_of_remaining l R redCompat hredCompat torCompat htorCompat
      orbCompat horbCompat secCompat hsecCompat cusCompat hcusCompat).toInitialThetaInput.badPlaces =
        Bad (S1280Selection l) :=
  rfl

@[simp] theorem S1280SourceData_of_remaining_reduction (l : PrimeGeFive)
    (R : S1280RemainingClauses l)
    (redCompat : Prop) (hredCompat : redCompat)
    (torCompat : Prop) (htorCompat : torCompat)
    (orbCompat : Prop) (horbCompat : orbCompat)
    (secCompat : Prop) (hsecCompat : secCompat)
    (cusCompat : Prop) (hcusCompat : cusCompat) :
    (S1280SourceData_of_remaining l R redCompat hredCompat torCompat htorCompat
      orbCompat horbCompat secCompat hsecCompat cusCompat hcusCompat).reduction =
        S1280ReductionClause l :=
  rfl

/-! ## 6. Clause (c) coprimality at the actual place -/

/-- The concrete l = 5 label. -/
def S1280Five : PrimeGeFive where
  value := 5
  prime := Nat.prime_five
  ge_five := le_rfl

@[simp] theorem S1280Five_value : S1280Five.value = 5 := rfl

/-- The residue-characteristic half of Clause (c) holds for the actual
selection exactly when l != 5: the bad residue characteristic is 5, and the
paper requires l prime to it. -/
theorem S1280_badResidueCharacteristic_coprime_iff (l : PrimeGeFive) :
    Nat.Coprime (NumberFieldFinitePlace.residueCharacteristic (S1280Place l))
        l.value ↔ l.value ≠ 5 := by
  rw [S1280Place_residueCharacteristic]
  constructor
  · intro h h5
    rw [h5] at h
    exact absurd h (by decide)
  · intro h5
    rw [Nat.coprime_primes Nat.prime_five l.prime]
    intro h
    exact h5 h.symm

/-- Clause (c) is refuted at l = 5.  For the actual selection at the place
above 5, the clause (c) coprimality card BadPlaceQParameterCards has no
inhabitant when l = 5: its residue-characteristic field would require
Nat.Coprime 5 5.  A source-faithful Definition 3.1(b) selection for l = 5
therefore cannot use this bad moduli place. -/
theorem S1280_clauseC_refuted_at_five :
    ¬ Nonempty (BadPlaceQParameterCards (S1280Selection S1280Five)) := by
  rintro ⟨C⟩
  rcases (S1280Selection S1280Five).V_mod_bad_nonempty with ⟨p, hp⟩
  have hp_eq : p = concreteGaussianFivePlace := by
    have hmem := hp
    rw [S1280Selection_V_mod_bad] at hmem
    exact Set.eq_of_mem_singleton hmem
  have hcop := C.badResidueCharacteristic_primeToL p hp
  rw [hp_eq, S1280Place_residueCharacteristic, S1280Five_value] at hcop
  exact absurd hcop (by decide)

/-! ## 7. Axiom footprint -/

#print axioms S1280Selection
#print axioms S1280ReductionCards
#print axioms S1280PlacePartition
#print axioms S1280ReductionClause
#print axioms S1280ReductionClause_qParameter_eq
#print axioms S1280SourceData_of_remaining
#print axioms S1280_assembled_initialThetaInput_arithmetic
#print axioms S1280_assembled_initialThetaInput_badPlaces
#print axioms S1280_clauseC_refuted_at_five

end LeanFormal.IUT.XiFPaper.S1280SourceDefinition31Actual

end
