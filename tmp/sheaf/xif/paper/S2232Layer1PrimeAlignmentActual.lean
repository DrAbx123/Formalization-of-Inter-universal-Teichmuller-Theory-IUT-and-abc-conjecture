import tmp.sheaf.xif.paper.S2195Layer1InstanceActual
import tmp.sheaf.xif.paper.S1730BadSetWithoutLActual
import LeanFormal.IUT.ABCBridge.Geometry.FinitePlaceRelativeCommonPrime
import Mathlib.RingTheory.Ideal.Int

/-!
# S2232: layer (1) prime alignment, actual prime data and exact paper conditions

S2195 reduced the full layer (1) split package at the actual (T, b) to the
three arithmetic inputs

* S2135PrimeAlignmentRequired T b (qVFamTensorP T b in primeStrip 2 7),
* S2040QVPlaceDegreeOneRequired T b (the rational residue degree is one),
* S2040QVPlaceUnramifiedRequired T b (the local ramification index is one),

and constructed the aligned package from them.  The source clauses of
Definition 3.1 supply neither the prime-strip membership nor the two local
degree conditions:

* Definition 3.1(b) gives only that a bad moduli place has odd residue
  characteristic; Clause (b) adds the coprimality of that residue
  characteristic with l, together with the reduction and q-parameter data.
  None of these fields bounds the rational prime from above, and none is a
  degree-one or unramifiedness condition at the chosen lying-over place;
* the source section V -> V_mod is a section of restriction, not a
  degree-one or unramified local extension;
* IUT III Theorem 3.11/Corollary 3.12 is stated for arbitrary initial
  Theta-data, so the numeric strip 2..7 is not a paper hypothesis there.

This file does not fake the missing input.  It records and proves:

1. the actual primality data: qVFamTensorP T b is prime, is the rational
   prime under the bad place, equals the residue characteristic of the actual
   F-place and of b, is odd, and is prime to l;
2. the exact strip form: membership in primeStrip 2 7 is equivalent to
   qVFamTensorP T b <= 7 and to the explicit disjunction
   = 2 or = 3 or = 5 or = 7;
3. the exact paper arithmetic conditions, named S2232PaperArithmeticConditions,
   and the equivalence "the aligned split package exists iff these three
   conditions hold";
4. a source-adequacy audit: oddness plus coprimality to l do not imply the
   strip bound (there is an odd prime above 7 coprime to l);
5. actual concrete strip evidence in the paper's S1667 model: every S1730 bad
   moduli place has residue characteristic in {3,5,7} contained in primeStrip 2 7.
   This is evidence for the concrete paper bad set, not a proof of
   qVFamTensorP T b in primeStrip 2 7 for an arbitrary T: the native source
   datum over that arithmetic root is a separate open field (cf. S1519).

No proof placeholders, extra assumptions, True/PUnit slots, arbitrary
inhabitants or Nonempty gates are used. -/

noncomputable section
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 2000000

namespace LeanFormal.IUT.XiFPaper.S2232Layer1PrimeAlignmentActual

open LeanFormal.IUT
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.S2040QVPlaceSplitActual
open LeanFormal.IUT.XiFPaper.S2135Layer1SplitActual
open LeanFormal.IUT.XiFPaper.S2195Layer1InstanceActual
open LeanFormal.IUT.XiFPaper.S1712OddResidueActual
open LeanFormal.IUT.XiFPaper.S1717PlaceSevenD5Actual
open LeanFormal.IUT.XiFPaper.S1729FullBadPlaceActual
open LeanFormal.IUT.XiFPaper.S1730BadSetWithoutLActual

universe u

variable {l : PrimeGeFive} (T : SourceNativeInitialThetaData.{0} l)
  (b : Bad (nativePlaceSelection T))

/-! ## 1. Actual primality and residue-characteristic alignment -/

/-- For a rational finite place, the residue characteristic is the height-one
prime generator.  This is the arithmetic bridge between the
Rat.HeightOneSpectrum.primesEquiv value used by completionRationalPrime and
the source-level residueCharacteristic. -/
theorem s2232_rational_residueCharacteristic_eq_natGenerator
    (q : NumberField.FinitePlace ℚ) :
    residueCharacteristic q = Rat.HeightOneSpectrum.natGenerator q.maximalIdeal := by
  let e : NumberField.RingOfIntegers ℚ ≃+* ℤ := Rat.IsIntegralClosure.intEquiv _
  have halg : (e.symm : ℤ →+* NumberField.RingOfIntegers ℚ) =
      algebraMap ℤ (NumberField.RingOfIntegers ℚ) :=
    RingHom.ext_int _ _
  unfold residueCharacteristic
  rw [Ideal.ringChar_quot]
  have hunder_map :
      Ideal.under ℤ q.maximalIdeal.asIdeal = Ideal.map e q.maximalIdeal.asIdeal := by
    ext x
    rw [Ideal.mem_comap]
    constructor
    · intro hx
      rw [Ideal.mem_map_iff_of_surjective _ e.surjective]
      refine ⟨algebraMap ℤ (NumberField.RingOfIntegers ℚ) x, hx, ?_⟩
      rw [← halg]
      exact e.apply_symm_apply x
    · intro hx
      rw [Ideal.mem_map_iff_of_surjective _ e.surjective] at hx
      obtain ⟨y, hy, rfl⟩ := hx
      have h : (e.symm : ℤ →+* NumberField.RingOfIntegers ℚ) (e y) = y :=
        e.symm_apply_apply y
      rw [← halg]
      change (e.symm : ℤ →+* NumberField.RingOfIntegers ℚ) (e y) ∈
        q.maximalIdeal.asIdeal
      rw [h]
      exact hy
  have hunder : Ideal.under ℤ q.maximalIdeal.asIdeal =
      Ideal.span {(Rat.HeightOneSpectrum.natGenerator q.maximalIdeal : ℤ)} := by
    rw [hunder_map, ← Rat.HeightOneSpectrum.span_natGenerator (v := q.maximalIdeal)]
  rw [hunder, Ideal.absNorm_span_singleton]
  simp

/-- The rational prime of a finite place is its residue characteristic. -/
theorem s2232_completionRationalPrime_val_eq_residueCharacteristic
    {K : Type u} [Field K] [NumberField K]
    (place : NumberField.FinitePlace K) :
    (completionRationalPrime place).val = residueCharacteristic place := by
  change Rat.HeightOneSpectrum.natGenerator (comap (k := ℚ) place).maximalIdeal =
    residueCharacteristic place
  rw [← s2232_rational_residueCharacteristic_eq_natGenerator
    (comap (k := ℚ) place)]
  exact residueCharacteristic_comap (k := ℚ) place

/-- The tensor rational prime is the residue characteristic of the actual
F-place. -/
theorem s2232_qVFamTensorP_eq_residueCharacteristic :
    qVFamTensorP T b = residueCharacteristic (qVFamTensorPlace T b) := by
  unfold qVFamTensorP
  exact s2232_completionRationalPrime_val_eq_residueCharacteristic
    (qVFamTensorPlace T b)

/-- The tensor rational prime is the residue characteristic of the bad moduli
place b itself. -/
theorem s2232_qVFamTensorP_eq_b_residueCharacteristic :
    qVFamTensorP T b = residueCharacteristic b.1 := by
  rw [s2232_qVFamTensorP_eq_residueCharacteristic T b]
  rw [← residueCharacteristic_comap (k := T.arithmetic.Fmod) (K := T.arithmetic.F)
    (qVFamTensorPlace T b)]
  rw [(nativeBadLift T).lift_comap b]

/-- qVFamTensorP T b is prime. -/
theorem s2232_qVFamTensorP_prime : Nat.Prime (qVFamTensorP T b) :=
  (qVFamTensorPFact T b).out

/-- qVFamTensorP T b is at least two. -/
theorem s2232_qVFamTensorP_two_le : 2 ≤ qVFamTensorP T b :=
  (s2232_qVFamTensorP_prime T b).two_le

/-- The source's oddness condition transfers to qVFamTensorP T b. -/
theorem s2232_qVFamTensorP_odd : Odd (qVFamTensorP T b) := by
  rw [s2232_qVFamTensorP_eq_b_residueCharacteristic T b]
  exact (nativePlaceSelection T).V_mod_bad_odd_residue_characteristic b.1 b.2

/-- The source's Clause (b) coprimality condition transfers to qVFamTensorP T b. -/
theorem s2232_qVFamTensorP_coprime_l :
    Nat.Coprime (qVFamTensorP T b) l.value := by
  rw [s2232_qVFamTensorP_eq_b_residueCharacteristic T b]
  have h := T.clauseB.residue_characteristic_prime_to_l
    ((nativeBadLift T).lift b) (by
      rw [(nativeBadLift T).lift_comap b]
      exact b.2)
  rw [(nativeBadLift T).lift_comap b] at h
  exact Nat.coprime_comm.mp h

/-! ## 2. The exact strip form -/

/-- The numeric prime strip is exactly the upper bound <= 7 for the actual
prime qVFamTensorP T b. -/
theorem s2232_mem_primeStrip_iff_le_seven :
    qVFamTensorP T b ∈ primeStrip 2 7 ↔ qVFamTensorP T b ≤ 7 := by
  rw [mem_primeStrip_iff]
  constructor
  · rintro ⟨-, hle, -⟩
    exact hle
  · intro hle
    exact ⟨s2232_qVFamTensorP_two_le T b, hle, s2232_qVFamTensorP_prime T b⟩

/-- The exact numeric form of the strip: {2,3,5,7}. -/
theorem s2232_mem_primeStrip_iff_eq :
    qVFamTensorP T b ∈ primeStrip 2 7 ↔
      qVFamTensorP T b = 2 ∨ qVFamTensorP T b = 3 ∨
        qVFamTensorP T b = 5 ∨ qVFamTensorP T b = 7 := by
  constructor
  · intro hmem
    have hle := (s2232_mem_primeStrip_iff_le_seven T b).mp hmem
    have hge := s2232_qVFamTensorP_two_le T b
    have hp := s2232_qVFamTensorP_prime T b
    set p := qVFamTensorP T b with hpdef
    interval_cases p
    · simp
    · simp
    · norm_num at hp
    · simp
    · norm_num at hp
    · simp
  · rintro (h2 | h3 | h5 | h7)
    · rw [h2]
      exact mem_primeStrip_iff.mpr ⟨by norm_num, by norm_num, Nat.prime_two⟩
    · rw [h3]
      exact mem_primeStrip_iff.mpr ⟨by norm_num, by norm_num, Nat.prime_three⟩
    · rw [h5]
      exact mem_primeStrip_iff.mpr ⟨by norm_num, by norm_num, Nat.prime_five⟩
    · rw [h7]
      exact mem_primeStrip_iff.mpr ⟨by norm_num, by norm_num, Nat.prime_seven⟩

/-! ## 3. The exact paper arithmetic conditions -/

/-- The exact paper arithmetic condition missing for the prime alignment. -/
def S2232PrimeStripRequired : Prop :=
  qVFamTensorP T b ∈ primeStrip 2 7

/-- The same condition in upper-bound form. -/
def S2232PrimeUpperBoundRequired : Prop :=
  qVFamTensorP T b ≤ 7

/-- The exact residue-degree condition: f = 1 at the actual F-place. -/
def S2232ResidueDegreeOneRequired : Prop :=
  relativeResidueDegree (k := ℚ) (qVFamTensorPlace T b) = 1

/-- The exact ramification condition: e = 1 at the actual F-place. -/
def S2232RamificationIndexOneRequired : Prop :=
  relativeRamificationIndex (k := ℚ) (qVFamTensorPlace T b) = 1

/-- The named paper arithmetic conditions whose conjunction is exactly the
layer (1) split package. -/
structure S2232PaperArithmeticConditions : Prop where
  prime_strip : S2232PrimeStripRequired T b
  residue_degree_one : S2232ResidueDegreeOneRequired T b
  ramification_index_one : S2232RamificationIndexOneRequired T b

/-- The new name is definitionally the S2135 missing prime alignment. -/
theorem s2232_primeStripRequired_iff_S2135 :
    S2232PrimeStripRequired T b ↔ S2135PrimeAlignmentRequired T b :=
  Iff.rfl

/-- The strip condition is exactly the upper bound. -/
theorem s2232_primeUpperBound_iff_primeStrip :
    S2232PrimeUpperBoundRequired T b ↔ S2232PrimeStripRequired T b := by
  unfold S2232PrimeUpperBoundRequired S2232PrimeStripRequired
  exact (s2232_mem_primeStrip_iff_le_seven T b).symm

/-- The named residue-degree condition is definitionally the S2040 one. -/
theorem s2232_residueDegreeOne_iff_S2040 :
    S2232ResidueDegreeOneRequired T b ↔ S2040QVPlaceDegreeOneRequired T b := by
  unfold S2232ResidueDegreeOneRequired S2040QVPlaceDegreeOneRequired
  rw [s2195_qVFamTensorRationalDegree_eq_relativeResidueDegree]

/-- The named ramification condition is equivalent to the S2040 one. -/
theorem s2232_ramificationIndexOne_iff_S2040 :
    S2232RamificationIndexOneRequired T b ↔ S2040QVPlaceUnramifiedRequired T b := by
  unfold S2232RamificationIndexOneRequired S2040QVPlaceUnramifiedRequired
  rw [s2195_localRamificationIndex_eq_relativeRamificationIndex]

/-- The exact first missing input, in one equivalence.  Once the actual
primality data are aligned, the full aligned split package exists exactly when
the three paper arithmetic conditions hold.  No other input is missing. -/
theorem s2232_paperArithmeticConditions_iff_package :
    S2232PaperArithmeticConditions T b ↔
      Nonempty (S2135PrimeAlignedSplitPackage T b) := by
  constructor
  · rintro ⟨hstrip, hdeg, hram⟩
    have hmem : qVFamTensorP T b ∈ primeStrip 2 7 := hstrip
    have hdeg' : S2040QVPlaceDegreeOneRequired T b :=
      (s2232_residueDegreeOne_iff_S2040 T b).mpr hdeg
    have hram' : S2040QVPlaceUnramifiedRequired T b :=
      (s2232_ramificationIndexOne_iff_S2040 T b).mp hram
    exact ⟨s2195_primeAlignedSplitPackage T b
      ⟨qVFamTensorP T b, hmem⟩ rfl hdeg' hram'⟩
  · rintro ⟨P⟩
    exact ⟨s2135_aligned_package_prime_mem T b P,
      (s2232_residueDegreeOne_iff_S2040 T b).mp P.degree_one,
      (s2232_ramificationIndexOne_iff_S2040 T b).mpr P.unramified⟩

/-- The aligned split package from the named paper conditions. -/
theorem s2232_package_of_paperArithmeticConditions
    (h : S2232PaperArithmeticConditions T b) :
    Nonempty (S2135PrimeAlignedSplitPackage T b) :=
  (s2232_paperArithmeticConditions_iff_package T b).mp h

/-- Conversely, any aligned split package yields exactly the named paper
conditions. -/
theorem s2232_paperArithmeticConditions_of_package
    (P : S2135PrimeAlignedSplitPackage T b) :
    S2232PaperArithmeticConditions T b :=
  (s2232_paperArithmeticConditions_iff_package T b).mpr ⟨P⟩

/-! ## 4. Source-adequacy audit -/

/-- The source's oddness condition alone does not bound the rational prime:
for every l >= 5 there is an odd prime outside the strip that is prime to l.
This is the precise sense in which Definition 3.1(b) and Clause (b) cannot
imply the strip membership. -/
theorem s2232_source_constraints_do_not_force_strip (l : PrimeGeFive) :
    ∃ p : ℕ, Nat.Prime p ∧ Odd p ∧ Nat.Coprime p l.value ∧
      p ∉ primeStrip 2 7 := by
  obtain ⟨p, hpge, hpprime⟩ := Nat.exists_infinite_primes (l.value + 8)
  have hpgt7 : 7 < p := by
    have := l.ge_five
    omega
  have hpgtl : l.value < p := by
    omega
  refine ⟨p, hpprime, ?_, ?_, ?_⟩
  · exact hpprime.odd_of_ne_two (by omega)
  · rw [hpprime.coprime_iff_not_dvd]
    exact Nat.not_dvd_of_pos_of_lt (Nat.Prime.pos l.prime) hpgtl
  · rw [mem_primeStrip_iff]
    rintro ⟨-, hle, -⟩
    omega

/-! ## 5. Actual concrete strip evidence in the paper's S1667 model -/

/-- Every bad moduli place of the concrete S1730 selection is one of the
actual rational places 3, 5, 7, hence has residue characteristic in the paper
strip.  This is genuine concrete evidence for the paper's bad-prime strip; it
is not a substitution for the missing native T over that root. -/
theorem s2232_concrete_bad_residue_mem_primeStrip
    (l : PrimeGeFive) (p : NumberField.FinitePlace ℚ)
    (hp : p ∈ S1730VModBad l) :
    residueCharacteristic p ∈ primeStrip 2 7 := by
  rcases (S1730VModBad_mem_iff_triple l p).mp hp with
    ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩
  · rw [concreteThreePlace_residueCharacteristic]
    exact mem_primeStrip_iff.mpr ⟨by norm_num, by norm_num, Nat.prime_three⟩
  · rw [S1712ConcreteFivePlace_residueCharacteristic]
    exact mem_primeStrip_iff.mpr ⟨by norm_num, by norm_num, Nat.prime_five⟩
  · rw [concreteSevenPlace_residueCharacteristic]
    exact mem_primeStrip_iff.mpr ⟨by norm_num, by norm_num, Nat.prime_seven⟩

/-- The actual prime-strip place attached to a concrete bad moduli place. -/
noncomputable def s2232_concretePrimePlace
    (l : PrimeGeFive) (p : NumberField.FinitePlace ℚ)
    (hp : p ∈ S1730VModBad l) : FinitePrimePlace 2 7 :=
  ⟨residueCharacteristic p, s2232_concrete_bad_residue_mem_primeStrip l p hp⟩

@[simp] theorem s2232_concretePrimePlace_val
    (l : PrimeGeFive) (p : NumberField.FinitePlace ℚ)
    (hp : p ∈ S1730VModBad l) :
    (s2232_concretePrimePlace l p hp).1 = residueCharacteristic p := rfl

/-- Transfer of concrete residue-characteristic strip evidence to the actual
tensor rational prime: any (T, b) whose bad residue characteristic lies in
the strip has qVFamTensorP T b in the strip. -/
theorem s2232_qVFamTensorP_mem_of_residueCharacteristic_mem
    (h : residueCharacteristic b.1 ∈ primeStrip 2 7) :
    qVFamTensorP T b ∈ primeStrip 2 7 := by
  rwa [s2232_qVFamTensorP_eq_b_residueCharacteristic T b]

/-- The same transfer in the exact named form. -/
theorem s2232_primeStripRequired_of_residueCharacteristic_mem
    (h : residueCharacteristic b.1 ∈ primeStrip 2 7) :
    S2232PrimeStripRequired T b :=
  s2232_qVFamTensorP_mem_of_residueCharacteristic_mem T b h

/-! ## 6. Axiom probes -/

#print axioms s2232_rational_residueCharacteristic_eq_natGenerator
#print axioms s2232_completionRationalPrime_val_eq_residueCharacteristic
#print axioms s2232_qVFamTensorP_eq_residueCharacteristic
#print axioms s2232_qVFamTensorP_eq_b_residueCharacteristic
#print axioms s2232_qVFamTensorP_prime
#print axioms s2232_qVFamTensorP_odd
#print axioms s2232_qVFamTensorP_coprime_l
#print axioms s2232_mem_primeStrip_iff_le_seven
#print axioms s2232_mem_primeStrip_iff_eq
#print axioms s2232_paperArithmeticConditions_iff_package
#print axioms s2232_package_of_paperArithmeticConditions
#print axioms s2232_paperArithmeticConditions_of_package
#print axioms s2232_source_constraints_do_not_force_strip
#print axioms s2232_concrete_bad_residue_mem_primeStrip
#print axioms s2232_concretePrimePlace
#print axioms s2232_qVFamTensorP_mem_of_residueCharacteristic_mem

#check S2232PaperArithmeticConditions
#check S2232PrimeStripRequired
#check S2232ResidueDegreeOneRequired
#check S2232RamificationIndexOneRequired
#check s2232_paperArithmeticConditions_iff_package
#check s2232_concretePrimePlace

end LeanFormal.IUT.XiFPaper.S2232Layer1PrimeAlignmentActual
end
