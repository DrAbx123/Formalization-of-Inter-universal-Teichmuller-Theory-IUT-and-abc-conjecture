import tmp.sheaf.xif.paper.S1729FullBadPlaceActual

/-!
# S1730: the bad moduli set with the fixed prime l removed

S1729 constructs the literal full bad moduli set {3, 5, 7} as three actual
rational finite places, the actual place above 3, split multiplicative
reduction at all three places, and the q-parameter proxies.  Its Clause (c)
card nevertheless needs Nat.Coprime p.characteristic l for **every** bad
place.  At l = 5 (resp. l = 7) the place above 5 (resp. 7) is in the full
set, so that coprime requirement is refuted.  The paper's Clause (c) instead
requires the fixed prime l not to occur among the bad moduli.

This file therefore constructs, for every l : PrimeGeFive, the honest bad
moduli set

  V_mod_bad(l) := {3, 5, 7} \ {p | residueCharacteristic p = l.value},

i.e. the full three-point actual set with the place of residue characteristic
l removed when that place is 5 or 7.  For l >= 11 nothing is removed; for
l = 5 the set is {3, 7} and for l = 7 it is {3, 5}.  It is therefore not a
singleton and not always the full set.

On this set we construct, unconditionally for all l >= 5:

* S1730Selection l : SourcePlaceSelection A l, with odd residue
  characteristics, nonemptiness and finiteness proved;
* the Fintype (Bad (S1730Selection l)) instance;
* S1730BadPlaceReductionCards l (Clause (b)), by restricting the S1729
  split multiplicative reduction cards from {3,5,7};
* S1730BadPlaceQParameterCards l (Clause (c)), because every remaining
  residue characteristic is now prime to l;
* S1730SourceReductionClause l, the assembled D4 reduction clause.

The two boundary cases are checked explicitly: at l = 5 the deleted place is
5, the bad set is exactly {3, 7}, and 3 and 7 are coprime to 5; at l = 7 the
deleted place is 7, the bad set is exactly {3, 5}, and 3 and 5 are coprime to
7.  No sorry, no axiom, no singleton posing as the full bad set, and no
unconditional reuse of the full {3,5,7} set when l = 5 or l = 7.
-/

noncomputable section

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 2000000

namespace LeanFormal.IUT.XiFPaper.S1730BadSetWithoutLActual

open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S1667AdmissibleCurveActual
open LeanFormal.IUT.XiFPaper.S1720SourceArithmeticActual
open LeanFormal.IUT.XiFPaper.S1724PaperArithmeticActual
open LeanFormal.IUT.XiFPaper.S1717PlaceSevenD5Actual
open LeanFormal.IUT.XiFPaper.S1712OddResidueActual
open LeanFormal.IUT.XiFPaper.S1729FullBadPlaceActual
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction

/-! ## 1. The bad moduli set with the place of residue characteristic l
removed -/

/-- The actual bad moduli set {3,5,7} with the rational finite place of
residue characteristic l.value removed.  Since l >= 5, only the places 5 and
7 can be removed; for all larger l the set is the full three-point set. -/
def S1730VModBad (l : PrimeGeFive) : Set (NumberField.FinitePlace ℚ) :=
  S1729VModBad \
    {p | NumberFieldFinitePlace.residueCharacteristic p = l.value}

/-- The bad set is contained in the literal full set {3,5,7}. -/
theorem S1730VModBad_subset (l : PrimeGeFive) :
    S1730VModBad l ⊆ S1729VModBad :=
  Set.sdiff_subset

/-- Membership in V_mod_bad(l): membership in {3,5,7} and residue
characteristic different from l. -/
theorem S1730VModBad_mem_iff (l : PrimeGeFive)
    (p : NumberField.FinitePlace ℚ) :
    p ∈ S1730VModBad l ↔
      p ∈ S1729VModBad ∧
        NumberFieldFinitePlace.residueCharacteristic p ≠ l.value := by
  rw [S1730VModBad, Set.mem_sdiff, Set.mem_setOf_eq]

/-- The explicit three-place description of V_mod_bad(l).  The conjunct
l.value != 3 is automatic for l >= 5, but is kept so that the statement is a
literal filtering of the three actual places. -/
theorem S1730VModBad_mem_iff_triple (l : PrimeGeFive)
    (p : NumberField.FinitePlace ℚ) :
    p ∈ S1730VModBad l ↔
      (p = concreteThreePlace ∧ l.value ≠ 3) ∨
      (p = concreteFivePlace ∧ l.value ≠ 5) ∨
      (p = concreteSevenPlace ∧ l.value ≠ 7) := by
  rw [S1730VModBad_mem_iff, S1729VModBad_mem_iff]
  constructor
  · rintro ⟨hp, hne⟩
    rcases hp with rfl | rfl | rfl
    · exact Or.inl ⟨rfl, fun h =>
        hne (by rw [concreteThreePlace_residueCharacteristic]; exact h.symm)⟩
    · exact Or.inr (Or.inl ⟨rfl, fun h =>
        hne (by rw [S1712ConcreteFivePlace_residueCharacteristic]; exact h.symm)⟩)
    · exact Or.inr (Or.inr ⟨rfl, fun h =>
        hne (by rw [concreteSevenPlace_residueCharacteristic]; exact h.symm)⟩)
  · rintro (⟨rfl, h3⟩ | ⟨rfl, h5⟩ | ⟨rfl, h7⟩)
    · refine ⟨S1729VModBad_three_mem, ?_⟩
      rw [concreteThreePlace_residueCharacteristic]
      exact fun h => h3 h.symm
    · refine ⟨S1729VModBad_five_mem, ?_⟩
      rw [S1712ConcreteFivePlace_residueCharacteristic]
      exact fun h => h5 h.symm
    · refine ⟨S1729VModBad_seven_mem, ?_⟩
      rw [concreteSevenPlace_residueCharacteristic]
      exact fun h => h7 h.symm

/-- The place 3 is always in V_mod_bad(l), since l >= 5. -/
theorem S1730VModBad_three_mem (l : PrimeGeFive) :
    concreteThreePlace ∈ S1730VModBad l := by
  rw [S1730VModBad_mem_iff]
  refine ⟨S1729VModBad_three_mem, ?_⟩
  rw [concreteThreePlace_residueCharacteristic]
  have h := l.ge_five
  omega

/-- The place 5 survives precisely when l.value != 5. -/
theorem S1730VModBad_five_mem_iff (l : PrimeGeFive) :
    concreteFivePlace ∈ S1730VModBad l ↔ l.value ≠ 5 := by
  rw [S1730VModBad_mem_iff]
  constructor
  · rintro ⟨-, hne⟩
    rw [S1712ConcreteFivePlace_residueCharacteristic] at hne
    exact fun h5 => hne h5.symm
  · intro h5
    refine ⟨S1729VModBad_five_mem, ?_⟩
    rw [S1712ConcreteFivePlace_residueCharacteristic]
    exact fun h => h5 h.symm

/-- The place 7 survives precisely when l.value != 7. -/
theorem S1730VModBad_seven_mem_iff (l : PrimeGeFive) :
    concreteSevenPlace ∈ S1730VModBad l ↔ l.value ≠ 7 := by
  rw [S1730VModBad_mem_iff]
  constructor
  · rintro ⟨-, hne⟩
    rw [concreteSevenPlace_residueCharacteristic] at hne
    exact fun h7 => hne h7.symm
  · intro h7
    refine ⟨S1729VModBad_seven_mem, ?_⟩
    rw [concreteSevenPlace_residueCharacteristic]
    exact fun h => h7 h.symm

/-- Every point of V_mod_bad(l) has odd residue characteristic, because it is
one of the three S1729 bad places. -/
theorem S1730VModBad_odd (l : PrimeGeFive)
    (p : NumberField.FinitePlace ℚ) (hp : p ∈ S1730VModBad l) :
    Odd (NumberFieldFinitePlace.residueCharacteristic p) :=
  S1729VModBad_odd p (S1730VModBad_subset l hp)

/-- V_mod_bad(l) is nonempty: it always contains the actual place 3. -/
theorem S1730VModBad_nonempty (l : PrimeGeFive) :
    (S1730VModBad l).Nonempty :=
  ⟨concreteThreePlace, S1730VModBad_three_mem l⟩

/-- V_mod_bad(l) is finite, being a subset of the finite set {3,5,7}. -/
theorem S1730VModBad_finite (l : PrimeGeFive) :
    (S1730VModBad l).Finite :=
  S1729VModBad_finite.subset (S1730VModBad_subset l)

/-- V_mod_bad(l) is never a singleton.  If l = 5 it contains 3 and 7;
otherwise it contains 3 and 5. -/
theorem S1730VModBad_not_singleton (l : PrimeGeFive) :
    ∃ p ∈ S1730VModBad l, ∃ q ∈ S1730VModBad l, p ≠ q := by
  by_cases h5 : l.value = 5
  · refine ⟨concreteThreePlace, S1730VModBad_three_mem l,
      concreteSevenPlace, ?_, S1729Three_ne_seven⟩
    exact (S1730VModBad_seven_mem_iff l).mpr (by rw [h5]; norm_num)
  · refine ⟨concreteThreePlace, S1730VModBad_three_mem l,
      concreteFivePlace, ?_, S1729Three_ne_five⟩
    exact (S1730VModBad_five_mem_iff l).mpr h5

/-- If l is neither 5 nor 7, then nothing is removed and V_mod_bad(l) is the
literal full set {3,5,7}. -/
theorem S1730VModBad_eq_full_of_ne (l : PrimeGeFive)
    (h5 : l.value ≠ 5) (h7 : l.value ≠ 7) :
    S1730VModBad l = S1729VModBad := by
  ext p
  rw [S1730VModBad_mem_iff]
  constructor
  · rintro ⟨hp, -⟩
    exact hp
  · intro hp
    refine ⟨hp, ?_⟩
    rcases (S1729VModBad_mem_iff p).mp hp with rfl | rfl | rfl
    · rw [concreteThreePlace_residueCharacteristic]
      have h := l.ge_five
      omega
    · rw [S1712ConcreteFivePlace_residueCharacteristic]
      exact fun h => h5 h.symm
    · rw [concreteSevenPlace_residueCharacteristic]
      exact fun h => h7 h.symm

/-- If l is neither 5 nor 7, the three concrete places 3, 5 and 7 are all in
V_mod_bad(l) and are pairwise distinct; this is the three-point case. -/
theorem S1730VModBad_three_distinct_of_ne (l : PrimeGeFive)
    (h5 : l.value ≠ 5) (h7 : l.value ≠ 7) :
    concreteThreePlace ∈ S1730VModBad l ∧
      concreteFivePlace ∈ S1730VModBad l ∧
      concreteSevenPlace ∈ S1730VModBad l ∧
      concreteThreePlace ≠ concreteFivePlace ∧
      concreteThreePlace ≠ concreteSevenPlace ∧
      concreteFivePlace ≠ concreteSevenPlace := by
  have hset := S1730VModBad_eq_full_of_ne l h5 h7
  refine ⟨?_, ?_, ?_, S1729Three_ne_five, S1729Three_ne_seven,
    S1729Five_ne_seven⟩
  · rw [hset]
    exact S1729VModBad_three_mem
  · rw [hset]
    exact S1729VModBad_five_mem
  · rw [hset]
    exact S1729VModBad_seven_mem

/-! ## 2. The actual source selection with V_mod_bad(l) -/

/-- Definition 3.1(b) source place selection with the honest bad moduli set
{3,5,7} \ {l} over the actual arithmetic input A l. -/
noncomputable def S1730Selection (l : PrimeGeFive) :
    SourcePlaceSelection (S1724InitialThetaArithmeticData l) where
  V_mod_bad := S1730VModBad l
  V_mod_bad_odd_residue_characteristic := S1730VModBad_odd l
  V_mod_bad_nonempty := S1730VModBad_nonempty l

@[simp] theorem S1730Selection_V_mod_bad (l : PrimeGeFive) :
    (S1730Selection l).V_mod_bad = S1730VModBad l := rfl

theorem S1730Selection_V_mod_bad_finite (l : PrimeGeFive) :
    (S1730Selection l).V_mod_bad.Finite := by
  rw [S1730Selection_V_mod_bad]
  exact S1730VModBad_finite l

/-- The finite index Bad (S1730Selection l) of the bad moduli places. -/
@[reducible] noncomputable def S1730BadFintype (l : PrimeGeFive) :
    Fintype (Bad (S1730Selection l)) :=
  (S1730Selection_V_mod_bad_finite l).fintype

instance S1730BadFintypeInstance (l : PrimeGeFive) :
    Fintype (Bad (S1730Selection l)) :=
  S1730BadFintype l

/-! ## 3. Clause (b): split multiplicative reduction at the surviving bad
places -/

/-- Split multiplicative reduction at every place of F' above a place of
V_mod_bad(l), obtained by restricting the S1729 cards from {3,5,7}. -/
theorem S1730SplitAtDF (l : PrimeGeFive)
    (w : NumberField.FinitePlace (S1724InitialThetaArithmeticData l).F)
    (hw : NumberFieldFinitePlace.comap
      (k := (S1724InitialThetaArithmeticData l).Fmod) w ∈
        (S1730Selection l).V_mod_bad) :
    (S1724InitialThetaArithmeticData l).curve.HasSplitMultiplicativeReductionAt w :=
  S1729SplitAtDF l w (S1730VModBad_subset l hw)

/-- Clause (b) reduction cards for the selection with V_mod_bad(l). -/
theorem S1730BadPlaceReductionCards (l : PrimeGeFive) :
    BadPlaceReductionCards (S1730Selection l) :=
  BadPlaceReductionCards.ofSplitMultiplicative
    (fun w hw => S1730SplitAtDF l w hw)

/-! ## 4. Clause (c): unconditional q-parameter cards -/

/-- Every residue characteristic occurring in V_mod_bad(l) is prime to l.
This is where the removal of the place l matters: at l = 5 (resp. l = 7) the
surviving residue characteristics are 3 and 7 (resp. 3 and 5). -/
theorem S1730BadResidueCharacteristic_coprime (l : PrimeGeFive) :
    ∀ p : NumberField.FinitePlace ℚ,
      p ∈ S1730VModBad l →
        Nat.Coprime (NumberFieldFinitePlace.residueCharacteristic p) l.value := by
  intro p hp
  have hp' := (S1730VModBad_mem_iff l p).mp hp
  rcases (S1729VModBad_mem_iff p).mp hp'.1 with rfl | rfl | rfl
  · rw [concreteThreePlace_residueCharacteristic]
    exact S1729Three_coprime l
  · rw [S1712ConcreteFivePlace_residueCharacteristic]
    have hne : 5 ≠ l.value := by
      simpa [S1712ConcreteFivePlace_residueCharacteristic] using hp'.2
    exact (S1729Five_coprime_iff l).mpr (fun h => hne h.symm)
  · rw [concreteSevenPlace_residueCharacteristic]
    have hne : 7 ≠ l.value := by
      simpa [concreteSevenPlace_residueCharacteristic] using hp'.2
    exact (S1729Seven_coprime_iff l).mpr (fun h => hne h.symm)

/-- The type-I_n order at a bad place: 2 above 7 and 6 above 3 or 5. -/
def S1730BadOrder (l : PrimeGeFive)
    (w : NumberField.FinitePlace (S1724InitialThetaArithmeticData l).F)
    (hw : NumberFieldFinitePlace.comap
      (k := (S1724InitialThetaArithmeticData l).Fmod) w ∈
        (S1730Selection l).V_mod_bad) : ℕ :=
  S1729BadOrder w (S1730VModBad_subset l hw)

theorem S1730BadOrder_pos (l : PrimeGeFive)
    (w : NumberField.FinitePlace (S1724InitialThetaArithmeticData l).F)
    (hw : NumberFieldFinitePlace.comap
      (k := (S1724InitialThetaArithmeticData l).Fmod) w ∈
        (S1730Selection l).V_mod_bad) :
    0 < S1730BadOrder l w hw :=
  S1729BadOrder_pos w (S1730VModBad_subset l hw)

theorem S1730BadOrder_primeToL (l : PrimeGeFive)
    (w : NumberField.FinitePlace (S1724InitialThetaArithmeticData l).F)
    (hw : NumberFieldFinitePlace.comap
      (k := (S1724InitialThetaArithmeticData l).Fmod) w ∈
        (S1730Selection l).V_mod_bad) :
    Nat.Coprime (S1730BadOrder l w hw) l.value :=
  S1729BadOrder_primeToL l w (S1730VModBad_subset l hw)

/-- Clause (c) q-parameter cards for the selection with V_mod_bad(l),
unconditionally for every l : PrimeGeFive. -/
noncomputable def S1730BadPlaceQParameterCards (l : PrimeGeFive) :
    BadPlaceQParameterCards (S1730Selection l) where
  badResidueCharacteristic_primeToL := S1730BadResidueCharacteristic_coprime l
  sourceQParameterOrder := S1730BadOrder l
  sourceQParameterOrder_pos := fun w hw => S1730BadOrder_pos l w hw
  sourceQParameterOrder_primeToL := fun w hw =>
    S1730BadOrder_primeToL l w hw

/-! ## 5. D4: the assembled source reduction clause -/

/-- The D3/D4 source reduction clause from an arbitrary Clause (b) card. -/
noncomputable def S1730SourceReductionClauseOfCards (l : PrimeGeFive)
    (C : BadPlaceReductionCards (S1730Selection l)) :
    Theorem311Source.SourceReductionClause
      (Selected (S1730Selection l)) (Bad (S1730Selection l)) :=
  toSourceReductionClause (S1730Selection l) C

/-- The unconditional source reduction clause over V_mod_bad(l). -/
noncomputable def S1730SourceReductionClause (l : PrimeGeFive) :
    Theorem311Source.SourceReductionClause
      (Selected (S1730Selection l)) (Bad (S1730Selection l)) :=
  S1730SourceReductionClauseOfCards l (S1730BadPlaceReductionCards l)

theorem S1730SourceReductionClause_split (l : PrimeGeFive)
    (b : Bad (S1730Selection l)) :
    (S1730SourceReductionClause l).splitMultiplicativeReduction b :=
  (S1730SourceReductionClause l).splitMultiplicativeReduction_proved b

theorem S1730SourceReductionClause_qParameter_nonzero (l : PrimeGeFive)
    (b : Bad (S1730Selection l)) :
    (S1730SourceReductionClause l).qParameter b ≠ 0 :=
  (S1730SourceReductionClause l).qParameter_nonzero b

theorem S1730SourceReductionClause_qParameter_contracting (l : PrimeGeFive)
    (b : Bad (S1730Selection l)) :
    ‖(S1730SourceReductionClause l).qParameter b‖ < 1 :=
  (S1730SourceReductionClause l).qParameter_contracting b

/-! ## 6. The boundary values l = 5 and l = 7 -/

/-- The concrete label l = 5. -/
abbrev S1730Five : PrimeGeFive := S1729Five

/-- The concrete label l = 7. -/
abbrev S1730Seven : PrimeGeFive := S1729Seven

@[simp] theorem S1730Five_value : S1730Five.value = 5 := rfl

@[simp] theorem S1730Seven_value : S1730Seven.value = 7 := rfl

/-- At l = 5 the removed point 5 is not in the bad set. -/
theorem S1730Five_not_mem :
    concreteFivePlace ∉ S1730VModBad S1730Five := by
  rw [S1730VModBad, Set.mem_sdiff]
  intro h
  have h' := h.2
  rw [Set.mem_setOf_eq, S1712ConcreteFivePlace_residueCharacteristic,
    S1730Five_value] at h'
  exact h' rfl

/-- At l = 7 the removed point 7 is not in the bad set. -/
theorem S1730Seven_not_mem :
    concreteSevenPlace ∉ S1730VModBad S1730Seven := by
  rw [S1730VModBad, Set.mem_sdiff]
  intro h
  have h' := h.2
  rw [Set.mem_setOf_eq, concreteSevenPlace_residueCharacteristic,
    S1730Seven_value] at h'
  exact h' rfl

/-- At l = 5 the bad set is not the full set {3,5,7}: the place 5 is absent. -/
theorem S1730Five_not_full :
    S1730VModBad S1730Five ≠ S1729VModBad := by
  intro h
  have hmem : concreteFivePlace ∈ S1730VModBad S1730Five := by
    rw [h]
    exact S1729VModBad_five_mem
  exact S1730Five_not_mem hmem

/-- At l = 7 the bad set is not the full set {3,5,7}: the place 7 is absent. -/
theorem S1730Seven_not_full :
    S1730VModBad S1730Seven ≠ S1729VModBad := by
  intro h
  have hmem : concreteSevenPlace ∈ S1730VModBad S1730Seven := by
    rw [h]
    exact S1729VModBad_seven_mem
  exact S1730Seven_not_mem hmem

/-- At l = 5 the bad set is exactly the two-point set {3,7} (the full set
with the place 5 deleted). -/
theorem S1730VModBad_five_eq :
    S1730VModBad S1730Five =
      ({concreteThreePlace, concreteSevenPlace} :
        Set (NumberField.FinitePlace ℚ)) := by
  ext p
  rw [S1730VModBad_mem_iff, S1729VModBad_mem_iff]
  constructor
  · rintro ⟨hp, hne⟩
    rcases hp with rfl | rfl | rfl
    · simp
    · exfalso
      apply hne
      rw [S1712ConcreteFivePlace_residueCharacteristic]
      exact S1730Five_value.symm
    · simp
  · intro hp
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hp
    rcases hp with rfl | rfl
    · refine ⟨S1729VModBad_three_mem, ?_⟩
      rw [concreteThreePlace_residueCharacteristic,
        S1730Five_value]
      norm_num
    · refine ⟨S1729VModBad_seven_mem, ?_⟩
      rw [concreteSevenPlace_residueCharacteristic,
        S1730Five_value]
      norm_num

/-- At l = 7 the bad set is exactly the two-point set {3,5} (the full set
with the place 7 deleted). -/
theorem S1730VModBad_seven_eq :
    S1730VModBad S1730Seven =
      ({concreteThreePlace, concreteFivePlace} :
        Set (NumberField.FinitePlace ℚ)) := by
  ext p
  rw [S1730VModBad_mem_iff, S1729VModBad_mem_iff]
  constructor
  · rintro ⟨hp, hne⟩
    rcases hp with rfl | rfl | rfl
    · simp
    · simp
    · exfalso
      apply hne
      rw [concreteSevenPlace_residueCharacteristic]
      exact S1730Seven_value.symm
  · intro hp
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hp
    rcases hp with rfl | rfl
    · refine ⟨S1729VModBad_three_mem, ?_⟩
      rw [concreteThreePlace_residueCharacteristic,
        S1730Seven_value]
      norm_num
    · refine ⟨S1729VModBad_five_mem, ?_⟩
      rw [S1712ConcreteFivePlace_residueCharacteristic,
        S1730Seven_value]
      norm_num

/-- At l = 5 the two surviving residue characteristics 3 and 7 are both
coprime to 5. -/
theorem S1730Five_remaining_coprime :
    Nat.Coprime
        (NumberFieldFinitePlace.residueCharacteristic concreteThreePlace)
        S1730Five.value ∧
      Nat.Coprime
        (NumberFieldFinitePlace.residueCharacteristic concreteSevenPlace)
        S1730Five.value := by
  constructor
  · rw [concreteThreePlace_residueCharacteristic, S1730Five_value]
    decide
  · rw [concreteSevenPlace_residueCharacteristic, S1730Five_value]
    decide

/-- At l = 7 the two surviving residue characteristics 3 and 5 are both
coprime to 7. -/
theorem S1730Seven_remaining_coprime :
    Nat.Coprime
        (NumberFieldFinitePlace.residueCharacteristic concreteThreePlace)
        S1730Seven.value ∧
      Nat.Coprime
        (NumberFieldFinitePlace.residueCharacteristic concreteFivePlace)
        S1730Seven.value := by
  constructor
  · rw [concreteThreePlace_residueCharacteristic, S1730Seven_value]
    decide
  · rw [S1712ConcreteFivePlace_residueCharacteristic, S1730Seven_value]
    decide

/-- Clause (c) exists unconditionally at l = 5, with the place 5 excluded. -/
theorem S1730FiveQParameterCards :
    Nonempty (BadPlaceQParameterCards (S1730Selection S1730Five)) :=
  ⟨S1730BadPlaceQParameterCards S1730Five⟩

/-- Clause (c) exists unconditionally at l = 7, with the place 7 excluded. -/
theorem S1730SevenQParameterCards :
    Nonempty (BadPlaceQParameterCards (S1730Selection S1730Seven)) :=
  ⟨S1730BadPlaceQParameterCards S1730Seven⟩

/-- The unconditional reduction clause exists at l = 5. -/
theorem S1730FiveSourceReductionClause :
    Nonempty (Theorem311Source.SourceReductionClause
      (Selected (S1730Selection S1730Five))
      (Bad (S1730Selection S1730Five))) :=
  ⟨S1730SourceReductionClause S1730Five⟩

/-- The unconditional reduction clause exists at l = 7. -/
theorem S1730SevenSourceReductionClause :
    Nonempty (Theorem311Source.SourceReductionClause
      (Selected (S1730Selection S1730Seven))
      (Bad (S1730Selection S1730Seven))) :=
  ⟨S1730SourceReductionClause S1730Seven⟩

/-! ## 7. Axiom footprint -/

#print axioms S1730VModBad_odd
#print axioms S1730VModBad_nonempty
#print axioms S1730VModBad_finite
#print axioms S1730VModBad_not_singleton
#print axioms S1730VModBad_three_distinct_of_ne
#print axioms S1730Selection
#print axioms S1730BadFintype
#print axioms S1730BadPlaceReductionCards
#print axioms S1730BadPlaceQParameterCards
#print axioms S1730SourceReductionClause
#print axioms S1730Five_not_mem
#print axioms S1730Seven_not_mem
#print axioms S1730Five_not_full
#print axioms S1730Seven_not_full
#print axioms S1730VModBad_five_eq
#print axioms S1730VModBad_seven_eq
#print axioms S1730Five_remaining_coprime
#print axioms S1730Seven_remaining_coprime
#print axioms S1730FiveQParameterCards
#print axioms S1730SevenQParameterCards
#print axioms S1730FiveSourceReductionClause
#print axioms S1730SevenSourceReductionClause

end LeanFormal.IUT.XiFPaper.S1730BadSetWithoutLActual

end
