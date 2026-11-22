import tmp.sheaf.xif.paper.S2482QiArithmeticActual
import tmp.sheaf.xif.paper.S2485Places3Actual
import tmp.sheaf.xif.paper.S2489FbarActual

/-!
# S2490: the actual all-places restriction section and the place data of
IUT I, Definition 3.1, over the Gaussian field Q(i)

This file works over the actual Gaussian field

  F = AdjoinRoot (X ^ 2 + 1 : Q[X])

of S2480QiActual, i.e. F = Q(i), and over the actual punctured elliptic
curve y^2 = x^3 - x of S2482QiCurveActual.

## What is constructed (unconditionally, no sorry, no added axiom)

* S2490RestrictionSection : NumberFieldPlace.RestrictionSection Q F.  This is
  the canonical all-places section of LeanFormal.IUT.Foundations.NumberField.Places:
  one extension of every finite rational place and one extension of every
  infinite rational place, with comap as a left inverse
  (S2490RestrictionSection_comap_lift) and injective lift
  (S2490RestrictionSection_lift_injective).
* The actual arithmetic input S2490ArithmeticData l with
  Fmod = Q, F = K = F, for every l : PrimeGeFive (the tower has degree two,
  prime to l), together with its l = 5 instance S2490A, whose carriers are
  definitionally those of the established S2482Arithmetic.arithmeticData.
* The rational bad moduli place S2490VModBad = {S2485p3}, the place over 3,
  with the new computation
  S2490p3_residueCharacteristic : residueCharacteristic S2485p3 = 3 and the
  resulting oddness S2490VModBad_odd.
* The all-places data: V = range (lift) (S2490V), the bijection V_mod -> V
  induced by restriction (S2490VModBijection) and the restriction
  compatibility S2490VPlaceComap.

These eight fields are bundled in S2490AllPlacesFields, which is literally the
place-field block of SourceSignQuotientData (V, V_mod_bad,
V_mod_bad_odd_residue_characteristic, V_mod_bad_nonempty, V_section,
V_eq_section, V_mod_bijection, V_place_comap).  S2490PlaceFields (resp.
S2490PlaceFieldsA) is the concrete instance for S2490ArithmeticData l (resp.
for S2490A).

## Consumer

S2490AllPlacesFields.fill writes these eight fields into any
SourceSignQuotientData, leaving every other field untouched; the lemmas
fill_cK and fill_epsilon record that the still-input K-side cusp data are not
modified.  Thus the place block of Definition 3.1(e) is no longer an input: it
is the actual canonical restriction section.  Conversely
S2490AllPlacesFields.ofSourceSignQuotientData extracts the place block of a
source record, and the two round trips are proven.

## What is deliberately *not* constructed here

The remaining fields of SourceSignQuotientData -- the F-side orbicurve xF, the
sign action and quotient cF, the fundamental-group data, the K-side
orbicurves xK, cK, their scalar extensions and signature identifications, and
the cusp epsilon -- are clause (a)/(d)/(f) data and are not touched by this
file.  In particular cK and epsilon remain inputs of the record: fill is
proved to preserve them (fill_cK, fill_epsilon).  No structure is filled with
PUnit, True, or an arbitrary type.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 2000000

open scoped NumberField
open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.XiFPaper.S2480QiActual
open LeanFormal.IUT.XiFPaper.S2482QiCurveActual
open LeanFormal.IUT.XiFPaper.S2482QiArithmeticActual
open LeanFormal.IUT.XiFPaper.S2482QiArithmeticActual.S2482Arithmetic
open LeanFormal.IUT.XiFPaper.S2485Places3Actual

namespace LeanFormal.IUT.XiFPaper.S2490RestrictionSectionActual

/-! ## 1. The actual Gaussian arithmetic input A -/

/-- The Gaussian tower Q -> F -> F satisfies the l-prime-to-degree condition
for every prime l >= 5: the degree is 2, which is coprime to every odd
prime. -/
theorem S2490ThetaTower (l : PrimeGeFive) :
    ThetaFieldTower l ℚ F F where
  sqrtNegOne := S2480_hasSqrtNegOne
  degreePrimeToL := by
    rw [S2482_finrank]
    exact l.odd.coprime_two_left

/-- The actual arithmetic input over Q(i): Fmod = Q, F = K = Q(i), and the
punctured curve y^2 = x^3 - x.  This is the Gaussian analogue of
S2482Arithmetic.arithmeticData, valid for every l : PrimeGeFive. -/
noncomputable def S2490ArithmeticData (l : PrimeGeFive) :
    InitialThetaArithmeticData l where
  Fmod := ℚ
  F := F
  K := F
  tower := S2490ThetaTower l
  curve := S2482PuncturedCurve

/-- The l = 5 arithmetic input used elsewhere in the Gaussian place files:
literally S2482Arithmetic.arithmeticData. -/
abbrev S2490A : InitialThetaArithmeticData l5 :=
  S2482Arithmetic.arithmeticData

@[simp] theorem S2490ArithmeticData_Fmod (l : PrimeGeFive) :
    (S2490ArithmeticData l).Fmod = ℚ := rfl

@[simp] theorem S2490ArithmeticData_F (l : PrimeGeFive) :
    (S2490ArithmeticData l).F = F := rfl

@[simp] theorem S2490ArithmeticData_K (l : PrimeGeFive) :
    (S2490ArithmeticData l).K = F := rfl

@[simp] theorem S2490ArithmeticData_curve (l : PrimeGeFive) :
    (S2490ArithmeticData l).curve = S2482PuncturedCurve := rfl

@[simp] theorem S2490A_Fmod : S2490A.Fmod = ℚ := rfl

@[simp] theorem S2490A_F : S2490A.F = F := rfl

@[simp] theorem S2490A_K : S2490A.K = F := rfl

@[simp] theorem S2490A_curve : S2490A.curve = S2482PuncturedCurve := rfl

/-- The l = 5 specialization has the same carriers as the general Gaussian
input. -/
theorem S2490A_Fmod_eq_general :
    S2490A.Fmod = (S2490ArithmeticData l5).Fmod := rfl

theorem S2490A_K_eq_general :
    S2490A.K = (S2490ArithmeticData l5).K := rfl

theorem S2490A_curve_eq_general :
    S2490A.curve = (S2490ArithmeticData l5).curve := rfl

/-! ## 2. The all-places restriction section Q -> Q(i) -/

/-- The canonical restriction section over Q: it extends every finite rational
place to a finite place of Q(i) and every infinite rational place to an
infinite place of Q(i), and restriction is a left inverse. -/
noncomputable def S2490RestrictionSection :
    NumberFieldPlace.RestrictionSection ℚ F :=
  NumberFieldPlace.restrictionSection

/-- The lift of a finite place stays finite (it is the chosen finite extension
of NumberFieldFinitePlace.comap_surjective). -/
@[simp] theorem S2490RestrictionSection_lift_finite
    (p : NumberField.FinitePlace ℚ) :
    ∃ q : NumberField.FinitePlace F,
      S2490RestrictionSection.lift (NumberFieldPlace.finite p) =
        NumberFieldPlace.finite q :=
  ⟨NumberFieldPlace.finiteLift (K := F) p, rfl⟩

/-- The lift of an infinite place stays infinite (it is the chosen extension of
NumberField.InfinitePlace.comap_surjective). -/
@[simp] theorem S2490RestrictionSection_lift_infinite
    (v : NumberField.InfinitePlace ℚ) :
    ∃ w : NumberField.InfinitePlace F,
      S2490RestrictionSection.lift (NumberFieldPlace.infinite v) =
        NumberFieldPlace.infinite w :=
  ⟨NumberFieldPlace.infiniteLift (K := F) v, rfl⟩

/-- Every lower place is recovered by restricting its chosen extension. -/
theorem S2490RestrictionSection_comap_lift
    (v : NumberFieldPlace ℚ) :
    NumberFieldPlace.comap (k := ℚ) (S2490RestrictionSection.lift v) = v :=
  S2490RestrictionSection.comap_lift v

/-- The chosen extensions of distinct rational places are distinct. -/
theorem S2490RestrictionSection_lift_injective :
    Function.Injective S2490RestrictionSection.lift :=
  S2490RestrictionSection.lift_injective

/-- The canonical restriction section in the source-tuple notation A.Fmod,
A.K. -/
noncomputable def S2490ArithmeticSection (l : PrimeGeFive) :
    NumberFieldPlace.RestrictionSection (S2490ArithmeticData l).Fmod
      (S2490ArithmeticData l).K :=
  NumberFieldPlace.restrictionSection

/-- The canonical restriction section for the established Gaussian input
S2490A (i.e. S2482Arithmetic.arithmeticData). -/
noncomputable def S2490ASection :
    NumberFieldPlace.RestrictionSection S2490A.Fmod S2490A.K :=
  NumberFieldPlace.restrictionSection

theorem S2490ArithmeticSection_eq (l : PrimeGeFive) :
    S2490ArithmeticSection l = S2490RestrictionSection := rfl

theorem S2490ASection_eq :
    S2490ASection = S2490RestrictionSection := rfl

theorem S2490ASection_comap_lift (v : NumberFieldPlace S2490A.Fmod) :
    NumberFieldPlace.comap (k := S2490A.Fmod) (S2490ASection.lift v) = v :=
  S2490ASection.comap_lift v

/-! ## 3. The bad moduli place over 3 and its residue characteristic -/

/-- The bad moduli set of the source tuple over Q: the rational place p3 over
3, as constructed in S2485Places3Actual. -/
def S2490VModBad : Set (NumberField.FinitePlace ℚ) :=
  S2485VModBad

theorem S2490VModBad_eq : S2490VModBad = {S2485p3} := rfl

/-- The rational prime 3 lies in the maximal ideal of the rational place over
3. -/
theorem S2490p3_three_mem :
    ((3 : ℕ) : 𝓞 ℚ) ∈ (S2485p3).maximalIdeal.asIdeal := by
  unfold S2485p3
  rw [NumberField.FinitePlace.maximalIdeal_mk]
  show ((3 : ℕ) : 𝓞 ℚ) ∈
    Ideal.comap Rat.ringOfIntegersEquiv.toRingHom (Ideal.span {(3 : ℤ)})
  refine Ideal.mem_comap.mpr ?_
  have hmap :
      Rat.ringOfIntegersEquiv.toRingHom ((3 : ℕ) : 𝓞 ℚ) =
        ((3 : ℕ) : ℤ) :=
    map_natCast _ 3
  rw [hmap]
  exact Ideal.mem_span_singleton_self ((3 : ℕ) : ℤ)

/-- The residue characteristic of the rational place over 3 is 3. -/
theorem S2490p3_residueCharacteristic :
    NumberFieldFinitePlace.residueCharacteristic S2485p3 = 3 := by
  show ringChar (NumberFieldFinitePlace.ResidueField S2485p3) = 3
  refine CharP.ringChar_of_prime_eq_zero Nat.prime_three ?_
  have h :
      Ideal.Quotient.mk (S2485p3).maximalIdeal.asIdeal
          ((3 : ℕ) : 𝓞 ℚ) =
        ((3 : ℕ) : NumberFieldFinitePlace.ResidueField S2485p3) :=
    map_natCast (Ideal.Quotient.mk (S2485p3).maximalIdeal.asIdeal) 3
  rw [← h]
  exact Ideal.Quotient.eq_zero_iff_mem.mpr S2490p3_three_mem

theorem S2490p3_odd :
    Odd (NumberFieldFinitePlace.residueCharacteristic S2485p3) := by
  rw [S2490p3_residueCharacteristic]
  exact ⟨1, by norm_num⟩

/-- Every bad moduli place has odd residue characteristic (the set is the
singleton p3). -/
theorem S2490VModBad_odd :
    ∀ p : NumberField.FinitePlace ℚ, p ∈ S2490VModBad →
      Odd (NumberFieldFinitePlace.residueCharacteristic p) := by
  intro p hp
  have hp' : p = S2485p3 := by
    simpa [S2490VModBad, S2485VModBad] using hp
  rw [hp']
  exact S2490p3_odd

theorem S2490VModBad_nonempty : S2490VModBad.Nonempty :=
  ⟨S2485p3, by simp [S2490VModBad, S2485VModBad]⟩

/-! ## 4. The all-places data V, V_mod -> V, and restriction compatibility -/

/-- V is the image of the canonical all-places section. -/
noncomputable def S2490V : Set (NumberFieldPlace F) :=
  S2490RestrictionSection.selected

theorem S2490V_eq_range :
    S2490V = Set.range S2490RestrictionSection.lift := rfl

theorem S2490V_spec (v : NumberFieldPlace F) :
    v ∈ S2490V ↔ ∃ u : NumberFieldPlace ℚ,
      S2490RestrictionSection.lift u = v :=
  Iff.rfl

/-- The actual bijection V_mod = Place(Q) -> V induced by the restriction
section. -/
noncomputable def S2490VModBijection :
    NumberFieldPlace ℚ ≃ {v : NumberFieldPlace F // v ∈ S2490V} :=
  S2490RestrictionSection.selectedEquiv

@[simp] theorem S2490VModBijection_apply (v : NumberFieldPlace ℚ) :
    (S2490VModBijection v).1 = S2490RestrictionSection.lift v :=
  rfl

theorem S2490VModBijection_symm_apply
    (v : {v : NumberFieldPlace F // v ∈ S2490V}) :
    S2490VModBijection.symm v =
      NumberFieldPlace.comap (k := ℚ) v.1 :=
  NumberFieldPlace.RestrictionSection.selectedEquiv_symm_apply
    S2490RestrictionSection v

/-- The defining compatibility of the place bijection: restricting a selected
place gives back its V_mod index. -/
theorem S2490VPlaceComap
    (v : {v : NumberFieldPlace F // v ∈ S2490V}) :
    NumberFieldPlace.comap (k := ℚ) v.1 = S2490VModBijection.symm v :=
  (S2490VModBijection_symm_apply v).symm

/-! ## 5. The eight place fields of SourceSignQuotientData, bundled -/

/-- The place-field block of SourceSignQuotientData, with exactly the same
eight fields and no additional data. -/
structure S2490AllPlacesFields {l : PrimeGeFive}
    (A : InitialThetaArithmeticData l) where
  V : Set (NumberFieldPlace A.K)
  V_mod_bad : Set (NumberField.FinitePlace A.Fmod)
  V_mod_bad_odd_residue_characteristic :
    ∀ p, p ∈ V_mod_bad →
      Odd (NumberFieldFinitePlace.residueCharacteristic p)
  V_mod_bad_nonempty : V_mod_bad.Nonempty
  V_section : NumberFieldPlace.RestrictionSection A.Fmod A.K
  V_eq_section : V = V_section.selected
  V_mod_bijection :
    NumberFieldPlace A.Fmod ≃ {v : NumberFieldPlace A.K // v ∈ V}
  V_place_comap :
    ∀ v : {v : NumberFieldPlace A.K // v ∈ V},
      NumberFieldPlace.comap (k := A.Fmod) v.1 = V_mod_bijection.symm v

/-- The concrete place block over the general Gaussian input
S2490ArithmeticData l. -/
noncomputable def S2490PlaceFields (l : PrimeGeFive) :
    S2490AllPlacesFields (S2490ArithmeticData l) where
  V := S2490V
  V_mod_bad := S2490VModBad
  V_mod_bad_odd_residue_characteristic := S2490VModBad_odd
  V_mod_bad_nonempty := S2490VModBad_nonempty
  V_section := S2490ArithmeticSection l
  V_eq_section := rfl
  V_mod_bijection := S2490VModBijection
  V_place_comap := S2490VPlaceComap

/-- The concrete place block over the established Gaussian input S2490A
(S2482Arithmetic.arithmeticData). -/
noncomputable def S2490PlaceFieldsA :
    S2490AllPlacesFields S2490A where
  V := S2490V
  V_mod_bad := S2490VModBad
  V_mod_bad_odd_residue_characteristic := S2490VModBad_odd
  V_mod_bad_nonempty := S2490VModBad_nonempty
  V_section := S2490ASection
  V_eq_section := rfl
  V_mod_bijection := S2490VModBijection
  V_place_comap := S2490VPlaceComap

@[simp] theorem S2490PlaceFieldsA_V :
    S2490PlaceFieldsA.V = S2490V := rfl

@[simp] theorem S2490PlaceFieldsA_V_mod_bad :
    S2490PlaceFieldsA.V_mod_bad = S2490VModBad := rfl

@[simp] theorem S2490PlaceFieldsA_V_section :
    S2490PlaceFieldsA.V_section = S2490ASection := rfl

@[simp] theorem S2490PlaceFieldsA_V_mod_bijection :
    S2490PlaceFieldsA.V_mod_bijection = S2490VModBijection := rfl

/-! ## 6. Consistency with the generic source place selection -/

/-- The same place block obtained from the generic
SourcePlaceSelection.singleton: this checks that the concrete construction is
exactly the canonical one of the foundations. -/
noncomputable def S2490PlaceSelection (l : PrimeGeFive) :
    SourcePlaceSelection (S2490ArithmeticData l) :=
  SourcePlaceSelection.singleton (S2490ArithmeticData l) S2485p3 S2490p3_odd

noncomputable def S2490APlaceSelection :
    SourcePlaceSelection S2490A :=
  SourcePlaceSelection.singleton S2490A S2485p3 S2490p3_odd

@[simp] theorem S2490PlaceSelection_V_mod_bad (l : PrimeGeFive) :
    (S2490PlaceSelection l).V_mod_bad = S2490VModBad := rfl

@[simp] theorem S2490PlaceSelection_V (l : PrimeGeFive) :
    (S2490PlaceSelection l).V = S2490V := rfl

@[simp] theorem S2490PlaceSelection_V_section (l : PrimeGeFive) :
    (S2490PlaceSelection l).V_section = S2490ArithmeticSection l := rfl

@[simp] theorem S2490PlaceSelection_V_mod_bijection (l : PrimeGeFive) :
    (S2490PlaceSelection l).V_mod_bijection = S2490VModBijection := rfl

@[simp] theorem S2490APlaceSelection_V_mod_bad :
    S2490APlaceSelection.V_mod_bad = S2490VModBad := rfl

@[simp] theorem S2490APlaceSelection_V :
    S2490APlaceSelection.V = S2490V := rfl

/-! ## 7. Filling the place block into a source sign-quotient record -/

namespace S2490AllPlacesFields

variable {l : PrimeGeFive} {A : InitialThetaArithmeticData l}

/-- The place block of any source sign-quotient record. -/
noncomputable def ofSourceSignQuotientData
    (S : SourceSignQuotientData A) : S2490AllPlacesFields A where
  V := S.V
  V_mod_bad := S.V_mod_bad
  V_mod_bad_odd_residue_characteristic :=
    S.V_mod_bad_odd_residue_characteristic
  V_mod_bad_nonempty := S.V_mod_bad_nonempty
  V_section := S.V_section
  V_eq_section := S.V_eq_section
  V_mod_bijection := S.V_mod_bijection
  V_place_comap := S.V_place_comap

/-- Write the eight actual place fields into a source sign-quotient record.
Every other field is unchanged; in particular cK, its signature and extension
identifications, and epsilon stay exactly as supplied. -/
noncomputable def fill (P : S2490AllPlacesFields A)
    (S : SourceSignQuotientData A) : SourceSignQuotientData A :=
  { S with
    V := P.V
    V_mod_bad := P.V_mod_bad
    V_mod_bad_odd_residue_characteristic :=
      P.V_mod_bad_odd_residue_characteristic
    V_mod_bad_nonempty := P.V_mod_bad_nonempty
    V_section := P.V_section
    V_eq_section := P.V_eq_section
    V_mod_bijection := P.V_mod_bijection
    V_place_comap := P.V_place_comap }

@[simp] theorem fill_V (P : S2490AllPlacesFields A)
    (S : SourceSignQuotientData A) :
    (P.fill S).V = P.V := rfl

@[simp] theorem fill_V_mod_bad (P : S2490AllPlacesFields A)
    (S : SourceSignQuotientData A) :
    (P.fill S).V_mod_bad = P.V_mod_bad := rfl

@[simp] theorem fill_V_mod_bad_odd_residue_characteristic
    (P : S2490AllPlacesFields A) (S : SourceSignQuotientData A) :
    (P.fill S).V_mod_bad_odd_residue_characteristic =
      P.V_mod_bad_odd_residue_characteristic := rfl

@[simp] theorem fill_V_mod_bad_nonempty
    (P : S2490AllPlacesFields A) (S : SourceSignQuotientData A) :
    (P.fill S).V_mod_bad_nonempty = P.V_mod_bad_nonempty := rfl

@[simp] theorem fill_V_section (P : S2490AllPlacesFields A)
    (S : SourceSignQuotientData A) :
    (P.fill S).V_section = P.V_section := rfl

@[simp] theorem fill_V_eq_section (P : S2490AllPlacesFields A)
    (S : SourceSignQuotientData A) :
    (P.fill S).V_eq_section = P.V_eq_section := rfl

@[simp] theorem fill_V_mod_bijection (P : S2490AllPlacesFields A)
    (S : SourceSignQuotientData A) :
    (P.fill S).V_mod_bijection = P.V_mod_bijection := rfl

@[simp] theorem fill_V_place_comap (P : S2490AllPlacesFields A)
    (S : SourceSignQuotientData A) :
    (P.fill S).V_place_comap = P.V_place_comap := rfl

/-- Filling the place block does not touch the K-side orbicurve cK. -/
@[simp] theorem fill_cK (P : S2490AllPlacesFields A)
    (S : SourceSignQuotientData A) :
    (P.fill S).cK = S.cK := rfl

/-- Filling the place block does not touch the cusp epsilon. -/
@[simp] theorem fill_epsilon (P : S2490AllPlacesFields A)
    (S : SourceSignQuotientData A) :
    (P.fill S).epsilon = S.epsilon := rfl

/-- Filling the place block does not touch the F-side orbicurve xF. -/
@[simp] theorem fill_xF (P : S2490AllPlacesFields A)
    (S : SourceSignQuotientData A) :
    (P.fill S).xF = S.xF := rfl

/-- Filling the place block does not touch the K-side orbicurve xK. -/
@[simp] theorem fill_xK (P : S2490AllPlacesFields A)
    (S : SourceSignQuotientData A) :
    (P.fill S).xK = S.xK := rfl

/-- Extracting the place block and filling it back is the identity. -/
theorem fill_ofSourceSignQuotientData (S : SourceSignQuotientData A) :
    (ofSourceSignQuotientData S).fill S = S := rfl

/-- Filling any place block and extracting it back returns that block. -/
theorem ofSourceSignQuotientData_fill (P : S2490AllPlacesFields A)
    (S : SourceSignQuotientData A) :
    ofSourceSignQuotientData (P.fill S) = P := by
  cases P
  rfl

end S2490AllPlacesFields

/-! ## 8. Axiom footprint -/

#print axioms S2490ThetaTower
#print axioms S2490ArithmeticData
#print axioms S2490RestrictionSection
#print axioms S2490RestrictionSection_comap_lift
#print axioms S2490RestrictionSection_lift_injective
#print axioms S2490ArithmeticSection_eq
#print axioms S2490ASection_eq
#print axioms S2490ArithmeticData_Fmod
#print axioms S2490A_Fmod
#print axioms S2490p3_three_mem
#print axioms S2490p3_residueCharacteristic
#print axioms S2490p3_odd
#print axioms S2490VModBad_odd
#print axioms S2490VModBad_nonempty
#print axioms S2490V_spec
#print axioms S2490VModBijection_symm_apply
#print axioms S2490VPlaceComap
#print axioms S2490PlaceFields
#print axioms S2490PlaceFieldsA
#print axioms S2490PlaceSelection
#print axioms S2490APlaceSelection
#print axioms S2490AllPlacesFields.ofSourceSignQuotientData
#print axioms S2490AllPlacesFields.fill
#print axioms S2490AllPlacesFields.fill_cK
#print axioms S2490AllPlacesFields.fill_epsilon
#print axioms S2490AllPlacesFields.fill_ofSourceSignQuotientData
#print axioms S2490AllPlacesFields.ofSourceSignQuotientData_fill

end LeanFormal.IUT.XiFPaper.S2490RestrictionSectionActual
end
