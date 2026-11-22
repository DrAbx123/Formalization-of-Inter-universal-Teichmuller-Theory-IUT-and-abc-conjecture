import tmp.sheaf.xif.paper.S2696VbadActual
import tmp.sheaf.xif.paper.S2689SourceBadQAbsLogActual
import tmp.sheaf.xif.paper.S1280SourceDefinition31Actual

/-!
# S2699: the S2696 bad-q absolute log as an actual source-places sum

Layer: source q-side. Consumer: the hcomp bad-q data of
S2681HcompMinimalInputActual (HcompSourceBadQData), through the S2689 per-place
lower bound.

## State of the S2696 interface

`S2696VbadActual` currently carries the four-place interface
`S2696FourPlaceData` with places `p5a p5b p2161a p2161b` (and oddness
proofs), `S2696Vbad D`, `S2696Selection l D`, `S2696BadQAbsLog D`.  The
older two-place interface `S2696Vbad l` is no longer present.  This file is
written against the current four-place interface and instantiates it at the
concrete two-place datum `S2696TwoPlaceData` (both five slots are
`concreteGaussianFivePlace`, both 2161 slots are
`S2696GaussianPlace2161`), whose bad set is exactly the actual two-place set.

## What is proved here

* `qVbad l D` is the actual per-place function on the bad set
  `S2696Vbad D`: `qVbad l D p hp = |log (badPlaceQProxy (S2696Selection l D) ⟨p, hp⟩)|`.
* `S2696BadQAbsLog_eq_sum_badPlaces`: `S2696BadQAbsLog D (qVbad l D)` is the
  sum over the actual bad-place index `Bad (S2696Selection l D)` (rfl).
* `sourceBadQAbsLog_d11EntryData_eq_sum_badPlaces`: for any source selection
  `P` and any Definition 3.1 data assembled by the generic `d11EntryData`,
  `sourceBadQAbsLog` is exactly the per-place sum of `badPlaceQProxy P` (rfl).
  This is the bridge to the actual source scalar;
  `S2696BadQAbsLog_eq_sourceBadQAbsLog` specialises it to the S2696 selection
  for every `S2696FourPlaceData`.
* `two_log5_lt_S2696BadQAbsLog_of_residue`: the strict two-place lower bound
  from explicit residue-characteristic data for one five place and one 2161
  place and their distinctness.
* `two_log5_lt_S2696BadQAbsLog`: the unconditional strict bound
  `2 * log 5 < S2696BadQAbsLog S2696TwoPlaceData (qVbad l S2696TwoPlaceData)`
  for the concrete two-place datum, using
  `concreteGaussianFivePlace_residueCharacteristic = 5` and
  `S2696GaussianPlace2161_residueCharacteristic = 2161`.
* `S2696TwoPlaceBadQAbsLog_eq_five_add_2161`: the sum splits into the actual
  five-place term plus the actual 2161-place term.

## Exact missing actual data (no fake)

`SourceDefinition31Data l` cannot be constructed from the S2696 selection in
this tree: `d11EntryData` still needs `BadPlaceReductionCards` and the four
Definition 3.1 clauses (torsion, orbicurve, sections, cusp) with their five
compatibility pairs; the D5 torsion clause is the open source datum recorded
in S1280SourceDefinition31Actual.  The bridge is therefore stated with those
components as explicit hypotheses, and no source datum is fabricated.  No
`sorry`, axiom, `native_decide` or `True` is used.
-/

noncomputable section
open scoped BigOperators

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 16000000

namespace LeanFormal.IUT.XiFPaper.S2699VbadSumActual

open LeanFormal.IUT
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.XiFPaper.S1280SourceDefinition31Actual
open LeanFormal.IUT.XiFPaper.S2696VbadActual
open LeanFormal.IUT.XiFPaper.S2689SourceBadQAbsLogActual

/-- The Gaussian field is `AdjoinRoot (X^2 + 1)`; the irreducibility fact is
needed to synthesize its field structure, exactly as in the S2696/S2689
sources. -/
local instance s2699GaussianIrreducible :
    Fact (Irreducible (Polynomial.X ^ 2 - Polynomial.C (-1) : Polynomial ℚ)) :=
  ⟨gaussianPolynomial_irreducible⟩

/-- The actual S2696 per-place bad-q absolute log on the bad set of a
four-place datum `D`. -/
noncomputable def qVbad (l : PrimeGeFive) (D : S2696FourPlaceData) :
    (p : NumberField.FinitePlace GaussianField) → p ∈ S2696Vbad D → Real :=
  fun p hp => |Real.log (badPlaceQProxy (S2696Selection l D) ⟨p, hp⟩)|

/-- The actual S2696 bad-q absolute log is the per-place sum over the actual
bad-place index `Bad (S2696Selection l D)`.  The displayed `letI` is the
finiteness instance `(S2696Vbad_finite D).fintype` used by
`S2696BadQAbsLog` itself; there is no global finite instance on the
subtype. -/
theorem S2696BadQAbsLog_eq_sum_badPlaces (l : PrimeGeFive)
    (D : S2696FourPlaceData) :
    S2696BadQAbsLog D (qVbad l D) =
      letI : Fintype (Bad (S2696Selection l D)) := (S2696Vbad_finite D).fintype
      ∑ b : Bad (S2696Selection l D),
        |Real.log (badPlaceQProxy (S2696Selection l D) b)| := by
  rfl

/-! ## The four explicit data places -/

theorem S2696Vbad_mem_five_a (D : S2696FourPlaceData) :
    D.p5a ∈ S2696Vbad D := Or.inl rfl

theorem S2696Vbad_mem_five_b (D : S2696FourPlaceData) :
    D.p5b ∈ S2696Vbad D := Or.inr (Or.inl rfl)

theorem S2696Vbad_mem_2161_a (D : S2696FourPlaceData) :
    D.p2161a ∈ S2696Vbad D := Or.inr (Or.inr (Or.inl rfl))

theorem S2696Vbad_mem_2161_b (D : S2696FourPlaceData) :
    D.p2161b ∈ S2696Vbad D := Or.inr (Or.inr (Or.inr rfl))

/-! ## Per-place lower bounds and the conditional two-place bound -/

/-- The five-place summand is at least `log 5` once the residue
characteristic of `D.p5a` is 5 (S2689 pointwise bound). -/
theorem log_five_le_qVbad (l : PrimeGeFive) (D : S2696FourPlaceData)
    (h : NumberFieldFinitePlace.residueCharacteristic D.p5a = 5) :
    Real.log 5 ≤ qVbad l D D.p5a (S2696Vbad_mem_five_a D) := by
  have hb := log_residueCharacteristic_le_abs_log_badPlaceQProxy
    (S2696Selection l D)
    (⟨D.p5a, S2696Vbad_mem_five_a D⟩ : Bad (S2696Selection l D))
  have hb' : Real.log ((NumberFieldFinitePlace.residueCharacteristic D.p5a : ℕ) : ℝ) ≤
      |Real.log (badPlaceQProxy (S2696Selection l D)
        ⟨D.p5a, S2696Vbad_mem_five_a D⟩)| := hb
  have hchar : ((NumberFieldFinitePlace.residueCharacteristic D.p5a : ℕ) : ℝ) =
      (5 : ℝ) := by
    rw [h]
    norm_num
  rw [hchar] at hb'
  simpa [qVbad] using hb'

/-- The 2161-place summand is at least `log 2161` once the residue
characteristic of `D.p2161a` is 2161 (S2689 pointwise bound). -/
theorem log_2161_le_qVbad (l : PrimeGeFive) (D : S2696FourPlaceData)
    (h : NumberFieldFinitePlace.residueCharacteristic D.p2161a = 2161) :
    Real.log 2161 ≤ qVbad l D D.p2161a (S2696Vbad_mem_2161_a D) := by
  have hb := log_residueCharacteristic_le_abs_log_badPlaceQProxy
    (S2696Selection l D)
    (⟨D.p2161a, S2696Vbad_mem_2161_a D⟩ : Bad (S2696Selection l D))
  have hb' : Real.log ((NumberFieldFinitePlace.residueCharacteristic D.p2161a : ℕ) : ℝ) ≤
      |Real.log (badPlaceQProxy (S2696Selection l D)
        ⟨D.p2161a, S2696Vbad_mem_2161_a D⟩)| := hb
  have hchar :
      ((NumberFieldFinitePlace.residueCharacteristic D.p2161a : ℕ) : ℝ) =
        (2161 : ℝ) := by
    rw [h]
    norm_num
  rw [hchar] at hb'
  simpa [qVbad] using hb'

/-- **Conditional strict two-log-5 lower bound.**  If one five place and one
2161 place of the datum have residue characteristics 5 and 2161 and are
distinct, then `2 * log 5` is strictly below the actual bad-q absolute
log. -/
theorem two_log5_lt_S2696BadQAbsLog_of_residue (l : PrimeGeFive)
    (D : S2696FourPlaceData)
    (h5 : NumberFieldFinitePlace.residueCharacteristic D.p5a = 5)
    (h2161 : NumberFieldFinitePlace.residueCharacteristic D.p2161a = 2161)
    (hne : D.p5a ≠ D.p2161a) :
    2 * Real.log 5 < S2696BadQAbsLog D (qVbad l D) := by
  classical
  letI : Fintype (Bad (S2696Selection l D)) := (S2696Vbad_finite D).fintype
  have h5' : Real.log 5 ≤
      |Real.log (badPlaceQProxy (S2696Selection l D)
        ⟨D.p5a, S2696Vbad_mem_five_a D⟩)| := by
    have h := log_five_le_qVbad l D h5
    simpa [qVbad] using h
  have h2161' : Real.log 2161 ≤
      |Real.log (badPlaceQProxy (S2696Selection l D)
        ⟨D.p2161a, S2696Vbad_mem_2161_a D⟩)| := by
    have h := log_2161_le_qVbad l D h2161
    simpa [qVbad] using h
  have hlt : Real.log (5 : ℝ) < Real.log (2161 : ℝ) :=
    Real.log_lt_log (by norm_num) (by norm_num)
  have hne' :
      (⟨D.p5a, S2696Vbad_mem_five_a D⟩ : Bad (S2696Selection l D)) ≠
        ⟨D.p2161a, S2696Vbad_mem_2161_a D⟩ := by
    intro h
    exact hne (congrArg Subtype.val h)
  have hsum := two_terms_le_sum
    (fun b : Bad (S2696Selection l D) =>
      |Real.log (badPlaceQProxy (S2696Selection l D) b)|)
    (fun b => abs_nonneg _) hne'
  have hsum' :
      |Real.log (badPlaceQProxy (S2696Selection l D)
          ⟨D.p5a, S2696Vbad_mem_five_a D⟩)| +
        |Real.log (badPlaceQProxy (S2696Selection l D)
          ⟨D.p2161a, S2696Vbad_mem_2161_a D⟩)| ≤
      ∑ b : Bad (S2696Selection l D),
        |Real.log (badPlaceQProxy (S2696Selection l D) b)| := hsum
  rw [S2696BadQAbsLog_eq_sum_badPlaces]
  change 2 * Real.log 5 <
    (∑ b : Bad (S2696Selection l D),
      |Real.log (badPlaceQProxy (S2696Selection l D) b)|)
  linarith

/-! ## The concrete actual two-place datum -/

/-- The concrete two-place datum: both five slots are the concrete Gaussian
five place, both 2161 slots are the actual Gaussian place above 2161.  Its bad
set is the actual two-place set `{concreteGaussianFivePlace,
S2696GaussianPlace2161}`. -/
noncomputable def S2696TwoPlaceData : S2696FourPlaceData where
  p5a := concreteGaussianFivePlace
  p5b := concreteGaussianFivePlace
  p2161a := S2696GaussianPlace2161
  p2161b := S2696GaussianPlace2161
  odd5a := by
    rw [LeanFormal.IUT.IUTII.Frobenioid.Example36.concreteGaussianFivePlace_residueCharacteristic]
    norm_num
  odd5b := by
    rw [LeanFormal.IUT.IUTII.Frobenioid.Example36.concreteGaussianFivePlace_residueCharacteristic]
    norm_num
  odd2161a := by
    rw [S2696GaussianPlace2161_residueCharacteristic]
    norm_num
  odd2161b := by
    rw [S2696GaussianPlace2161_residueCharacteristic]
    norm_num

/-- The bad set of the concrete two-place datum is exactly the actual
two-place set. -/
theorem S2696TwoPlaceData_V_bad :
    S2696Vbad S2696TwoPlaceData =
      ({concreteGaussianFivePlace, S2696GaussianPlace2161} :
        Set (NumberField.FinitePlace GaussianField)) := by
  ext p
  simp [S2696Vbad, S2696TwoPlaceData]

/-- The two actual places are distinct: their residue characteristics are 5
and 2161. -/
theorem five_ne_2161 : concreteGaussianFivePlace ≠ S2696GaussianPlace2161 := by
  intro h
  have hfive :=
    LeanFormal.IUT.IUTII.Frobenioid.Example36.concreteGaussianFivePlace_residueCharacteristic
  have h2161 := S2696GaussianPlace2161_residueCharacteristic
  rw [h] at hfive
  rw [hfive] at h2161
  norm_num at h2161

/-- **The unconditional strict two-log-5 lower bound for the actual two-place
S2696 data.** -/
theorem two_log5_lt_S2696BadQAbsLog (l : PrimeGeFive) :
    2 * Real.log 5 <
      S2696BadQAbsLog S2696TwoPlaceData (qVbad l S2696TwoPlaceData) := by
  refine two_log5_lt_S2696BadQAbsLog_of_residue l S2696TwoPlaceData ?_ ?_ ?_
  · exact
      LeanFormal.IUT.IUTII.Frobenioid.Example36.concreteGaussianFivePlace_residueCharacteristic
  · exact S2696GaussianPlace2161_residueCharacteristic
  · exact five_ne_2161

/-! ## The two-term split for the concrete datum -/

/-- The actual S2696 two-place bad-q absolute log splits into the five-place
term plus the 2161-place term. -/
theorem S2696TwoPlaceBadQAbsLog_eq_five_add_2161 (l : PrimeGeFive) :
    S2696BadQAbsLog S2696TwoPlaceData (qVbad l S2696TwoPlaceData) =
      qVbad l S2696TwoPlaceData concreteGaussianFivePlace (Or.inl rfl) +
        qVbad l S2696TwoPlaceData S2696GaussianPlace2161
          (Or.inr (Or.inr (Or.inl rfl))) := by
  classical
  rw [S2696BadQAbsLog_eq_sum_badPlaces]
  letI : Fintype (Bad (S2696Selection l S2696TwoPlaceData)) :=
    (S2696Vbad_finite S2696TwoPlaceData).fintype
  have hne :
      (⟨concreteGaussianFivePlace, (Or.inl rfl : concreteGaussianFivePlace ∈
          S2696Vbad S2696TwoPlaceData)⟩ :
          Bad (S2696Selection l S2696TwoPlaceData)) ≠
        ⟨S2696GaussianPlace2161, (Or.inr (Or.inr (Or.inl rfl)) :
          S2696GaussianPlace2161 ∈ S2696Vbad S2696TwoPlaceData)⟩ := by
    intro h
    exact five_ne_2161 (congrArg Subtype.val h)
  have huniv :
      (Finset.univ : Finset (Bad (S2696Selection l S2696TwoPlaceData))) =
        {⟨concreteGaussianFivePlace, (Or.inl rfl :
            concreteGaussianFivePlace ∈ S2696Vbad S2696TwoPlaceData)⟩,
          ⟨S2696GaussianPlace2161, (Or.inr (Or.inr (Or.inl rfl)) :
            S2696GaussianPlace2161 ∈ S2696Vbad S2696TwoPlaceData)⟩} := by
    ext b
    simp only [Finset.mem_univ, true_iff, Finset.mem_insert,
      Finset.mem_singleton]
    rcases b with ⟨p, hp⟩
    have hp' : p ∈ S2696Vbad S2696TwoPlaceData := hp
    rw [S2696TwoPlaceData_V_bad] at hp'
    rcases hp' with rfl | rfl
    · exact Or.inl (Subtype.ext rfl)
    · exact Or.inr (Subtype.ext rfl)
  rw [huniv, Finset.sum_pair hne]
  rfl

/-! ## The rfl bridge to the actual source scalar -/

/-- **The definitional bridge.** For any actual source selection `P` and any
Definition 3.1 data assembled by the generic `d11EntryData` from `P`, the
source bad-q absolute log is exactly the per-place sum of the assembled
`badPlaceQProxy` values.  This is a definitional equality: `d11EntryData`
sets `badPlaces := Bad P`, `badFinite := inferInstance`, and
`qParameter := fun b => badPlaceQProxy P b`. -/
theorem sourceBadQAbsLog_d11EntryData_eq_sum_badPlaces
    {l : PrimeGeFive} {A : InitialThetaArithmeticData l}
    (P : SourcePlaceSelection A) [Fintype (Bad P)]
    (C : BadPlaceReductionCards P)
    (T : Theorem311Source.SourceTorsionClause l)
    (O : Theorem311Source.SourceOrbicurveClause)
    (Se : Theorem311Source.SourceSectionClause)
    (Cu : Theorem311Source.SourceCuspClause)
    (redCompat : Prop) (hredCompat : redCompat)
    (torCompat : Prop) (htorCompat : torCompat)
    (orbCompat : Prop) (horbCompat : orbCompat)
    (secCompat : Prop) (hsecCompat : secCompat)
    (cusCompat : Prop) (hcusCompat : cusCompat) :
    Theorem311Source.sourceBadQAbsLog
      (Definition31PlacePartition.d11EntryData P C T O Se Cu
        redCompat hredCompat torCompat htorCompat orbCompat horbCompat
        secCompat hsecCompat cusCompat hcusCompat) =
      ∑ b : Bad P, |Real.log (badPlaceQProxy P b)| := by
  rfl

/-- The explicit candidate source datum over a concrete S2696 four-place
datum, assembled through `d11EntryData` from the (hypothesised) bad-place
reduction cards and the four remaining Definition 3.1 clauses.  No inhabitant
of the component arguments is constructed in this file. -/
noncomputable def S2696SourceDataCandidate (l : PrimeGeFive)
    (D : S2696FourPlaceData)
    (C : BadPlaceReductionCards (S2696Selection l D))
    (T : Theorem311Source.SourceTorsionClause l)
    (O : Theorem311Source.SourceOrbicurveClause)
    (Se : Theorem311Source.SourceSectionClause)
    (Cu : Theorem311Source.SourceCuspClause)
    (redCompat : Prop) (hredCompat : redCompat)
    (torCompat : Prop) (htorCompat : torCompat)
    (orbCompat : Prop) (horbCompat : orbCompat)
    (secCompat : Prop) (hsecCompat : secCompat)
    (cusCompat : Prop) (hcusCompat : cusCompat) :
    Theorem311Source.SourceDefinition31Data l :=
  @Definition31PlacePartition.d11EntryData l (S1280Arithmetic l)
    (S2696Selection l D) ((S2696Vbad_finite D).fintype) C T O Se Cu
    redCompat hredCompat torCompat htorCompat orbCompat horbCompat
    secCompat hsecCompat cusCompat hcusCompat

/-- **The S2696 bridge.** The actual S2696 bad-q absolute log is the actual
source scalar `sourceBadQAbsLog` of the candidate Definition 3.1 source datum
assembled from the S2696 selection by `d11EntryData`. -/
theorem S2696BadQAbsLog_eq_sourceBadQAbsLog (l : PrimeGeFive)
    (D : S2696FourPlaceData)
    (C : BadPlaceReductionCards (S2696Selection l D))
    (T : Theorem311Source.SourceTorsionClause l)
    (O : Theorem311Source.SourceOrbicurveClause)
    (Se : Theorem311Source.SourceSectionClause)
    (Cu : Theorem311Source.SourceCuspClause)
    (redCompat : Prop) (hredCompat : redCompat)
    (torCompat : Prop) (htorCompat : torCompat)
    (orbCompat : Prop) (horbCompat : orbCompat)
    (secCompat : Prop) (hsecCompat : secCompat)
    (cusCompat : Prop) (hcusCompat : cusCompat) :
    S2696BadQAbsLog D (qVbad l D) =
      Theorem311Source.sourceBadQAbsLog
        (S2696SourceDataCandidate l D C T O Se Cu
          redCompat hredCompat torCompat htorCompat orbCompat horbCompat
          secCompat hsecCompat cusCompat hcusCompat) := by
  rw [S2696BadQAbsLog_eq_sum_badPlaces]
  letI : Fintype (Bad (S2696Selection l D)) := (S2696Vbad_finite D).fintype
  exact (sourceBadQAbsLog_d11EntryData_eq_sum_badPlaces
    (S2696Selection l D) C T O Se Cu
    redCompat hredCompat torCompat htorCompat orbCompat horbCompat
    secCompat hsecCompat cusCompat hcusCompat).symm

/-- The concrete two-place instance of the bridge: the actual two-place S2696
bad-q absolute log is the source scalar of the candidate source datum over
`S2696TwoPlaceData`. -/
theorem S2696TwoPlaceBadQAbsLog_eq_sourceBadQAbsLog (l : PrimeGeFive)
    (C : BadPlaceReductionCards (S2696Selection l S2696TwoPlaceData))
    (T : Theorem311Source.SourceTorsionClause l)
    (O : Theorem311Source.SourceOrbicurveClause)
    (Se : Theorem311Source.SourceSectionClause)
    (Cu : Theorem311Source.SourceCuspClause)
    (redCompat : Prop) (hredCompat : redCompat)
    (torCompat : Prop) (htorCompat : torCompat)
    (orbCompat : Prop) (horbCompat : orbCompat)
    (secCompat : Prop) (hsecCompat : secCompat)
    (cusCompat : Prop) (hcusCompat : cusCompat) :
    S2696BadQAbsLog S2696TwoPlaceData (qVbad l S2696TwoPlaceData) =
      Theorem311Source.sourceBadQAbsLog
        (S2696SourceDataCandidate l S2696TwoPlaceData C T O Se Cu
          redCompat hredCompat torCompat htorCompat orbCompat horbCompat
          secCompat hsecCompat cusCompat hcusCompat) :=
  S2696BadQAbsLog_eq_sourceBadQAbsLog l S2696TwoPlaceData C T O Se Cu
    redCompat hredCompat torCompat htorCompat orbCompat horbCompat
    secCompat hsecCompat cusCompat hcusCompat

/-! ## Axiom audit -/

#print axioms qVbad
#print axioms S2696BadQAbsLog_eq_sum_badPlaces
#print axioms S2696Vbad_mem_five_a
#print axioms S2696Vbad_mem_2161_a
#print axioms log_five_le_qVbad
#print axioms log_2161_le_qVbad
#print axioms two_log5_lt_S2696BadQAbsLog_of_residue
#print axioms S2696TwoPlaceData
#print axioms S2696TwoPlaceData_V_bad
#print axioms five_ne_2161
#print axioms two_log5_lt_S2696BadQAbsLog
#print axioms S2696TwoPlaceBadQAbsLog_eq_five_add_2161
#print axioms sourceBadQAbsLog_d11EntryData_eq_sum_badPlaces
#print axioms S2696SourceDataCandidate
#print axioms S2696BadQAbsLog_eq_sourceBadQAbsLog
#print axioms S2696TwoPlaceBadQAbsLog_eq_sourceBadQAbsLog

end LeanFormal.IUT.XiFPaper.S2699VbadSumActual
end
