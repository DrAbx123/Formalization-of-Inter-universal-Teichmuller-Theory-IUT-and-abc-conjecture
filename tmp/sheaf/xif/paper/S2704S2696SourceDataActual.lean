import tmp.sheaf.xif.paper.S2696VbadActual
import tmp.sheaf.xif.paper.S2697Gaussian2161Actual
import tmp.sheaf.xif.paper.S2689SourceBadQAbsLogActual
import tmp.sheaf.xif.paper.S2681HcompMinimalInputActual

/-!
# S2704: the actual Definition 3.1 source datum over the S2696 bad set {5, 2161}

This file constructs, from actual data only (no sorry, axiom, native_decide,
True, or fabricated clause):

* the concrete two-element bad set {concreteGaussianFivePlace,
  S2696GaussianPlace2161} as a presentation of the current S2696
  S2696FourPlaceData interface (the two extra slots repeat the two actual
  places, so the underlying set is exactly the paper V_bad = {5, 2161});
* the Definition 3.1(b) bad-place reduction cards for that selection, from the
  actual split multiplicative reduction at the concrete five place
  (concreteGaussianFivePlace_hasSplitMultiplicativeReduction) and at the
  Gaussian place above 2161 (S2697_hasSplitMultiplicativeReductionAt2161),
  through the selection-generic BadPlaceReductionCards.ofSplitMultiplicative;
* the actual SourceDefinition31Data through d11EntryData, with the four
  remaining Definition 3.1 clauses and the five D9 compatibility pairs kept as
  explicit parameters (no clause is invented);
* the definitional identities badPlaces = Bad (S2696Selection ...) and
  reduction.qParameter = badPlaceQProxy;
* the alignment sourceBadQAbsLog S2696SourceData = S2696BadQAbsLog qVbad;
* the strict lower bound 2 log 5 < sourceBadQAbsLog S2696SourceData, from the
  S2689 pointwise bound log p_b <= |log q_b| at the two actual bad places;
* the conditional hcomp reduction: an alignment
  sourceBadQAbsLog S2696SourceData <= baseQTotalLogMagnitude T yields
  HcompBadQData T of S2681.

Boundary: the four Definition 3.1 clauses (torsion, orbicurve, sections, cusp)
and the five arithmetic-compatibility propositions are inputs, not proved here.
No source object is manufactured.  The real q-parameter of the reduction clause
is the completed-DVR proxy badPlaceQProxy, as in S1280; its identification
with the Tate q-parameter remains the recorded D4 boundary.
-/

noncomputable section
open scoped BigOperators

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 16000000

namespace LeanFormal.IUT.XiFPaper.S2704S2696SourceDataActual

open LeanFormal.IUT
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.XiFPaper.S1280SourceDefinition31Actual
open LeanFormal.IUT.XiFPaper.S2696VbadActual
open LeanFormal.IUT.XiFPaper.S2697Gaussian2161Actual
open LeanFormal.IUT.XiFPaper.S2689SourceBadQAbsLogActual
open LeanFormal.IUT.XiFPaper.S2681HcompMinimalInputActual
open LeanFormal.IUT.XiFPaper.BaseQLogVolumeActual

local instance s2704GaussianIrreducible :
    Fact (Irreducible (Polynomial.X ^ 2 - Polynomial.C (-1) : Polynomial ℚ)) :=
  ⟨gaussianPolynomial_irreducible⟩

/-! ## 1. The concrete two-place presentation of the S2696 bad data -/

/-- The concrete two-place presentation of the S2696 four-slot data: the two
extra slots repeat the actual five and 2161 places, so the bad set is exactly
the two-element set {concreteGaussianFivePlace, S2696GaussianPlace2161}. -/
def S2696TwoPlaceData : S2696FourPlaceData where
  p5a := concreteGaussianFivePlace
  p5b := concreteGaussianFivePlace
  p2161a := S2696GaussianPlace2161
  p2161b := S2696GaussianPlace2161
  odd5a := by
    rw [LeanFormal.IUT.IUTII.Frobenioid.Example36.concreteGaussianFivePlace_residueCharacteristic]
    exact ⟨2, by norm_num⟩
  odd5b := by
    rw [LeanFormal.IUT.IUTII.Frobenioid.Example36.concreteGaussianFivePlace_residueCharacteristic]
    exact ⟨2, by norm_num⟩
  odd2161a := by
    rw [S2696GaussianPlace2161_residueCharacteristic]
    exact ⟨1080, by norm_num⟩
  odd2161b := by
    rw [S2696GaussianPlace2161_residueCharacteristic]
    exact ⟨1080, by norm_num⟩

/-- The S2696 bad set of the two-place presentation is exactly
{concreteGaussianFivePlace, S2696GaussianPlace2161}. -/
@[simp] theorem S2696Vbad_twoPlace_eq :
    S2696Vbad S2696TwoPlaceData =
      ({concreteGaussianFivePlace, S2696GaussianPlace2161} :
        Set (NumberField.FinitePlace GaussianField)) := by
  ext p
  simp [S2696Vbad, S2696TwoPlaceData]

/-- The actual S2696 selection with V_bad = {5, 2161}. -/
abbrev S2696SelectionTwo (l : PrimeGeFive) :
    SourcePlaceSelection (S1280Arithmetic l) :=
  S2696Selection l S2696TwoPlaceData

instance S2696BadFintype (l : PrimeGeFive) :
    Fintype (Bad (S2696SelectionTwo l)) :=
  (S2696Vbad_finite S2696TwoPlaceData).fintype

/-! ## 2. The actual reduction cards at the two bad places -/

/-- Every F-place above a bad moduli place of the two-place selection is one of
the two actual places (the identity tower Fmod = F = Q(i)). -/
theorem S2696_bad_fibre_eq (l : PrimeGeFive)
    (w : NumberField.FinitePlace (S1280Arithmetic l).F)
    (hw : NumberFieldFinitePlace.comap (k := (S1280Arithmetic l).Fmod) w ∈
      (S2696SelectionTwo l).V_mod_bad) :
    w = concreteGaussianFivePlace ∨ w = S2696GaussianPlace2161 := by
  have hw' := hw
  rw [S1280_comap_eq_self l w] at hw'
  change w = concreteGaussianFivePlace ∨ w = concreteGaussianFivePlace ∨
    w = S2696GaussianPlace2161 ∨ w = S2696GaussianPlace2161 at hw'
  rcases hw' with rfl | rfl | rfl | rfl
  · exact Or.inl rfl
  · exact Or.inl rfl
  · exact Or.inr rfl
  · exact Or.inr rfl

/-- Definition 3.1(b) reduction cards for the actual two-place selection,
assembled from the actual split multiplicative reduction at the concrete five
place and at the Gaussian place above 2161. -/
theorem S2696ReductionCards (l : PrimeGeFive) :
    BadPlaceReductionCards (S2696SelectionTwo l) :=
  BadPlaceReductionCards.ofSplitMultiplicative (P := S2696SelectionTwo l)
    (fun w hw => by
      rcases S2696_bad_fibre_eq l w hw with rfl | rfl
      · exact concreteGaussianFivePlace_hasSplitMultiplicativeReduction l
      · exact S2697_hasSplitMultiplicativeReductionAt2161)

/-- The card unfolds to the expected pointwise split multiplicative data. -/
theorem S2696ReductionCards_split (l : PrimeGeFive)
    (w : NumberField.FinitePlace (S1280Arithmetic l).F)
    (hw : NumberFieldFinitePlace.comap (k := (S1280Arithmetic l).Fmod) w ∈
      (S2696SelectionTwo l).V_mod_bad) :
    (S1280Arithmetic l).curve.HasSplitMultiplicativeReductionAt w :=
  (S2696ReductionCards l).splitMultiplicativeReduction w hw

/-! ## 3. The actual Definition 3.1 source datum -/

/-- The actual Definition 3.1 source datum over the S2696 two-place selection.
The four remaining clauses are R; the five arithmetic-compatibility
propositions and proofs are explicit parameters. -/
noncomputable def S2696SourceData (l : PrimeGeFive)
    (R : S1280RemainingClauses l)
    (redCompat : Prop) (hredCompat : redCompat)
    (torCompat : Prop) (htorCompat : torCompat)
    (orbCompat : Prop) (horbCompat : orbCompat)
    (secCompat : Prop) (hsecCompat : secCompat)
    (cusCompat : Prop) (hcusCompat : cusCompat) :
    SourceDefinition31Data l :=
  Definition31PlacePartition.d11EntryData (P := S2696SelectionTwo l)
    (C := S2696ReductionCards l)
    R.torsion R.orbicurve R.sections R.cusp
    redCompat hredCompat torCompat htorCompat orbCompat horbCompat
    secCompat hsecCompat cusCompat hcusCompat

/-- The arithmetic component of the constructed source datum is the actual
S1280Arithmetic l. -/
@[simp] theorem S2696SourceData_arithmetic (l : PrimeGeFive)
    (R : S1280RemainingClauses l)
    (redCompat : Prop) (hredCompat : redCompat)
    (torCompat : Prop) (htorCompat : torCompat)
    (orbCompat : Prop) (horbCompat : orbCompat)
    (secCompat : Prop) (hsecCompat : secCompat)
    (cusCompat : Prop) (hcusCompat : cusCompat) :
    (S2696SourceData l R redCompat hredCompat torCompat htorCompat
      orbCompat horbCompat secCompat hsecCompat cusCompat hcusCompat).arithmetic =
        S1280Arithmetic l := rfl

/-- The bad-place index of the constructed source datum is exactly
Bad (S2696SelectionTwo l). -/
@[simp] theorem S2696SourceData_badPlaces (l : PrimeGeFive)
    (R : S1280RemainingClauses l)
    (redCompat : Prop) (hredCompat : redCompat)
    (torCompat : Prop) (htorCompat : torCompat)
    (orbCompat : Prop) (horbCompat : orbCompat)
    (secCompat : Prop) (hsecCompat : secCompat)
    (cusCompat : Prop) (hcusCompat : cusCompat) :
    (S2696SourceData l R redCompat hredCompat torCompat htorCompat
      orbCompat horbCompat secCompat hsecCompat cusCompat hcusCompat).badPlaces =
        Bad (S2696SelectionTwo l) := rfl

/-- The reduction component is the reduction-module assembly. -/
@[simp] theorem S2696SourceData_reduction (l : PrimeGeFive)
    (R : S1280RemainingClauses l)
    (redCompat : Prop) (hredCompat : redCompat)
    (torCompat : Prop) (htorCompat : torCompat)
    (orbCompat : Prop) (horbCompat : orbCompat)
    (secCompat : Prop) (hsecCompat : secCompat)
    (cusCompat : Prop) (hcusCompat : cusCompat) :
    (S2696SourceData l R redCompat hredCompat torCompat htorCompat
      orbCompat horbCompat secCompat hsecCompat cusCompat hcusCompat).reduction =
        toSourceReductionClause (S2696SelectionTwo l) (S2696ReductionCards l) := rfl

/-- The q-parameter of the reduction clause is definitionally the
completed-DVR proxy badPlaceQProxy. -/
@[simp] theorem S2696SourceData_qParameter (l : PrimeGeFive)
    (R : S1280RemainingClauses l)
    (redCompat : Prop) (hredCompat : redCompat)
    (torCompat : Prop) (htorCompat : torCompat)
    (orbCompat : Prop) (horbCompat : orbCompat)
    (secCompat : Prop) (hsecCompat : secCompat)
    (cusCompat : Prop) (hcusCompat : cusCompat)
    (b : Bad (S2696SelectionTwo l)) :
    (S2696SourceData l R redCompat hredCompat torCompat htorCompat
      orbCompat horbCompat secCompat hsecCompat cusCompat hcusCompat).reduction.qParameter b =
        badPlaceQProxy (S2696SelectionTwo l) b := rfl

/-! ## 4. The alignment with the S2696 bad-q absolute log -/

/-- The actual per-place S2696 bad-q absolute log, as a function on the actual
bad set. -/
noncomputable def qVbad (l : PrimeGeFive) :
    (p : NumberField.FinitePlace GaussianField) →
      p ∈ S2696Vbad S2696TwoPlaceData → Real :=
  fun p hp => |Real.log (badPlaceQProxy (S2696SelectionTwo l) ⟨p, hp⟩)|

/-- The S2696 bad-q absolute log is the per-place sum over the actual bad index. -/
theorem S2696BadQAbsLog_eq_sum (l : PrimeGeFive) :
    S2696BadQAbsLog S2696TwoPlaceData (qVbad l) =
      ∑ b : Bad (S2696SelectionTwo l),
        |Real.log (badPlaceQProxy (S2696SelectionTwo l) b)| := rfl

/-- The source bad-q absolute log of the constructed datum is the same per-place
sum over the actual bad index. -/
theorem S2696SourceData_sourceBadQAbsLog_eq_sum (l : PrimeGeFive)
    (R : S1280RemainingClauses l)
    (redCompat : Prop) (hredCompat : redCompat)
    (torCompat : Prop) (htorCompat : torCompat)
    (orbCompat : Prop) (horbCompat : orbCompat)
    (secCompat : Prop) (hsecCompat : secCompat)
    (cusCompat : Prop) (hcusCompat : cusCompat) :
    sourceBadQAbsLog
      (S2696SourceData l R redCompat hredCompat torCompat htorCompat
        orbCompat horbCompat secCompat hsecCompat cusCompat hcusCompat) =
      ∑ b : Bad (S2696SelectionTwo l),
        |Real.log (badPlaceQProxy (S2696SelectionTwo l) b)| := rfl

/-- **The alignment**: the actual source bad-q absolute log of the constructed
Definition 3.1 datum equals the S2696 bad-q absolute log S2696BadQAbsLog qVbad. -/
theorem S2696SourceData_sourceBadQAbsLog (l : PrimeGeFive)
    (R : S1280RemainingClauses l)
    (redCompat : Prop) (hredCompat : redCompat)
    (torCompat : Prop) (htorCompat : torCompat)
    (orbCompat : Prop) (horbCompat : orbCompat)
    (secCompat : Prop) (hsecCompat : secCompat)
    (cusCompat : Prop) (hcusCompat : cusCompat) :
    sourceBadQAbsLog
      (S2696SourceData l R redCompat hredCompat torCompat htorCompat
        orbCompat horbCompat secCompat hsecCompat cusCompat hcusCompat) =
      S2696BadQAbsLog S2696TwoPlaceData (qVbad l) := by
  rw [S2696SourceData_sourceBadQAbsLog_eq_sum, S2696BadQAbsLog_eq_sum]

/-! ## 5. The two actual bad indices -/

/-- The 2161 place as a finite place of the actual arithmetic field
S1280Arithmetic l. -/
abbrev S2696Place2161Arith (l : PrimeGeFive) :
    NumberField.FinitePlace (S1280Arithmetic l).Fmod :=
  S2696GaussianPlace2161

theorem S2696Place2161Arith_residueCharacteristic (l : PrimeGeFive) :
    NumberFieldFinitePlace.residueCharacteristic (S2696Place2161Arith l) = 2161 :=
  S2696GaussianPlace2161_residueCharacteristic

theorem S2696BadFive_mem (l : PrimeGeFive) :
    S1280Place l ∈ (S2696SelectionTwo l).V_mod_bad := by
  change S1280Place l ∈ S2696Vbad S2696TwoPlaceData
  exact Or.inl rfl

theorem S2696Bad2161_mem (l : PrimeGeFive) :
    S2696Place2161Arith l ∈ (S2696SelectionTwo l).V_mod_bad := by
  change S2696Place2161Arith l ∈ S2696Vbad S2696TwoPlaceData
  exact Or.inr (Or.inr (Or.inl rfl))

/-- The actual bad index at the concrete five place. -/
def S2696BadFive (l : PrimeGeFive) : Bad (S2696SelectionTwo l) :=
  ⟨S1280Place l, S2696BadFive_mem l⟩

/-- The actual bad index at the Gaussian place above 2161. -/
def S2696Bad2161 (l : PrimeGeFive) : Bad (S2696SelectionTwo l) :=
  ⟨S2696Place2161Arith l, S2696Bad2161_mem l⟩

/-- The two actual bad indices are distinct: their residue characteristics are
5 and 2161. -/
theorem S2696BadFive_ne_2161 (l : PrimeGeFive) :
    S2696BadFive l ≠ S2696Bad2161 l := by
  intro h
  have hval : S1280Place l = S2696Place2161Arith l := congrArg Subtype.val h
  have h5 := S1280Place_residueCharacteristic l
  have h2161 := S2696Place2161Arith_residueCharacteristic l
  rw [hval] at h5
  rw [h5] at h2161
  norm_num at h2161

/-- The five-place summand is at least log 5, by the S2689 pointwise
residue-characteristic bound. -/
theorem S2696_log_five_le (l : PrimeGeFive) :
    Real.log 5 ≤
      |Real.log (badPlaceQProxy (S2696SelectionTwo l) (S2696BadFive l))| := by
  have h := log_residueCharacteristic_le_abs_log_badPlaceQProxy
    (S2696SelectionTwo l) (S2696BadFive l)
  have hchar : ((NumberFieldFinitePlace.residueCharacteristic
      (S2696BadFive l).1 : ℕ) : ℝ) = 5 := by
    rw [show (S2696BadFive l).1 = S1280Place l from rfl,
      S1280Place_residueCharacteristic l]
    norm_num
  simpa [hchar] using h

/-- The 2161-place summand is at least log 2161, by the S2689 pointwise
residue-characteristic bound. -/
theorem S2696_log_2161_le (l : PrimeGeFive) :
    Real.log 2161 ≤
      |Real.log (badPlaceQProxy (S2696SelectionTwo l) (S2696Bad2161 l))| := by
  have h := log_residueCharacteristic_le_abs_log_badPlaceQProxy
    (S2696SelectionTwo l) (S2696Bad2161 l)
  have hchar : ((NumberFieldFinitePlace.residueCharacteristic
      (S2696Bad2161 l).1 : ℕ) : ℝ) = 2161 := by
    rw [show (S2696Bad2161 l).1 = S2696Place2161Arith l from rfl,
      S2696Place2161Arith_residueCharacteristic l]
    norm_num
  simpa [hchar] using h

/-- The strict 2 log 5 lower bound for the S2696 bad-q absolute log at the
actual two-place set. -/
theorem two_log5_lt_S2696BadQAbsLog (l : PrimeGeFive) :
    2 * Real.log 5 < S2696BadQAbsLog S2696TwoPlaceData (qVbad l) := by
  rw [S2696BadQAbsLog_eq_sum]
  have hne := S2696BadFive_ne_2161 l
  have hsum := two_terms_le_sum
    (fun b : Bad (S2696SelectionTwo l) =>
      |Real.log (badPlaceQProxy (S2696SelectionTwo l) b)|)
    (fun b => abs_nonneg _) hne
  have h5 := S2696_log_five_le l
  have h2161 := S2696_log_2161_le l
  have hlt : Real.log (5 : ℝ) < Real.log 2161 :=
    Real.log_lt_log (by norm_num) (by norm_num)
  linarith

/-- The strict 2 log 5 lower bound for the actual source bad-q absolute log of
the constructed Definition 3.1 datum. -/
theorem two_log5_lt_sourceBadQAbsLog (l : PrimeGeFive)
    (R : S1280RemainingClauses l)
    (redCompat : Prop) (hredCompat : redCompat)
    (torCompat : Prop) (htorCompat : torCompat)
    (orbCompat : Prop) (horbCompat : orbCompat)
    (secCompat : Prop) (hsecCompat : secCompat)
    (cusCompat : Prop) (hcusCompat : cusCompat) :
    2 * Real.log 5 <
      sourceBadQAbsLog
        (S2696SourceData l R redCompat hredCompat torCompat htorCompat
          orbCompat horbCompat secCompat hsecCompat cusCompat hcusCompat) := by
  rw [S2696SourceData_sourceBadQAbsLog]
  exact two_log5_lt_S2696BadQAbsLog l

/-! ## 6. Conditional hcomp -/

/-- **Conditional hcomp.**  If the actual source bad-q absolute log of the
constructed Definition 3.1 datum is aligned with the native base-q total
magnitude (halign), then the S2681 bad-q datum HcompBadQData T holds. -/
theorem hcompBadQData_of_halign
    {l : PrimeGeFive} {T : SourceNativeInitialThetaData.{0} l}
    [Fintype (Bad (nativePlaceSelection T))]
    (R : S1280RemainingClauses l)
    (redCompat : Prop) (hredCompat : redCompat)
    (torCompat : Prop) (htorCompat : torCompat)
    (orbCompat : Prop) (horbCompat : orbCompat)
    (secCompat : Prop) (hsecCompat : secCompat)
    (cusCompat : Prop) (hcusCompat : cusCompat)
    (halign : sourceBadQAbsLog
      (S2696SourceData l R redCompat hredCompat torCompat htorCompat
        orbCompat horbCompat secCompat hsecCompat cusCompat hcusCompat) ≤
      baseQTotalLogMagnitude T) :
    HcompBadQData T := by
  unfold HcompBadQData
  have h := le_of_lt (two_log5_lt_sourceBadQAbsLog l R redCompat hredCompat
    torCompat htorCompat orbCompat horbCompat secCompat hsecCompat cusCompat hcusCompat)
  linarith

/-! ## 7. Axiom audit -/

#print axioms S2696Vbad_twoPlace_eq
#print axioms S2696_bad_fibre_eq
#print axioms S2696ReductionCards
#print axioms S2696SourceData_badPlaces
#print axioms S2696SourceData_qParameter
#print axioms S2696BadQAbsLog_eq_sum
#print axioms S2696SourceData_sourceBadQAbsLog_eq_sum
#print axioms S2696SourceData_sourceBadQAbsLog
#print axioms S2696BadFive_ne_2161
#print axioms S2696_log_five_le
#print axioms S2696_log_2161_le
#print axioms two_log5_lt_S2696BadQAbsLog
#print axioms two_log5_lt_sourceBadQAbsLog
#print axioms hcompBadQData_of_halign

end LeanFormal.IUT.XiFPaper.S2704S2696SourceDataActual

end
