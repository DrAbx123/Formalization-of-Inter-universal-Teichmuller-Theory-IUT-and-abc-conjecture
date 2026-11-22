/-
Copyright (c) 2026 LeanFormal contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import tmp.sheaf.xif.paper.S2696VbadActual
import tmp.sheaf.xif.paper.S2689SourceBadQAbsLogActual
import tmp.sheaf.xif.paper.S2681HcompMinimalInputActual

/-!
# S2703: the actual S2696 V_bad bad-q total, its 2 log 5 bound, hcomp, and the
exact source-data bridge gap

Layer: source q-side.  Consumer: the hcomp bad-q data of
S2681HcompMinimalInputActual (`HcompBadQData`), through the S2689 per-place
lower bound.

## Actual interface read from the tree

`S2696VbadActual` is *not* parameterized by `l` alone: the actual bad set is

  `S2696Vbad (D : S2696FourPlaceData) = {D.p5a, D.p5b, D.p2161a, D.p2161b}`,

`S2696Selection l D : SourcePlaceSelection (S1280Arithmetic l)`, and
`S2696BadQAbsLog D q = sum over {p // p in S2696Vbad D} of q p p.2`.
This file therefore states everything for an arbitrary `D : S2696FourPlaceData`
(no residue-characteristic information is invented for the four abstract
places), and instantiates at the concrete two-element datum
`S2703TwoPlaceData = {5, 5, 2161, 2161}` whose bad set is exactly
`{concreteGaussianFivePlace, S2696GaussianPlace2161}`.

## What is proved

* `qVbad l D p hp = |log (badPlaceQProxy (S2696Selection l D) <p, hp>)|` is the
  actual per-place function on the actual bad set.
* `S2696BadQAbsLog_eq_badPlaces_sum`: `S2696BadQAbsLog D (qVbad l D)` is the
  per-place sum over the actual bad-place index `Bad (S2696Selection l D)`
  (definitional equality, no singleton substitution).
* `sourceBadQAbsLog_vbad l D := S2696BadQAbsLog D (qVbad l D)`, and it is
  nonnegative.
* `abs_log_proxy_add_le_sourceBadQAbsLog_vbad`: two distinct bad indices are
  bounded by the total; the S2689 pointwise bound
  `log (residueCharacteristic b) <= |log (badPlaceQProxy P b)|` turns residue
  characteristics 5 and 2161 into the two-place bound.  General form:
  `Real.log 5 + Real.log 2161 <= sourceBadQAbsLog_vbad l D` whenever two
  distinct bad indices have residue characteristics 5 and 2161; hence
  `2 * log 5 < sourceBadQAbsLog_vbad l D`.
  Concrete form at `S2703TwoPlaceData`: unconditional, including the exact
  two-term decomposition `S2696BadQAbsLog = five-term + 2161-term`.
* `hcompBadQData_of_sourceBadQAbsLog_vbad`: the conditional hcomp step
  `(halign : sourceBadQAbsLog_vbad l D <= baseQTotalLogMagnitude T) ->
  HcompBadQData T`, with the numeric residual discharged by `2 log 5 < ...`.
* The exact rfl bridge `sourceBadQAbsLog (d11EntryData P C T O Se Cu ...) =
  sum_b |log (badPlaceQProxy P b)|` for any selection `P`;
  `S2703SourceDataCandidate` is the `d11EntryData` instance at
  `P = S2696Selection l D`, and `sourceBadQAbsLog_candidate_eq_vbad` is the
  definitional identification of its source scalar with the S2696 V_bad total.

## The exact source-data gap (no fake)

`SourceDefinition31Data l` over `Bad (S2696Selection l D)` is *not* constructed
in the tree:

* `S1280SourceDefinition31Actual.S1280SourceData_of_remaining` is hardwired to
  `S1280Selection` (the synthetic singleton `{concreteGaussianFivePlace}`);
  there is no `S2696Selection` variant in the tree.
* `Definition31PlacePartition.d11EntryData` is generic in the selection, so the
  assembly is available *conditionally*: the exact missing input is
  `S2703MissingReductionCards l D = BadPlaceReductionCards (S2696Selection l D)`
  together with the four Definition 3.1 clause values and the five D9
  compatibility pairs.  `BadPlaceReductionCards` requires stable /
  multiplicative / split-multiplicative reduction of the curve at every
  F-place above every selected bad moduli place; the tree proves it only at the
  five place (`S1280ReductionCards`), and has nothing at the 2161 place.
* A concrete obstruction is proved: `Bad (S2696Selection l S2703TwoPlaceData)`
  has two elements, while `Bad (S1280Selection l)` is a singleton, so the two
  bad-index types are not equivalent (`S2703_S1280_badIndex_no_equiv`).  The
  S1280-assembled source datum therefore cannot be silently reused as the
  S2696 V_bad source datum.

No unfinished proof, added axiom, kernel-computed decision, trivial placeholder
proposition, or unit witness is used.  The conditional source bridge is stated
with its missing cards as explicit hypotheses.
-/

noncomputable section
open scoped BigOperators

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 16000000

namespace LeanFormal.IUT.XiFPaper.S2703VbadSourceLinkActual

open LeanFormal.IUT
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.XiFPaper.S1280SourceDefinition31Actual
open LeanFormal.IUT.XiFPaper.S2696VbadActual
open LeanFormal.IUT.XiFPaper.S2689SourceBadQAbsLogActual
open LeanFormal.IUT.XiFPaper.S2681HcompMinimalInputActual
open LeanFormal.IUT.XiFPaper.BaseQLogVolumeActual

attribute [local instance] Classical.decEq

local instance s2703GaussianIrreducible :
    Fact (Irreducible (Polynomial.X ^ 2 - Polynomial.C (-1) : Polynomial ℚ)) :=
  ⟨gaussianPolynomial_irreducible⟩

local instance s2703FivePrime : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩

/-! ## 1. The actual per-place function on the actual S2696 bad set -/

/-- The actual per-place bad-q absolute log on the actual S2696 bad set: at every
bad place `p` of `S2696Vbad D`, the absolute logarithm of the assembled source
q-parameter `badPlaceQProxy` at the corresponding bad index
`Bad (S2696Selection l D)`. -/
noncomputable def qVbad (l : PrimeGeFive) (D : S2696FourPlaceData) :
    (p : NumberField.FinitePlace GaussianField) → p ∈ S2696Vbad D → Real :=
  fun p hp => |Real.log (badPlaceQProxy (S2696Selection l D) ⟨p, hp⟩)|

/-- The actual S2696 bad-q absolute log is the per-place sum over the actual
bad-place index `Bad (S2696Selection l D)`.

The displayed `letI` is the finiteness instance `(S2696Vbad_finite D).fintype`
used inside `S2696BadQAbsLog` itself; there is no global finite instance on the
subtype.  This is a definitional equality: the subtype `{p // p ∈ S2696Vbad D}`
is literally `Bad (S2696Selection l D)`. -/
theorem S2696BadQAbsLog_eq_badPlaces_sum (l : PrimeGeFive) (D : S2696FourPlaceData) :
    S2696BadQAbsLog D (qVbad l D) =
      (letI : Fintype (Bad (S2696Selection l D)) := (S2696Vbad_finite D).fintype
       ∑ b : Bad (S2696Selection l D),
         |Real.log (badPlaceQProxy (S2696Selection l D) b)|) := by
  rfl

/-- The actual S2696 V_bad bad-q total: the actual per-place sum over the
actual bad set. -/
noncomputable def sourceBadQAbsLog_vbad (l : PrimeGeFive) (D : S2696FourPlaceData) :
    Real :=
  S2696BadQAbsLog D (qVbad l D)

/-- The per-place form of the S2696 bad-q total. -/
theorem sourceBadQAbsLog_vbad_eq_badPlaces_sum (l : PrimeGeFive) (D : S2696FourPlaceData) :
    sourceBadQAbsLog_vbad l D =
      (letI : Fintype (Bad (S2696Selection l D)) := (S2696Vbad_finite D).fintype
       ∑ b : Bad (S2696Selection l D),
         |Real.log (badPlaceQProxy (S2696Selection l D) b)|) :=
  S2696BadQAbsLog_eq_badPlaces_sum l D

/-- The actual S2696 V_bad bad-q total is nonnegative. -/
theorem sourceBadQAbsLog_vbad_nonneg (l : PrimeGeFive) (D : S2696FourPlaceData) :
    0 ≤ sourceBadQAbsLog_vbad l D := by
  rw [sourceBadQAbsLog_vbad_eq_badPlaces_sum]
  exact Finset.sum_nonneg (fun b _ => abs_nonneg _)

/-! ## 2. Two distinct bad indices and the two-place lower bound -/

/-- Two distinct summands of the actual bad-q total are bounded by the total
(the S2689 `two_terms_le_sum`, applied to the S2696 bad index and to `qVbad`). -/
theorem abs_log_proxy_add_le_sourceBadQAbsLog_vbad
    (l : PrimeGeFive) (D : S2696FourPlaceData)
    (b5 b2161 : Bad (S2696Selection l D)) (hne : b5 ≠ b2161) :
    |Real.log (badPlaceQProxy (S2696Selection l D) b5)| +
        |Real.log (badPlaceQProxy (S2696Selection l D) b2161)| ≤
      sourceBadQAbsLog_vbad l D := by
  rw [sourceBadQAbsLog_vbad_eq_badPlaces_sum]
  letI : Fintype (Bad (S2696Selection l D)) := (S2696Vbad_finite D).fintype
  exact two_terms_le_sum
    (fun b : Bad (S2696Selection l D) =>
      |Real.log (badPlaceQProxy (S2696Selection l D) b)|)
    (fun b => abs_nonneg _) hne

/-- **The general two-place lower bound.**  If two distinct bad indices of the
actual S2696 selection have residue characteristics 5 and 2161, then
`log 5 + log 2161` is bounded by the actual S2696 V_bad bad-q total.  This is
the S2689 pointwise bound
`log (residueCharacteristic b) <= |log (badPlaceQProxy P b)|`
summed over the actual bad index; no real place is replaced by a singleton. -/
theorem log5_add_log2161_le_sourceBadQAbsLog_vbad
    (l : PrimeGeFive) (D : S2696FourPlaceData)
    (b5 b2161 : Bad (S2696Selection l D)) (hne : b5 ≠ b2161)
    (h5 : NumberFieldFinitePlace.residueCharacteristic b5.1 = 5)
    (h2161 : NumberFieldFinitePlace.residueCharacteristic b2161.1 = 2161) :
    Real.log 5 + Real.log 2161 ≤ sourceBadQAbsLog_vbad l D := by
  have hsum := abs_log_proxy_add_le_sourceBadQAbsLog_vbad l D b5 b2161 hne
  have h5' : Real.log 5 ≤
      |Real.log (badPlaceQProxy (S2696Selection l D) b5)| := by
    have h := log_residueCharacteristic_le_abs_log_badPlaceQProxy
      (S2696Selection l D) b5
    have hcast :
        ((NumberFieldFinitePlace.residueCharacteristic b5.1 : ℕ) : ℝ) = (5 : ℝ) := by
      rw [h5]; norm_num
    rwa [hcast] at h
  have h2161' : Real.log 2161 ≤
      |Real.log (badPlaceQProxy (S2696Selection l D) b2161)| := by
    have h := log_residueCharacteristic_le_abs_log_badPlaceQProxy
      (S2696Selection l D) b2161
    have hcast :
        ((NumberFieldFinitePlace.residueCharacteristic b2161.1 : ℕ) : ℝ) = (2161 : ℝ) := by
      rw [h2161]; norm_num
    rwa [hcast] at h
  linarith

/-- **The strict `2 log 5` lower bound**, general form. -/
theorem two_log5_lt_sourceBadQAbsLog_vbad
    (l : PrimeGeFive) (D : S2696FourPlaceData)
    (b5 b2161 : Bad (S2696Selection l D)) (hne : b5 ≠ b2161)
    (h5 : NumberFieldFinitePlace.residueCharacteristic b5.1 = 5)
    (h2161 : NumberFieldFinitePlace.residueCharacteristic b2161.1 = 2161) :
    2 * Real.log 5 < sourceBadQAbsLog_vbad l D := by
  have h := log5_add_log2161_le_sourceBadQAbsLog_vbad l D b5 b2161 hne h5 h2161
  have hlt : Real.log (5 : ℝ) < Real.log (2161 : ℝ) :=
    Real.log_lt_log (by norm_num) (by norm_num)
  linarith

/-! ## 3. The concrete two-element datum `{5, 2161}` -/

/-- Oddness of the residue characteristic at the concrete Gaussian five place. -/
theorem S2703FiveOdd :
    Odd (NumberFieldFinitePlace.residueCharacteristic concreteGaussianFivePlace) := by
  rw [LeanFormal.IUT.IUTII.Frobenioid.Example36.concreteGaussianFivePlace_residueCharacteristic]
  exact ⟨2, by norm_num⟩

/-- Oddness of the residue characteristic at the actual Gaussian place above 2161. -/
theorem S2703GaussianPlace2161Odd :
    Odd (NumberFieldFinitePlace.residueCharacteristic S2696GaussianPlace2161) := by
  rw [S2696GaussianPlace2161_residueCharacteristic]
  exact ⟨1080, by norm_num⟩

/-- The concrete two-element `S2696FourPlaceData`: both places above 5 are the
concrete Gaussian five place, both places above 2161 are the actual Gaussian
place `S2696GaussianPlace2161`.  Its bad set is exactly `{5, 2161}`. -/
def S2703TwoPlaceData : S2696FourPlaceData where
  p5a := concreteGaussianFivePlace
  p5b := concreteGaussianFivePlace
  p2161a := S2696GaussianPlace2161
  p2161b := S2696GaussianPlace2161
  odd5a := S2703FiveOdd
  odd5b := S2703FiveOdd
  odd2161a := S2703GaussianPlace2161Odd
  odd2161b := S2703GaussianPlace2161Odd

/-- The two concrete places are distinct (residue characteristics 5 and 2161). -/
theorem S2703_five_ne_2161 :
    concreteGaussianFivePlace ≠ S2696GaussianPlace2161 := by
  intro h
  have hfive :=
    LeanFormal.IUT.IUTII.Frobenioid.Example36.concreteGaussianFivePlace_residueCharacteristic
  have h2161 := S2696GaussianPlace2161_residueCharacteristic
  rw [h] at hfive
  rw [hfive] at h2161
  norm_num at h2161

/-- Membership of the five place in the concrete bad set. -/
theorem S2703MemberFive :
    concreteGaussianFivePlace ∈ S2696Vbad S2703TwoPlaceData := by
  change concreteGaussianFivePlace = S2703TwoPlaceData.p5a ∨
    concreteGaussianFivePlace = S2703TwoPlaceData.p5b ∨
    concreteGaussianFivePlace = S2703TwoPlaceData.p2161a ∨
    concreteGaussianFivePlace = S2703TwoPlaceData.p2161b
  exact Or.inl rfl

/-- Membership of the 2161 place in the concrete bad set. -/
theorem S2703Member2161 :
    S2696GaussianPlace2161 ∈ S2696Vbad S2703TwoPlaceData := by
  change S2696GaussianPlace2161 = S2703TwoPlaceData.p5a ∨
    S2696GaussianPlace2161 = S2703TwoPlaceData.p5b ∨
    S2696GaussianPlace2161 = S2703TwoPlaceData.p2161a ∨
    S2696GaussianPlace2161 = S2703TwoPlaceData.p2161b
  exact Or.inr (Or.inr (Or.inl rfl))

/-- The five bad index of the concrete datum. -/
def S2703BadFive (l : PrimeGeFive) :
    Bad (S2696Selection l S2703TwoPlaceData) :=
  ⟨concreteGaussianFivePlace, S2703MemberFive⟩

/-- The 2161 bad index of the concrete datum. -/
def S2703Bad2161 (l : PrimeGeFive) :
    Bad (S2696Selection l S2703TwoPlaceData) :=
  ⟨S2696GaussianPlace2161, S2703Member2161⟩

/-- Finiteness instance for the concrete two-element bad index. -/
@[reducible] noncomputable def S2703BadFintype (l : PrimeGeFive) :
    Fintype (Bad (S2696Selection l S2703TwoPlaceData)) :=
  (S2696Vbad_finite S2703TwoPlaceData).fintype

instance S2703BadFintypeInstance (l : PrimeGeFive) :
    Fintype (Bad (S2696Selection l S2703TwoPlaceData)) :=
  S2703BadFintype l

/-- The concrete two bad indices are distinct. -/
theorem S2703BadFive_ne (l : PrimeGeFive) :
    S2703BadFive l ≠ S2703Bad2161 l := by
  intro h
  exact S2703_five_ne_2161 (congrArg Subtype.val h)

/-- Residue characteristic of the concrete five bad index. -/
theorem S2703Five_residueCharacteristic (l : PrimeGeFive) :
    NumberFieldFinitePlace.residueCharacteristic (S2703BadFive l).1 = 5 :=
  LeanFormal.IUT.IUTII.Frobenioid.Example36.concreteGaussianFivePlace_residueCharacteristic

/-- Residue characteristic of the concrete 2161 bad index. -/
theorem S2703_2161_residueCharacteristic (l : PrimeGeFive) :
    NumberFieldFinitePlace.residueCharacteristic (S2703Bad2161 l).1 = 2161 :=
  S2696GaussianPlace2161_residueCharacteristic

/-- The bad index of the concrete datum is exactly the two-element set. -/
theorem S2703BadUniv (l : PrimeGeFive) :
    (Finset.univ : Finset (Bad (S2696Selection l S2703TwoPlaceData))) =
      {S2703BadFive l, S2703Bad2161 l} := by
  classical
  ext b
  simp only [Finset.mem_univ, true_iff, Finset.mem_insert, Finset.mem_singleton]
  obtain ⟨p, hp⟩ := b
  have hp' : p = concreteGaussianFivePlace ∨ p = S2696GaussianPlace2161 := by
    change p = S2703TwoPlaceData.p5a ∨ p = S2703TwoPlaceData.p5b ∨
      p = S2703TwoPlaceData.p2161a ∨ p = S2703TwoPlaceData.p2161b at hp
    rcases hp with h | h | h | h
    · exact Or.inl h
    · exact Or.inl h
    · exact Or.inr h
    · exact Or.inr h
  rcases hp' with rfl | rfl
  · exact Or.inl (Subtype.ext rfl)
  · exact Or.inr (Subtype.ext rfl)

/-- **The exact two-term decomposition** of an S2696 bad-q total whose bad
index is known to be the pair `{b1, b2}`. -/
theorem S2696BadQAbsLog_eq_sum_pair
    (l : PrimeGeFive) (D : S2696FourPlaceData)
    (b1 b2 : Bad (S2696Selection l D)) (hne : b1 ≠ b2)
    (huniv : @Finset.univ (Bad (S2696Selection l D))
        (S2696Vbad_finite D).fintype = {b1, b2}) :
    S2696BadQAbsLog D (qVbad l D) =
      |Real.log (badPlaceQProxy (S2696Selection l D) b1)| +
        |Real.log (badPlaceQProxy (S2696Selection l D) b2)| := by
  rw [S2696BadQAbsLog_eq_badPlaces_sum]
  letI : Fintype (Bad (S2696Selection l D)) := (S2696Vbad_finite D).fintype
  rw [huniv, Finset.sum_pair hne]

/-- The concrete S2696 bad-q total is exactly the five term plus the 2161 term. -/
theorem S2703_S2696BadQAbsLog_eq_five_add_2161 (l : PrimeGeFive) :
    S2696BadQAbsLog S2703TwoPlaceData (qVbad l S2703TwoPlaceData) =
      qVbad l S2703TwoPlaceData concreteGaussianFivePlace S2703MemberFive +
        qVbad l S2703TwoPlaceData S2696GaussianPlace2161 S2703Member2161 := by
  rw [S2696BadQAbsLog_eq_sum_pair l S2703TwoPlaceData
    (S2703BadFive l) (S2703Bad2161 l) (S2703BadFive_ne l) (S2703BadUniv l)]
  rfl

/-- The concrete five summand is at least `log 5`. -/
theorem log5_le_abs_log_proxy_five (l : PrimeGeFive) :
    Real.log 5 ≤
      |Real.log (badPlaceQProxy (S2696Selection l S2703TwoPlaceData)
        (S2703BadFive l))| := by
  have h := log_residueCharacteristic_le_abs_log_badPlaceQProxy
    (S2696Selection l S2703TwoPlaceData) (S2703BadFive l)
  have hcast :
      ((NumberFieldFinitePlace.residueCharacteristic (S2703BadFive l).1 : ℕ) : ℝ) =
        (5 : ℝ) := by
    rw [S2703Five_residueCharacteristic]; norm_num
  rwa [hcast] at h

/-- The concrete 2161 summand is at least `log 2161`. -/
theorem log2161_le_abs_log_proxy_2161 (l : PrimeGeFive) :
    Real.log 2161 ≤
      |Real.log (badPlaceQProxy (S2696Selection l S2703TwoPlaceData)
        (S2703Bad2161 l))| := by
  have h := log_residueCharacteristic_le_abs_log_badPlaceQProxy
    (S2696Selection l S2703TwoPlaceData) (S2703Bad2161 l)
  have hcast :
      ((NumberFieldFinitePlace.residueCharacteristic (S2703Bad2161 l).1 : ℕ) : ℝ) =
        (2161 : ℝ) := by
    rw [S2703_2161_residueCharacteristic]; norm_num
  rwa [hcast] at h

/-- **The unconditional `log 5 + log 2161` lower bound at the concrete
two-element V_bad.** -/
theorem log5_add_log2161_le_sourceBadQAbsLog_vbad_twoPlace (l : PrimeGeFive) :
    Real.log 5 + Real.log 2161 ≤
      sourceBadQAbsLog_vbad l S2703TwoPlaceData := by
  have hsum := S2703_S2696BadQAbsLog_eq_five_add_2161 l
  have h5 := log5_le_abs_log_proxy_five l
  have h2161 := log2161_le_abs_log_proxy_2161 l
  unfold sourceBadQAbsLog_vbad
  rw [hsum]
  exact add_le_add h5 h2161

/-- **The unconditional strict `2 log 5` lower bound at the concrete
two-element V_bad.** -/
theorem two_log5_lt_sourceBadQAbsLog_vbad_twoPlace (l : PrimeGeFive) :
    2 * Real.log 5 < sourceBadQAbsLog_vbad l S2703TwoPlaceData := by
  have h := log5_add_log2161_le_sourceBadQAbsLog_vbad_twoPlace l
  have hlt : Real.log (5 : ℝ) < Real.log (2161 : ℝ) :=
    Real.log_lt_log (by norm_num) (by norm_num)
  linarith

/-! ## 4. Conditional hcomp -/

/-- **Conditional hcomp**, general form.  If the actual S2696 V_bad bad-q total
is dominated by the native total base-q magnitude, then the S2681 bad-q data
`HcompBadQData T` (`2 log 5 <= baseQTotalLogMagnitude T`) holds.  The
numeric residual `2 log 5 < sourceBadQAbsLog_vbad l D` is discharged by the
two-place bound; `halign` is the only remaining bridge and is not asserted. -/
theorem hcompBadQData_of_sourceBadQAbsLog_vbad
    {l : PrimeGeFive} {D : S2696FourPlaceData}
    {T : SourceNativeInitialThetaData.{0} l}
    [Fintype (Bad (nativePlaceSelection T))]
    (b5 b2161 : Bad (S2696Selection l D)) (hne : b5 ≠ b2161)
    (h5 : NumberFieldFinitePlace.residueCharacteristic b5.1 = 5)
    (h2161 : NumberFieldFinitePlace.residueCharacteristic b2161.1 = 2161)
    (halign : sourceBadQAbsLog_vbad l D ≤ baseQTotalLogMagnitude T) :
    HcompBadQData T := by
  unfold HcompBadQData
  have h := two_log5_lt_sourceBadQAbsLog_vbad l D b5 b2161 hne h5 h2161
  linarith

/-- **Conditional hcomp at the concrete two-element V_bad**: only the bridge
`halign` remains. -/
theorem hcompBadQData_of_sourceBadQAbsLog_vbad_twoPlace
    {l : PrimeGeFive} {T : SourceNativeInitialThetaData.{0} l}
    [Fintype (Bad (nativePlaceSelection T))]
    (halign : sourceBadQAbsLog_vbad l S2703TwoPlaceData ≤ baseQTotalLogMagnitude T) :
    HcompBadQData T :=
  hcompBadQData_of_sourceBadQAbsLog_vbad
    (D := S2703TwoPlaceData) (S2703BadFive l) (S2703Bad2161 l)
    (S2703BadFive_ne l) (S2703Five_residueCharacteristic l)
    (S2703_2161_residueCharacteristic l) halign

/-! ## 5. The source-data bridge and its exact gap -/

/-- The definitional bridge from the generic Definition 3.1 assembly
`d11EntryData` to the per-place `badPlaceQProxy` sum: `d11EntryData` sets
`badPlaces := Bad P`, `badFinite := inferInstance`, and
`qParameter := fun b => badPlaceQProxy P b`, so the source scalar is exactly
the per-place sum. -/
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

/-- The exact `SourceDefinition31Data` candidate over the actual S2696 selection,
assembled through the generic `d11EntryData`.  The reduction cards `C` and the
four Definition 3.1 clause values are explicit inputs; no inhabitant of them is
constructed in this file. -/
noncomputable def S2703SourceDataCandidate (l : PrimeGeFive) (D : S2696FourPlaceData)
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
  @Definition31PlacePartition.d11EntryData l (S1280Arithmetic l) (S2696Selection l D)
    ((S2696Vbad_finite D).fintype) C T O Se Cu
    redCompat hredCompat torCompat htorCompat orbCompat horbCompat
    secCompat hsecCompat cusCompat hcusCompat

/-- The bad index of the candidate source datum is `Bad (S2696Selection l D)`. -/
theorem S2703SourceDataCandidate_badPlaces (l : PrimeGeFive) (D : S2696FourPlaceData)
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
    (S2703SourceDataCandidate l D C T O Se Cu redCompat hredCompat
      torCompat htorCompat orbCompat horbCompat secCompat hsecCompat
      cusCompat hcusCompat).badPlaces = Bad (S2696Selection l D) :=
  rfl

/-- The reduction component of the candidate is `toSourceReductionClause` at the
actual S2696 selection, hence `qParameter = badPlaceQProxy`. -/
theorem S2703SourceDataCandidate_reduction (l : PrimeGeFive) (D : S2696FourPlaceData)
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
    (S2703SourceDataCandidate l D C T O Se Cu redCompat hredCompat
      torCompat htorCompat orbCompat horbCompat secCompat hsecCompat
      cusCompat hcusCompat).reduction =
      @toSourceReductionClause l (S1280Arithmetic l) (S2696Selection l D)
        ((S2696Vbad_finite D).fintype) C :=
  rfl

/-- The q-parameter of the candidate source datum is `badPlaceQProxy` at the
actual S2696 selection. -/
theorem S2703SourceDataCandidate_qParameter (l : PrimeGeFive) (D : S2696FourPlaceData)
    (C : BadPlaceReductionCards (S2696Selection l D))
    (T : Theorem311Source.SourceTorsionClause l)
    (O : Theorem311Source.SourceOrbicurveClause)
    (Se : Theorem311Source.SourceSectionClause)
    (Cu : Theorem311Source.SourceCuspClause)
    (redCompat : Prop) (hredCompat : redCompat)
    (torCompat : Prop) (htorCompat : torCompat)
    (orbCompat : Prop) (horbCompat : orbCompat)
    (secCompat : Prop) (hsecCompat : secCompat)
    (cusCompat : Prop) (hcusCompat : cusCompat)
    (b : Bad (S2696Selection l D)) :
    (S2703SourceDataCandidate l D C T O Se Cu redCompat hredCompat
      torCompat htorCompat orbCompat horbCompat secCompat hsecCompat
      cusCompat hcusCompat).reduction.qParameter b =
      badPlaceQProxy (S2696Selection l D) b :=
  rfl

/-- **The definitional source-data identification (conditional on the missing
cards).**  If the actual S2696 selection is equipped with bad-place reduction
cards and the four Definition 3.1 clause values, then the source scalar
`sourceBadQAbsLog` of the assembled `SourceDefinition31Data` is exactly the
actual S2696 V_bad bad-q total.  This is a definitional equality, not a numerical
coincidence. -/
theorem sourceBadQAbsLog_candidate_eq_vbad (l : PrimeGeFive) (D : S2696FourPlaceData)
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
    Theorem311Source.sourceBadQAbsLog
      (S2703SourceDataCandidate l D C T O Se Cu redCompat hredCompat
        torCompat htorCompat orbCompat horbCompat secCompat hsecCompat
        cusCompat hcusCompat) =
      sourceBadQAbsLog_vbad l D := by
  unfold sourceBadQAbsLog_vbad
  rw [S2696BadQAbsLog_eq_badPlaces_sum]
  exact @sourceBadQAbsLog_d11EntryData_eq_sum_badPlaces l (S1280Arithmetic l)
    (S2696Selection l D) ((S2696Vbad_finite D).fintype) C T O Se Cu
    redCompat hredCompat torCompat htorCompat orbCompat horbCompat
    secCompat hsecCompat cusCompat hcusCompat

/-- The exact missing input of the source-data bridge: the Definition 3.1(b)
bad-place reduction cards at the actual S2696 selection.  This type has no
known inhabitant in the tree; `S1280ReductionCards` supplies the same cards only
for the synthetic singleton `S1280Selection`. -/
abbrev S2703MissingReductionCards (l : PrimeGeFive) (D : S2696FourPlaceData) :=
  BadPlaceReductionCards (S2696Selection l D)

/-! ### The concrete cardinality obstruction of the S1280 hardwiring -/

/-- The unique bad index of the synthetic S1280 selection. -/
def S1280BadFiveIndex (l : PrimeGeFive) : Bad (S1280Selection l) :=
  ⟨concreteGaussianFivePlace, by
    rw [S1280Selection_V_mod_bad]
    exact Set.mem_singleton _⟩

/-- The synthetic S1280 bad index is a singleton. -/
theorem S1280Bad_card (l : PrimeGeFive) :
    Fintype.card (Bad (S1280Selection l)) = 1 := by
  letI : Subsingleton (Bad (S1280Selection l)) := S1280Bad_subsingleton l
  have huniv : (Finset.univ : Finset (Bad (S1280Selection l))) =
      {S1280BadFiveIndex l} := by
    ext b
    simp only [Finset.mem_univ, true_iff, Finset.mem_singleton]
    exact Subsingleton.elim b (S1280BadFiveIndex l)
  rw [← Finset.card_univ, huniv, Finset.card_singleton]

/-- The concrete two-element S2696 bad index has cardinality 2. -/
theorem S2703Bad_twoPlace_card (l : PrimeGeFive) :
    Fintype.card (Bad (S2696Selection l S2703TwoPlaceData)) = 2 := by
  rw [← Finset.card_univ, S2703BadUniv l]
  exact Finset.card_pair (S2703BadFive_ne l)

/-- **The S1280 hardwiring obstruction.**  The S2696 two-element bad index is
not equivalent to the S1280 singleton bad index, so the source datum assembled
by `S1280SourceData_of_remaining` cannot be silently reused as the source datum
over `Bad (S2696Selection l S2703TwoPlaceData)`.  This is the concrete
kernel-checked form of the source-data gap. -/
theorem S2703_S1280_badIndex_no_equiv (l : PrimeGeFive) :
    ¬ Nonempty (Bad (S2696Selection l S2703TwoPlaceData) ≃
        Bad (S1280Selection l)) := by
  rintro ⟨e⟩
  have hc := Fintype.card_congr e
  rw [S2703Bad_twoPlace_card l, S1280Bad_card l] at hc
  norm_num at hc

/-- The S2696 V_bad of the concrete datum is genuinely two-place. -/
theorem S2703_vbad_two_indices (l : PrimeGeFive) :
    ∃ b1 b2 : Bad (S2696Selection l S2703TwoPlaceData), b1 ≠ b2 :=
  ⟨S2703BadFive l, S2703Bad2161 l, S2703BadFive_ne l⟩

/-! ## 6. Axiom audit -/

#print axioms S2696BadQAbsLog_eq_badPlaces_sum
#print axioms sourceBadQAbsLog_vbad_nonneg
#print axioms abs_log_proxy_add_le_sourceBadQAbsLog_vbad
#print axioms log5_add_log2161_le_sourceBadQAbsLog_vbad
#print axioms two_log5_lt_sourceBadQAbsLog_vbad
#print axioms S2696BadQAbsLog_eq_sum_pair
#print axioms S2703_S2696BadQAbsLog_eq_five_add_2161
#print axioms log5_le_abs_log_proxy_five
#print axioms log2161_le_abs_log_proxy_2161
#print axioms log5_add_log2161_le_sourceBadQAbsLog_vbad_twoPlace
#print axioms two_log5_lt_sourceBadQAbsLog_vbad_twoPlace
#print axioms hcompBadQData_of_sourceBadQAbsLog_vbad
#print axioms hcompBadQData_of_sourceBadQAbsLog_vbad_twoPlace
#print axioms sourceBadQAbsLog_d11EntryData_eq_sum_badPlaces
#print axioms sourceBadQAbsLog_candidate_eq_vbad
#print axioms S2703_S1280_badIndex_no_equiv
#print axioms S2703_vbad_two_indices

end LeanFormal.IUT.XiFPaper.S2703VbadSourceLinkActual

end
