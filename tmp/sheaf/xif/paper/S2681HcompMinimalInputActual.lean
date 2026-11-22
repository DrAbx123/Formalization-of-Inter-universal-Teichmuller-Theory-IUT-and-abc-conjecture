/-
Copyright (c) 2026 LeanFormal contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import tmp.sheaf.xif.PaperQPilotObject
import tmp.sheaf.xif.PaperSignedHull
import tmp.sheaf.xif.paper.PaperQPilotObjectConcreteActual
import tmp.sheaf.xif.paper.ConcreteThetaLinkSourceActual
import tmp.sheaf.xif.paper.PaperThetaMagnitudeSignedActual
import tmp.sheaf.xif.paper.S1931SourceHaarSignedAverageActual
import tmp.sheaf.xif.paper.S2679HcompLocalBoundsActual
import LeanFormal.IUT.Foundations.Geometry.TateInverseJUniformization
import LeanFormal.IUT.Foundations.Theta.SignedLabelEquiv
import LeanFormal.IUT.IUTI.InitialTheta.SourcePlaceTateComparisonSynthesis

/-!
# S2681: the hcomp prerequisite chain as minimal input

## Target

PaperXiFUnconditional.PaperUnconditionalData (line 107) has three fields,
sourceLink, sourceLink_holds and thetaLink.  Its concrete hcomp (the
sourceLink_holds field) is exactly

  concreteSourceComparison O P  :=  P.procession.average <= -O.qPilotLogVolume

for the concrete paper q-pilot object O = paperQPilotObjectConcrete I
(ConcreteThetaLinkSourceActual.concreteSourceComparison).  By
ConcreteSourceComparisonNumericActual.concreteComparison_iff_gaussSum_le_badQAbsLog
(in the form re-proved below, because that module has no olean in the current
build set) this is exactly the numeric residual

  Real.log 5 * (sourceThetaWeightSum l / c3ThetaCard l) <= sourceBadQAbsLog I.initial.

## What this file does

1. It defines the minimal input for the hcomp chain, using only existing types:

   * HcompTateInput T is the disjunction of the two existing analytic Tate
     forms: TateInverseJUniformizationInterface (inverse-j q_Tate with
     ||q_Tate|| = 1/5 plus the analytic curve-indexed uniformization at the
     concrete split five place), OR the per-place contract family
     Nonempty (BadPlaceUniformizationContract (nativePlaceSelection T)) (whose
     realization field is the per-place CurveIndexedTateUniformization of
     TateUniformizationContract.lean:88 over the actual bad places of the
     native source data; this is the family isolated as minimal by
     SourcePlaceTateComparisonSynthesis).
   * HcompSourceQAgreement I T is the source qParameter/order agreement: the
     exact index/log alignment between the source bad q parameters
     (sourceBadQAbsLog) and the native base-q family (baseQ T b,
     baseQLogMagnitude T b), together with the actual order formula
     baseQLogMagnitude T b = order_b * log (residueNormBase ...) of
     BaseQLogVolumeActual.
   * HcompBadQData T is the bad-q data needed for hcomp:
     2 * log 5 <= baseQTotalLogMagnitude T (the native form of
     NativeGlobalQPilotComparison / S2678.NativeResidual; it is derived from
     the actual local bounds of S2679 under card(V_bad) >= 5).

2. It proves the reduction HcompMinimalInput -> hcomp (hcomp_of_minimalInput),
   and the sharper hcomp_of_agreement_badQ showing that the Tate component is
   not consumed by the numeric comparison.

3. It proves the converse up to two explicitly named numeric inputs:
   badQData_of_hcomp_of_coefficient recovers the bad-q data from hcomp once the
   Gaussian coefficient lower bound 2 log 5 <= log 5 * (W / card) is supplied.
   At l.value = 5 that bound is the exact identity W / card = 2
   (weightSum_div_card_eq_two_of_value_eq_five), so hcomp_iff_badQData_five is
   a genuine equivalence

     hcomp  <->  2 log 5 <= baseQTotalLogMagnitude T

   at l = 5, given the q agreement.

## Honest scope / what is not claimed

* No F-side comparison is asserted.  HcompBadQData is a hypothesis; the file
  only proves that it is exactly what hcomp needs.  HcompMinimalInput has no
  asserted inhabitant.
* The Tate analytic input is logically independent of the numeric content of
  hcomp: sourceBadQAbsLog is defined from I.initial.reduction.qParameter, and
  the latter is the completed-DVR proxy of the source reduction clause
  (S1280ReductionClause_qParameter_eq: q_b = (1/5) ^ order_b), so no
  uniformization theorem enters the inequality.  This is proved as
  hcomp_of_agreement_badQ, which takes no Tate input at all.  The role of the
  Tate input is the geometric one: it certifies that the source q candidates
  are genuine Tate parameters.  That identification is recorded as the explicit
  missing proposition S2681MissingTateQNumericLink (not assumed, not proved).
* The exact Gaussian sum closed form
  gaussExponentSum = lStar * (lStar + 1) * (2 * lStar + 1) / 3
  (SignedAverageBoundActual.GaussExponentSumClosedForm) is not proved in the
  tree.  Its l = 5 instance (W = 10, card = 5) IS proved below by a kernel
  decide over Fl 5 (no native_decide).
* No sorry, axiom, True, PUnit, empty type, or native_decide is used.
-/

noncomputable section
open scoped BigOperators
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 16000000

namespace LeanFormal.IUT.XiFPaper.S2681HcompMinimalInputActual

open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.Theorem311Source.PaperQPilotConcreteActual
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.N8Closure.C3Actual
open LeanFormal.IUT.N8Closure.SourcePilotRegion
open LeanFormal.IUT.N8Closure.ThetaPacketQIdentificationActual
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.InitialThetaSource.PlaceTateComparisonConstruction
open LeanFormal.IUT.XiFPaper.ConcreteThetaLinkSourceActual
open LeanFormal.IUT.XiFPaper.PaperThetaMagnitudeSignedActual
open LeanFormal.IUT.XiFPaper.ProcessionThetaPacketAverageActual
open LeanFormal.IUT.XiFPaper.S1931SourceHaarSignedAverageActual
open LeanFormal.IUT.XiFPaper.BaseQLogVolumeActual
open LeanFormal.IUT.XiFPaper.BaseQFamilyActual
open LeanFormal.IUT.XiFPaper.S2679HcompLocalBoundsActual
open LeanFormal.IUT.ArithmeticQPilotBaseChange
open LeanFormal.IUT.NumberFieldFinitePlace

universe uX uLabel

variable {l : PrimeGeFive}
variable {X : Type uX} {label : Type uLabel} [Fintype label]

/-! ## 1. The analytic Tate input: inverse-j interface or per-place family -/

/-- The analytic Tate input of the hcomp chain, in exactly the two existing
forms:

* TateInverseJUniformizationInterface: an inverse-j parameter q_Tate at the
  concrete split five place with ||q_Tate|| = 1/5, together with a
  curve-indexed Tate uniformization (coordinate variable change and
  Galois-equivariant quotient-point uniformization);
* the per-place contract family BadPlaceUniformizationContract over the actual
  bad places of the native source data, whose realization field is the one-way
  CurveIndexedTateUniformization contract of TateUniformizationContract.lean:88
  at each place.

No inhabitant is constructed or asserted. -/
def HcompTateInput (T : SourceNativeInitialThetaData.{0} l) : Prop :=
  TateInverseJUniformizationInterface ∨
    Nonempty (BadPlaceUniformizationContract (nativePlaceSelection T))

/-- The inverse-j interface is one admissible form of the minimal Tate input. -/
theorem hcompTateInput_of_inverseJ (T : SourceNativeInitialThetaData.{0} l)
    (h : TateInverseJUniformizationInterface) : HcompTateInput T :=
  Or.inl h

/-- The per-place contract family is the other admissible form. -/
theorem hcompTateInput_of_contract (T : SourceNativeInitialThetaData.{0} l)
    (K : BadPlaceUniformizationContract (nativePlaceSelection T)) :
    HcompTateInput T :=
  Or.inr ⟨K⟩

/-- The per-place branch supplies, at every bad place, the curve-indexed Tate
uniformization contract itself. -/
theorem perPlaceUniformization_of_contract
    (T : SourceNativeInitialThetaData.{0} l)
    (K : BadPlaceUniformizationContract (nativePlaceSelection T))
    (w : NumberField.FinitePlace T.arithmetic.F)
    (hw : NumberFieldFinitePlace.comap (k := T.arithmetic.Fmod) w ∈
      (nativePlaceSelection T).V_mod_bad) :
    Nonempty (CurveIndexedTateUniformization T.arithmetic.curve w
      (K.parameter w hw)) :=
  ⟨K.realization w hw⟩

/-! ## 2. The source qParameter / order agreement -/

/-- The exact source qParameter/order agreement used by hcomp.

* alignment: a bijection between the source bad places and the native bad
  places under which the absolute logarithms of the source q parameters
  I.initial.reduction.qParameter are the native base-q log-magnitudes
  baseQLogMagnitude T;
* order_formula: the actual order formula for the native base q family (the
  content of baseQLogMagnitude_eq_order_mul_log).

The alignment is a genuine missing bridge (the tree has no descent map from the
native F-completion to the source Fmod-completion); it is a hypothesis here,
never proved or asserted. -/
structure HcompSourceQAgreement
    (I : OriginalInput.{0, 0, 0, 0, 0} l (FinitePrimePlace 2 7))
    (T : SourceNativeInitialThetaData.{0} l) where
  alignment :
    ∃ e : I.initial.badPlaces ≃ Bad (nativePlaceSelection T),
      ∀ b : I.initial.badPlaces,
        |Real.log (I.initial.reduction.qParameter b)| =
          baseQLogMagnitude T (e b)
  order_formula :
    ∀ b : Bad (nativePlaceSelection T),
      baseQLogMagnitude T b =
        ((baseQ T b).order : ℝ) *
          Real.log (residueNormBase (nativeBaseSectionPlace T b))

/-- The agreement only has to supply the index/log alignment: the order formula
is the actual theorem baseQLogMagnitude_eq_order_mul_log. -/
theorem HcompSourceQAgreement.ofAlignment
    (I : OriginalInput.{0, 0, 0, 0, 0} l (FinitePrimePlace 2 7))
    (T : SourceNativeInitialThetaData.{0} l)
    (h : ∃ e : I.initial.badPlaces ≃ Bad (nativePlaceSelection T),
      ∀ b : I.initial.badPlaces,
        |Real.log (I.initial.reduction.qParameter b)| =
          baseQLogMagnitude T (e b)) :
    HcompSourceQAgreement I T where
  alignment := h
  order_formula := fun b => baseQLogMagnitude_eq_order_mul_log T b

/-! ## 3. The bad-q data needed for hcomp -/

/-- The bad-q data needed for hcomp: the total native bad base-q magnitude
dominates 2 log 5.  This is exactly NativeGlobalQPilotComparison
(GlobalQPilotComparisonTruthActual) / NativeResidual
(S2678PaperUnconditionalHcompActual), restated on the importable
baseQTotalLogMagnitude; it has no asserted inhabitant. -/
def HcompBadQData (T : SourceNativeInitialThetaData.{0} l)
    [Fintype (Bad (nativePlaceSelection T))] : Prop :=
  2 * Real.log 5 ≤ baseQTotalLogMagnitude T

/-- The source-side form of the bad-q data: the source bad-q absolute log
dominates 2 log 5.  Under the q agreement this is equivalent to HcompBadQData. -/
def HcompSourceBadQData
    (I : OriginalInput.{0, 0, 0, 0, 0} l (FinitePrimePlace 2 7)) : Prop :=
  2 * Real.log 5 ≤ sourceBadQAbsLog I.initial

/-- Under the exact source q agreement, the source bad-q absolute log IS the
total native base-q magnitude.  (Local reproduction of the
S2681HcompBadQAlignmentActual / S2678PaperUnconditionalHcompActual bridge,
whose modules are not importable beside the concrete paper objects.) -/
theorem sourceBadQAbsLog_eq_baseQTotalLogMagnitude
    (I : OriginalInput.{0, 0, 0, 0, 0} l (FinitePrimePlace 2 7))
    (T : SourceNativeInitialThetaData.{0} l)
    [Fintype (Bad (nativePlaceSelection T))]
    (halign : ∃ e : I.initial.badPlaces ≃ Bad (nativePlaceSelection T),
      ∀ b : I.initial.badPlaces,
        |Real.log (I.initial.reduction.qParameter b)| =
          baseQLogMagnitude T (e b)) :
    sourceBadQAbsLog I.initial = baseQTotalLogMagnitude T := by
  letI : Fintype I.initial.badPlaces := I.initial.bad_finite
  obtain ⟨e, he⟩ := halign
  unfold sourceBadQAbsLog baseQTotalLogMagnitude
  calc
    (∑ b : I.initial.badPlaces,
        |Real.log (I.initial.reduction.qParameter b)|) =
        ∑ b : I.initial.badPlaces, baseQLogMagnitude T (e b) := by
      refine Finset.sum_congr rfl ?_
      intro b _
      exact he b
    _ = ∑ b : Bad (nativePlaceSelection T), baseQLogMagnitude T b := by
      exact Fintype.sum_equiv e (fun b => baseQLogMagnitude T (e b))
        (fun b => baseQLogMagnitude T b) (fun b => rfl)

/-- The bad-q data gives the source bad-q absolute-log bound under the
agreement. -/
theorem two_log5_le_sourceBadQAbsLog
    (I : OriginalInput.{0, 0, 0, 0, 0} l (FinitePrimePlace 2 7))
    (T : SourceNativeInitialThetaData.{0} l)
    [Fintype (Bad (nativePlaceSelection T))]
    (halign : ∃ e : I.initial.badPlaces ≃ Bad (nativePlaceSelection T),
      ∀ b : I.initial.badPlaces,
        |Real.log (I.initial.reduction.qParameter b)| =
          baseQLogMagnitude T (e b))
    (h : HcompBadQData T) :
    2 * Real.log 5 ≤ sourceBadQAbsLog I.initial := by
  rw [sourceBadQAbsLog_eq_baseQTotalLogMagnitude I T halign]
  exact h

/-- The actual S2679 local order/residue bounds plus card(V_bad) >= 5 supply the
bad-q data.  This is the only known sufficient construction of HcompBadQData in
the tree; it needs the cardinality condition. -/
theorem hcompBadQData_of_card_ge_five
    (I : OriginalInput.{0, 0, 0, 0, 0} l (FinitePrimePlace 2 7))
    (T : SourceNativeInitialThetaData.{0} l)
    [Fintype (Bad (nativePlaceSelection T))]
    (halign : ∃ e : I.initial.badPlaces ≃ Bad (nativePlaceSelection T),
      ∀ b : I.initial.badPlaces,
        |Real.log (I.initial.reduction.qParameter b)| =
          baseQLogMagnitude T (e b))
    (hcard : 5 ≤ Nat.card I.initial.badPlaces) :
    HcompBadQData T := by
  have hcardNat : 5 ≤ Fintype.card (Bad (nativePlaceSelection T)) := by
    letI : Fintype I.initial.badPlaces := I.initial.bad_finite
    obtain ⟨e, -⟩ := halign
    have hcard' : 5 ≤ Fintype.card I.initial.badPlaces := by
      rwa [Nat.card_eq_fintype_card] at hcard
    calc 5 ≤ Fintype.card I.initial.badPlaces := hcard'
      _ = Fintype.card (Bad (nativePlaceSelection T)) := Fintype.card_congr e
  exact hcomp_global_ge_two_log5_of_card_ge_five T hcardNat

/-! ## 4. The minimal input -/

/-- The minimal input of the hcomp prerequisite chain.  Every component is an
existing type or an explicitly named proposition:

* tate: the analytic Tate input (inverse-j interface OR the per-place
  curve-indexed contract family);
* sourceQ: the source qParameter/order agreement;
* badQ: the bad-q data (2 log 5 <= baseQTotalLogMagnitude T).

The structure has no asserted inhabitant. -/
structure HcompMinimalInput
    (I : OriginalInput.{0, 0, 0, 0, 0} l (FinitePrimePlace 2 7))
    (T : SourceNativeInitialThetaData.{0} l)
    [Fintype (Bad (nativePlaceSelection T))] where
  tate : HcompTateInput T
  sourceQ : HcompSourceQAgreement I T
  badQ : HcompBadQData T

/-! ## 5. The exact numeric reduction of hcomp -/

/-- The concrete paper q-pilot object of the source input. -/
abbrev O (I : OriginalInput.{0, 0, 0, 0, 0} l (FinitePrimePlace 2 7)) :
    PaperQPilotObject (l := l) (V := FinitePrimePlace 2 7)
      (Label := ConcreteFiniteTheorem311.finiteLabel l)
      (Choice := ConcreteFiniteTheorem311.ProcessionChoice l)
      I (ConcreteKummerGroup (l := l)) (concreteQPilotStrip (l := l)) :=
  paperQPilotObjectConcrete (l := l) I

/-- The actual source-theater signed C3 object. -/
abbrev signedC3 (I : OriginalInput.{0, 0, 0, 0, 0} l (FinitePrimePlace 2 7))
    (D : SourcePilotRegionDonors (l := l) (V := FinitePrimePlace 2 7) I) :
    SourcePilotRegionData (l := l) (V := FinitePrimePlace 2 7) I :=
  actualSignedC3 (l := l) (V := FinitePrimePlace 2 7) (I := I) D

/-- The actual theta-packet parameter of the source-theater C3 is 1/5. -/
theorem signedC3_thetaPacket_q
    (I : OriginalInput.{0, 0, 0, 0, 0} l (FinitePrimePlace 2 7))
    (D : SourcePilotRegionDonors (l := l) (V := FinitePrimePlace 2 7) I) :
    (signedC3 I D).thetaPacket.q = (5 : ℝ)⁻¹ := by
  change (c3WithSourceTheaterTheta I D).thetaPacket.q = (5 : ℝ)⁻¹
  rw [c3WithSourceTheaterTheta_q I D,
    LeanFormal.IUT.IUTII.Frobenioid.Example36.SourceTheaterCarrier.gaussianFiveThetaQ_eq_inv_five]

/-- The actual signed average of the source-theater C3 in terms of the Gaussian
weight sum and the label cardinality (the content of
SignedAverageBoundActual.actualSignedC3_signedAverage_eq_log5_mul_sum_div_card,
re-proved here because that module has no olean in the current build set). -/
theorem signedAverage_eq_log5_mul_weightSum_div_card
    (I : OriginalInput.{0, 0, 0, 0, 0} l (FinitePrimePlace 2 7))
    (D : SourcePilotRegionDonors (l := l) (V := FinitePrimePlace 2 7) I) :
    (c3ThetaSignedProcession (signedC3 I D)).average =
      Real.log (5 : ℝ) *
        (sourceThetaWeightSum l / (c3ThetaCard (l := l) : ℝ)) := by
  rw [S1931SourceHaarSignedAverageActual.signedAverage_eq_neg]
  rw [signedC3_thetaPacket_q I D]
  rw [Real.log_inv]
  ring

/-- The exact numeric reduction of hcomp.  For any paper signed hull whose
procession average is the actual source-theater signed average, the concrete
source comparison (hcomp) is exactly the numeric bad-q inequality

  log 5 * (W / card) <= sourceBadQAbsLog I.initial.

This is the concrete instance of
ConcreteSourceComparisonNumericActual.concreteComparison_iff_gaussSum_le_badQAbsLog. -/
theorem concreteComparison_iff_weightSum_le_badQAbsLog
    (I : OriginalInput.{0, 0, 0, 0, 0} l (FinitePrimePlace 2 7))
    (D : SourcePilotRegionDonors (l := l) (V := FinitePrimePlace 2 7) I)
    (P : PaperSignedHull X label)
    (hP : P.procession.average =
      (c3ThetaSignedProcession (signedC3 I D)).average) :
    concreteSourceComparison (O I) P ↔
      Real.log (5 : ℝ) *
          (sourceThetaWeightSum l / (c3ThetaCard (l := l) : ℝ)) ≤
        sourceBadQAbsLog I.initial := by
  unfold concreteSourceComparison
  rw [paperQPilotObjectConcrete_qPilotLogVolume]
  rw [hP]
  rw [signedAverage_eq_log5_mul_weightSum_div_card I D]
  rw [sourceQPilotSignedLog]
  constructor <;> intro h <;> linarith

/-! ## 6. The reduction: minimal input implies hcomp -/

/-- Main reduction.  The minimal input (analytic Tate input + source
qParameter/order agreement + bad-q data) implies hcomp, given the Gaussian
coefficient bound log 5 * (W / card) <= 2 log 5 for the label l.

The coefficient bound is a pure property of the Gaussian weight sum; it is not
implied by the Tate input and it is false for l >= 7
(W / card = lStar * (lStar + 1) / 3 >= 4), so it is an explicit hypothesis.  At
l.value = 5 it is the identity W / card = 2 and is discharged in Section 8. -/
theorem hcomp_of_minimalInput
    (I : OriginalInput.{0, 0, 0, 0, 0} l (FinitePrimePlace 2 7))
    (D : SourcePilotRegionDonors (l := l) (V := FinitePrimePlace 2 7) I)
    (P : PaperSignedHull X label)
    (T : SourceNativeInitialThetaData.{0} l)
    [Fintype (Bad (nativePlaceSelection T))]
    (hP : P.procession.average =
      (c3ThetaSignedProcession (signedC3 I D)).average)
    (H : HcompMinimalInput I T)
    (hcoeff : Real.log (5 : ℝ) *
        (sourceThetaWeightSum l / (c3ThetaCard (l := l) : ℝ)) ≤
      2 * Real.log 5) :
    concreteSourceComparison (O I) P :=
  (concreteComparison_iff_weightSum_le_badQAbsLog I D P hP).mpr
    (le_trans hcoeff
      (two_log5_le_sourceBadQAbsLog I T H.sourceQ.alignment H.badQ))

/-- The Tate component is not consumed by the numeric comparison.  hcomp follows
from the source q agreement and the bad-q data alone; the analytic Tate input
plays no role in the inequality.  (It is required for the geometric meaning of
the q parameters; see S2681MissingTateQNumericLink.) -/
theorem hcomp_of_agreement_badQ
    (I : OriginalInput.{0, 0, 0, 0, 0} l (FinitePrimePlace 2 7))
    (D : SourcePilotRegionDonors (l := l) (V := FinitePrimePlace 2 7) I)
    (P : PaperSignedHull X label)
    (T : SourceNativeInitialThetaData.{0} l)
    [Fintype (Bad (nativePlaceSelection T))]
    (hP : P.procession.average =
      (c3ThetaSignedProcession (signedC3 I D)).average)
    (hQ : HcompSourceQAgreement I T)
    (hbad : HcompBadQData T)
    (hcoeff : Real.log (5 : ℝ) *
        (sourceThetaWeightSum l / (c3ThetaCard (l := l) : ℝ)) ≤
      2 * Real.log 5) :
    concreteSourceComparison (O I) P :=
  (concreteComparison_iff_weightSum_le_badQAbsLog I D P hP).mpr
    (le_trans hcoeff
      (two_log5_le_sourceBadQAbsLog I T hQ.alignment hbad))

/-! ## 7. The converse up to the named numeric inputs -/

/-- Converse.  hcomp recovers the bad-q data once the Gaussian coefficient
lower bound 2 log 5 <= log 5 * (W / card) is supplied, together with the source
q agreement.  This is the exact direction that the coefficient identity at
l = 5 closes (Section 8). -/
theorem badQData_of_hcomp_of_coefficient
    (I : OriginalInput.{0, 0, 0, 0, 0} l (FinitePrimePlace 2 7))
    (D : SourcePilotRegionDonors (l := l) (V := FinitePrimePlace 2 7) I)
    (P : PaperSignedHull X label)
    (T : SourceNativeInitialThetaData.{0} l)
    [Fintype (Bad (nativePlaceSelection T))]
    (hP : P.procession.average =
      (c3ThetaSignedProcession (signedC3 I D)).average)
    (halign : ∃ e : I.initial.badPlaces ≃ Bad (nativePlaceSelection T),
      ∀ b : I.initial.badPlaces,
        |Real.log (I.initial.reduction.qParameter b)| =
          baseQLogMagnitude T (e b))
    (hcoeff : 2 * Real.log 5 ≤ Real.log (5 : ℝ) *
        (sourceThetaWeightSum l / (c3ThetaCard (l := l) : ℝ)))
    (hcomp : concreteSourceComparison (O I) P) :
    HcompBadQData T := by
  have h1 :=
    (concreteComparison_iff_weightSum_le_badQAbsLog I D P hP).mp hcomp
  have h2 : 2 * Real.log 5 ≤ sourceBadQAbsLog I.initial := le_trans hcoeff h1
  rw [sourceBadQAbsLog_eq_baseQTotalLogMagnitude I T halign] at h2
  exact h2

/-! ## 8. The l = 5 coefficient identity and the exact equivalence -/

/-- The Gaussian weight sum only depends on l.value. -/
theorem sourceThetaWeightSum_congr {l l' : PrimeGeFive} (h : l.value = l'.value) :
    sourceThetaWeightSum l = sourceThetaWeightSum l' := by
  unfold sourceThetaWeightSum
  rw [h]

/-- The label cardinality only depends on l.value. -/
theorem c3ThetaCard_congr {l l' : PrimeGeFive} (h : l.value = l'.value) :
    c3ThetaCard (l := l) = c3ThetaCard (l := l') := by
  unfold c3ThetaCard
  rw [h]

/-- The Gaussian weight sum at the prime label 5 is 10: the signed labels are
-2, -1, 0, 1, 2 with Gaussian exponents 4, 1, 0, 1, 4.  The computation is
transported to Fl 5 and checked by the kernel (decide); no native_decide. -/
theorem sourceThetaWeightSum_five :
    sourceThetaWeightSum fivePrimeLabelInverseJ = 10 := by
  unfold sourceThetaWeightSum
  have hnat :
      (∑ j : SignedLabel fivePrimeLabelInverseJ.value,
        (gaussExponent j.1).toNat) = 10 := by
    rw [Fintype.sum_equiv (SignedLabel.equiv fivePrimeLabelInverseJ)
      (fun j : SignedLabel fivePrimeLabelInverseJ.value =>
        (gaussExponent j.1).toNat)
      (fun x : Fl fivePrimeLabelInverseJ.value =>
        (gaussExponent ((SignedLabel.equiv fivePrimeLabelInverseJ).symm x).1).toNat)
      (by intro j; rw [Equiv.symm_apply_apply])]
    decide
  have hreal :
      (∑ j : SignedLabel fivePrimeLabelInverseJ.value,
        ((gaussExponent j.1).toNat : ℝ)) = 10 := by
    have hcast := congrArg (fun n : Nat => (n : ℝ)) hnat
    push_cast at hcast
    simpa using hcast
  simpa using hreal

/-- The weight sum at l.value = 5 is 10. -/
theorem sourceThetaWeightSum_eq_ten_of_value_eq_five (hl : l.value = 5) :
    sourceThetaWeightSum l = 10 :=
  (sourceThetaWeightSum_congr
    (l' := fivePrimeLabelInverseJ)
    (by rw [hl, fivePrimeLabelInverseJ_value])).trans sourceThetaWeightSum_five

/-- The label cardinality at l.value = 5 is 5. -/
theorem c3ThetaCard_eq_five_of_value_eq (hl : l.value = 5) :
    c3ThetaCard (l := l) = 5 := by
  unfold c3ThetaCard
  rw [SignedLabel.card_signedLabel, hl]

/-- The Gaussian coefficient at l.value = 5 is exactly 2. -/
theorem weightSum_div_card_eq_two_of_value_eq_five (hl : l.value = 5) :
    sourceThetaWeightSum l / (c3ThetaCard (l := l) : ℝ) = 2 := by
  rw [sourceThetaWeightSum_eq_ten_of_value_eq_five hl,
    c3ThetaCard_eq_five_of_value_eq hl]
  norm_num

/-- hcomp from the minimal input at l.value = 5, with no coefficient side
condition: the coefficient is the proved identity W / card = 2. -/
theorem hcomp_of_minimalInput_five
    (I : OriginalInput.{0, 0, 0, 0, 0} l (FinitePrimePlace 2 7))
    (D : SourcePilotRegionDonors (l := l) (V := FinitePrimePlace 2 7) I)
    (P : PaperSignedHull X label)
    (T : SourceNativeInitialThetaData.{0} l)
    [Fintype (Bad (nativePlaceSelection T))]
    (hP : P.procession.average =
      (c3ThetaSignedProcession (signedC3 I D)).average)
    (hl : l.value = 5)
    (H : HcompMinimalInput I T) :
    concreteSourceComparison (O I) P :=
  hcomp_of_minimalInput I D P T hP H
    (by rw [weightSum_div_card_eq_two_of_value_eq_five hl]; linarith)

/-- The exact equivalence at l.value = 5.  Given the source q agreement and a
paper hull whose procession average is the actual source-theater signed average,
hcomp is equivalent to the bad-q data:

  concreteSourceComparison O P  <->  2 log 5 <= baseQTotalLogMagnitude T.

So the minimal input of the hcomp prerequisite chain, at l = 5, is exactly
(analytic Tate input) + (source q agreement) + (bad-q data), with the bad-q data
an exact necessary-and-sufficient numeric condition. -/
theorem hcomp_iff_badQData_five
    (I : OriginalInput.{0, 0, 0, 0, 0} l (FinitePrimePlace 2 7))
    (D : SourcePilotRegionDonors (l := l) (V := FinitePrimePlace 2 7) I)
    (P : PaperSignedHull X label)
    (T : SourceNativeInitialThetaData.{0} l)
    [Fintype (Bad (nativePlaceSelection T))]
    (hP : P.procession.average =
      (c3ThetaSignedProcession (signedC3 I D)).average)
    (hl : l.value = 5)
    (halign : ∃ e : I.initial.badPlaces ≃ Bad (nativePlaceSelection T),
      ∀ b : I.initial.badPlaces,
        |Real.log (I.initial.reduction.qParameter b)| =
          baseQLogMagnitude T (e b)) :
    concreteSourceComparison (O I) P ↔ HcompBadQData T := by
  constructor
  · intro hcomp
    refine badQData_of_hcomp_of_coefficient I D P T hP halign ?_ hcomp
    rw [weightSum_div_card_eq_two_of_value_eq_five hl]
    linarith
  · intro hbad
    refine (concreteComparison_iff_weightSum_le_badQAbsLog I D P hP).mpr ?_
    rw [weightSum_div_card_eq_two_of_value_eq_five hl]
    have h2 := two_log5_le_sourceBadQAbsLog I T halign hbad
    linarith

/-! ## 9. Exact missing-object ledger -/

/-- The Tate input's numeric link to the source q parameters: at each bad
place, the completion q is the order-th power of the inverse-j Tate parameter at
that place.  This is the geometric identification that the Tate input would
supply; it is not proved in the tree and it is not used by hcomp (the source q
parameters are already pinned by the source reduction clause
S1280ReductionClause_qParameter_eq, i.e. q_b = (1/5) ^ order_b). -/
def S2681MissingTateQNumericLink (T : SourceNativeInitialThetaData.{0} l) : Prop :=
  ∀ b : Bad (nativePlaceSelection T),
    ∃ (w : NumberField.FinitePlace T.arithmetic.F)
      (hw : NumberFieldFinitePlace.comap (k := T.arithmetic.Fmod) w ∈
        (nativePlaceSelection T).V_mod_bad),
      ∃ parameter : FinitePlaceQCandidate w,
        Nonempty (CurveIndexedTateUniformization T.arithmetic.curve w parameter) ∧
          baseQLogMagnitude T b =
            ((parameter.order : ℝ) * Real.log (residueNormBase w))

/-- The exact Gaussian sum closed form still missing for l > 5
(gaussExponentSum = lStar * (lStar + 1) * (2 * lStar + 1) / 3); its absence is
the only reason the coefficient bound stays a hypothesis in Section 6. -/
def S2681MissingGaussSumClosedForm (l : PrimeGeFive) : Prop :=
  sourceThetaWeightSum l =
    ((lStar l.value * (lStar l.value + 1) * (2 * lStar l.value + 1) : Nat) : ℝ) / 3

/-! ## 10. Axiom audit -/

#print axioms sourceBadQAbsLog_eq_baseQTotalLogMagnitude
#print axioms two_log5_le_sourceBadQAbsLog
#print axioms hcompBadQData_of_card_ge_five
#print axioms signedAverage_eq_log5_mul_weightSum_div_card
#print axioms concreteComparison_iff_weightSum_le_badQAbsLog
#print axioms hcomp_of_minimalInput
#print axioms hcomp_of_agreement_badQ
#print axioms badQData_of_hcomp_of_coefficient
#print axioms sourceThetaWeightSum_five
#print axioms weightSum_div_card_eq_two_of_value_eq_five
#print axioms hcomp_of_minimalInput_five
#print axioms hcomp_iff_badQData_five

end LeanFormal.IUT.XiFPaper.S2681HcompMinimalInputActual
end
