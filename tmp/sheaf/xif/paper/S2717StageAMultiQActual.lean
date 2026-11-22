import tmp.sheaf.xif.paper.S2716StageAQInterfaceActual
import tmp.sheaf.xif.paper.S2708MultiPlaceQPilotActual
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Data.Finset.BooleanAlgebra

/-!
# S2717: Stage A q-normalization for the multi-q source q-pilot

## Layer and consumers

Stage A (Corollary 3.12, q-side normalization) for the **multi-place** source
q-pilot scalar.  This file is the multi-q counterpart of
`tmp/sheaf/xif/paper/S2716StageAQInterfaceActual.lean`: it feeds the actual
paper multi-place q-pilot log-volume into the Step-XI certificate interface
`arithmeticTupleIQHullCertificateQ`.

Motivation: the S2708 multi-place donor computes the paper scalar
`paperQPilotLogVolume_multi D = -sum_b |log q_b|` over the actual finite bad
index.  S2709MultiQLogFormulaActual proves the scalar identity
`sum_i |log q_i| = -log (prod_i q_i)` for positive contracting factors; S2711
and S2714 use the multi-place scalar in the hcomp transfer.  This file turns
that scalar into a single positive Real q-parameter
`qProduct D = prod_b |q_b|` whose logarithm is the mixed sum
`sum_b log |q_b|`, and proves `-|log (qProduct D)| = paperQPilotLogVolume_multi D`.

## What is actual here

* `qProduct D := prod_{b : I.initial.badPlaces} |D.qFamily b|`, over the actual
  finite bad index `I.initial.bad_finite` (no singleton substitution).
* Each factor is positive and has absolute value `< 1` (source
  `qParameter_nonzero`, `qParameter_contracting`, and `D.qFamily_eq`).
* `qProduct_pos`, `qProduct_le_one`, `qProduct_log`,
  `qProduct_abs_log`, and the Stage A endpoint
  `stageAQParameterSigned_multi D = paperQPilotLogVolume_multi D`.
* The Stage A certificate/link-evidence/Cor312 conclusion at `qProduct D`.

## The missing nonemptiness hypothesis, exactly

The current source contract `SourceDefinition31Data` stores an arbitrary
`badPlaces : Type` with a `Fintype` (`bad_finite`) but **no**
`Nonempty badPlaces` field (the newer contracts `SourcePlaceSelection` /
`SourceInitialThetaData` do carry `V_mod_bad_nonempty`, but the
`OriginalInput` used by S2708 does not).  For empty `badPlaces` the empty
product is `1`, so `Real.log (qProduct D) = 0` and the Stage A hypothesis
`Real.log qParameter ≠ 0` cannot hold.  Accordingly:

* `qProduct_lt_one_of_nonempty` and `qProduct_log_ne_zero_of_nonempty` take
  `hbad : Nonempty I.initial.badPlaces`;
* `qProduct_lt_one_iff_nonempty` and `qProduct_log_ne_zero_iff_nonempty`
  prove that these are *exactly* equivalent to the missing nonemptiness;
* `qProduct_eq_one_of_isEmpty`, `paperQPilotLogVolume_multi_eq_zero_of_isEmpty`,
  and `stageAQParameterSigned_multi_eq_zero_of_isEmpty` record the degenerate
  empty-index case.

The unqualified `qProduct_lt_one` is therefore not provable from the source
contract, and the Stage A certificate instantiations below consequently take
`hbad`.  (The textbook lemma `Finset.prod_lt_one` additionally requires
`IsOrderedCancelMonoid R` and `MulLeftStrictMono R`, which do not hold for
`Real` under multiplication; the strict bound here is proved instead with
`Finset.prod_lt_prod` for positive factors.)

No placeholder proofs, no added logical assumptions, no native decision
procedure, and no vacuous proposition are used; no existing file is modified.
-/

noncomputable section
open scoped BigOperators

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 16000000

namespace LeanFormal.IUT.XiFPaper.S2717StageAMultiQActual

open MeasureTheory
open LeanFormal.IUT
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput

universe u v w ua uv upi umon ui

/-! ## 1. The multi-q positive Real q-parameter -/

section MultiQ

variable {l : PrimeGeFive} {V : Type uv}
variable {I : OriginalInput.{ua, uv, upi, umon, ui} l V}

/-- The actual finite bad index `I.initial.bad_finite` is used as the local
`Fintype` instance for every sum and product over `I.initial.badPlaces`. -/
noncomputable local instance s2717BadPlacesFintype :
    Fintype I.initial.badPlaces := I.initial.bad_finite

/-- The positive Real q-parameter of a multi-place q-pilot donor: the product
of the absolute per-place q-parameters over the actual finite bad index.

Its logarithm is the mixed sum `sum_b log |q_b|`, and the Stage A endpoint
`-|log (qProduct D)|` is the multi-place paper q-pilot log-volume
`-sum_b |log q_b|` (see `qProduct_abs_log`). -/
noncomputable def qProduct (D : MultiPlaceQPilotDonor I) : Real :=
  ∏ b : I.initial.badPlaces, |D.qFamily b|

@[simp] theorem qProduct_def (D : MultiPlaceQPilotDonor I) :
    qProduct D = ∏ b : I.initial.badPlaces, |D.qFamily b| := rfl

theorem qFamily_ne_zero (D : MultiPlaceQPilotDonor I)
    (b : I.initial.badPlaces) : D.qFamily b ≠ 0 := by
  rw [D.qFamily_eq]
  exact I.initial.q_parameter_nonzero b

theorem qFamily_abs_pos (D : MultiPlaceQPilotDonor I)
    (b : I.initial.badPlaces) : 0 < |D.qFamily b| :=
  abs_pos.mpr (qFamily_ne_zero D b)

theorem qFamily_abs_lt_one (D : MultiPlaceQPilotDonor I)
    (b : I.initial.badPlaces) : |D.qFamily b| < 1 := by
  have h := I.initial.q_parameter_contracting b
  rw [Real.norm_eq_abs] at h
  rwa [D.qFamily_eq]

theorem qProduct_pos (D : MultiPlaceQPilotDonor I) : 0 < qProduct D := by
  rw [qProduct_def]
  exact Finset.prod_pos (fun b _ => qFamily_abs_pos D b)

theorem qProduct_le_one (D : MultiPlaceQPilotDonor I) : qProduct D ≤ 1 := by
  rw [qProduct_def]
  exact Finset.prod_le_one (fun b _ => le_of_lt (qFamily_abs_pos D b))
    (fun b _ => le_of_lt (qFamily_abs_lt_one D b))

/-- Strict contractivity needs the bad index to be nonempty.  This uses
`Finset.prod_lt_prod` (positive factors), not `Finset.prod_lt_one`, which
requires `IsOrderedCancelMonoid Real` / `MulLeftStrictMono Real` and is not
available for `Real` under multiplication. -/
theorem qProduct_lt_one_of_nonempty (D : MultiPlaceQPilotDonor I)
    (hbad : Nonempty I.initial.badPlaces) : qProduct D < 1 := by
  rw [qProduct_def]
  obtain ⟨b⟩ := hbad
  have hlt : ∃ c ∈ (Finset.univ : Finset I.initial.badPlaces),
      |D.qFamily c| < (1 : Real) :=
    ⟨b, Finset.mem_univ b, qFamily_abs_lt_one D b⟩
  have h := Finset.prod_lt_prod
    (s := (Finset.univ : Finset I.initial.badPlaces))
    (f := fun c : I.initial.badPlaces => |D.qFamily c|)
    (g := fun _ => (1 : Real))
    (fun c _ => qFamily_abs_pos D c)
    (fun c _ => le_of_lt (qFamily_abs_lt_one D c))
    hlt
  simpa using h

theorem qProduct_eq_one_of_isEmpty [IsEmpty I.initial.badPlaces]
    (D : MultiPlaceQPilotDonor I) : qProduct D = 1 := by
  rw [qProduct_def]
  simp

/-- The strict contractivity is *exactly* the nonemptiness of the source bad
index: this is the missing source hypothesis, made explicit. -/
theorem qProduct_lt_one_iff_nonempty (D : MultiPlaceQPilotDonor I) :
    qProduct D < 1 ↔ Nonempty I.initial.badPlaces := by
  refine ⟨fun h => ?_, qProduct_lt_one_of_nonempty D⟩
  by_contra hne
  haveI : IsEmpty I.initial.badPlaces := ⟨fun b => hne ⟨b⟩⟩
  rw [qProduct_eq_one_of_isEmpty D] at h
  exact (lt_irrefl (1 : Real)) h

/-! ## 2. Logarithm and the Stage A signed q endpoint -/

theorem qProduct_log (D : MultiPlaceQPilotDonor I) :
    Real.log (qProduct D) =
      ∑ b : I.initial.badPlaces, Real.log |D.qFamily b| := by
  rw [qProduct_def]
  exact Real.log_prod (fun b _ => abs_ne_zero.mpr (qFamily_ne_zero D b))

theorem qProduct_log_ne_zero_of_nonempty (D : MultiPlaceQPilotDonor I)
    (hbad : Nonempty I.initial.badPlaces) :
    Real.log (qProduct D) ≠ 0 :=
  ne_of_lt (Real.log_neg (qProduct_pos D) (qProduct_lt_one_of_nonempty D hbad))

theorem qProduct_log_ne_zero_iff_nonempty (D : MultiPlaceQPilotDonor I) :
    Real.log (qProduct D) ≠ 0 ↔ Nonempty I.initial.badPlaces := by
  refine ⟨fun h => ?_, qProduct_log_ne_zero_of_nonempty D⟩
  by_contra hne
  haveI : IsEmpty I.initial.badPlaces := ⟨fun b => hne ⟨b⟩⟩
  apply h
  rw [qProduct_eq_one_of_isEmpty D, Real.log_one]

/-- The Stage A signed q endpoint of `qProduct D` is the actual multi-place
paper q-pilot log-volume. -/
theorem qProduct_abs_log (D : MultiPlaceQPilotDonor I) :
    -|Real.log (qProduct D)| = paperQPilotLogVolume_multi D := by
  have hlog : Real.log (qProduct D) ≤ 0 :=
    Real.log_nonpos (le_of_lt (qProduct_pos D)) (qProduct_le_one D)
  rw [abs_of_nonpos hlog, neg_neg, qProduct_log]
  change (∑ b : I.initial.badPlaces, Real.log |D.qFamily b|) =
    -(∑ b : I.initial.badPlaces, |Real.log (D.qFamily b)|)
  rw [← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl (fun b _ => ?_)
  have hqlog : Real.log (D.qFamily b) < 0 := by
    rw [← Real.log_abs]
    exact Real.log_neg (qFamily_abs_pos D b) (qFamily_abs_lt_one D b)
  rw [Real.log_abs, abs_of_neg hqlog, neg_neg]

/-- The Stage A signed q endpoint, defined by applying the S2716
`arithmeticTupleQParameterSigned` to `qProduct D`. -/
noncomputable def stageAQParameterSigned_multi
    (D : MultiPlaceQPilotDonor I) : Real :=
  arithmeticTupleQParameterSigned (qProduct D)

/-- The multi-q Stage A endpoint is exactly the multi-place paper q-pilot
log-volume: `-|log (prod_b |q_b|)| = -sum_b |log q_b|`. -/
theorem stageAQParameterSigned_multi_eq (D : MultiPlaceQPilotDonor I) :
    stageAQParameterSigned_multi D = paperQPilotLogVolume_multi D := by
  unfold stageAQParameterSigned_multi arithmeticTupleQParameterSigned
  exact qProduct_abs_log D

theorem stageAQParameterSigned_multi_neg (D : MultiPlaceQPilotDonor I)
    (hbad : Nonempty I.initial.badPlaces) :
    stageAQParameterSigned_multi D < 0 :=
  arithmeticTupleQParameterSigned_neg
    (qProduct_log_ne_zero_of_nonempty D hbad)

theorem paperQPilotLogVolume_multi_eq_zero_of_isEmpty
    [IsEmpty I.initial.badPlaces] (D : MultiPlaceQPilotDonor I) :
    paperQPilotLogVolume_multi D = 0 := by
  rw [← qProduct_abs_log D, qProduct_eq_one_of_isEmpty D, Real.log_one,
    abs_zero, neg_zero]

theorem stageAQParameterSigned_multi_eq_zero_of_isEmpty
    [IsEmpty I.initial.badPlaces] (D : MultiPlaceQPilotDonor I) :
    stageAQParameterSigned_multi D = 0 := by
  rw [stageAQParameterSigned_multi_eq,
    paperQPilotLogVolume_multi_eq_zero_of_isEmpty D]

end MultiQ

/-! ## 3. The Stage A certificate at the multi-q q-parameter -/

section StageACertificate

variable {l : PrimeGeFive} {V : Type uv}
variable {I : OriginalInput.{ua, uv, upi, umon, ui} l V}

variable {K : Type u} [Field K] [NumberField K] {p : ℕ} [Fact p.Prime]
variable {ι : Type v} [Fintype ι] {W : ι → Type w}
variable (places : (i : ι) → W i → FinitePlaceAtPrime K p)
variable (tuple : (i : ι) → W i)
variable [MeasurableSpace (ArithmeticTensorTupleBlock places tuple)]
variable (μ : Measure (ArithmeticTensorTupleBlock places tuple))
variable [BorelSpace (ArithmeticTensorTupleBlock places tuple)]
variable [Measure.IsAddHaarMeasure μ]

/-- The S2716 Stage A interface certificate instantiated at the multi-q
q-parameter `qProduct D`.  The hypothesis `hbad` is the actual nonemptiness
of the source bad index; it is exactly equivalent to
`Real.log (qProduct D) ≠ 0` (`qProduct_log_ne_zero_iff_nonempty`). -/
noncomputable def arithmeticTupleIQHullCertificateQ_multi
    {label : Type*} [Fintype label]
    (pt : label → ArithmeticTensorTupleBlock places tuple)
    (hpt : ∀ i, pt i ∈
      (arithmeticTupleIQHullLogVolumeInterfaceScaledUnit places tuple μ).imageSet)
    (data : WeightedValues label)
    (hvalue : ∀ i, data.value i =
      (iqHullFiniteHull
        (arithmeticTupleIQHullLogVolumeInterfaceScaledUnit places tuple μ)
        pt hpt).volume i)
    (hw : ∀ i, 0 ≤ data.weight i)
    (D : MultiPlaceQPilotDonor I)
    (hbad : Nonempty I.initial.badPlaces) :
    StepXIFiniteCertificate label :=
  arithmeticTupleIQHullCertificateQ places tuple μ pt hpt data hvalue hw
    (qProduct D) (qProduct_log_ne_zero_of_nonempty D hbad)

/-- The qSigned projection of the multi-q Stage A certificate is the
multi-place paper q-pilot log-volume. -/
theorem arithmeticTupleIQHullCertificateQ_multi_qSigned
    {label : Type*} [Fintype label]
    (pt : label → ArithmeticTensorTupleBlock places tuple)
    (hpt : ∀ i, pt i ∈
      (arithmeticTupleIQHullLogVolumeInterfaceScaledUnit places tuple μ).imageSet)
    (data : WeightedValues label)
    (hvalue : ∀ i, data.value i =
      (iqHullFiniteHull
        (arithmeticTupleIQHullLogVolumeInterfaceScaledUnit places tuple μ)
        pt hpt).volume i)
    (hw : ∀ i, 0 ≤ data.weight i)
    (D : MultiPlaceQPilotDonor I)
    (hbad : Nonempty I.initial.badPlaces) :
    (arithmeticTupleIQHullCertificateQ_multi places tuple μ pt hpt data hvalue hw
      D hbad).qSigned = paperQPilotLogVolume_multi D := by
  unfold arithmeticTupleIQHullCertificateQ_multi
  rw [arithmeticTupleIQHullCertificateQ_qSigned]
  exact qProduct_abs_log D

/-- The multi-q certificate is definitionally the S2716 certificate instantiated
at the positive Real q-parameter `qProduct D`. -/
theorem arithmeticTupleIQHullCertificateQ_multi_eq
    {label : Type*} [Fintype label]
    (pt : label → ArithmeticTensorTupleBlock places tuple)
    (hpt : ∀ i, pt i ∈
      (arithmeticTupleIQHullLogVolumeInterfaceScaledUnit places tuple μ).imageSet)
    (data : WeightedValues label)
    (hvalue : ∀ i, data.value i =
      (iqHullFiniteHull
        (arithmeticTupleIQHullLogVolumeInterfaceScaledUnit places tuple μ)
        pt hpt).volume i)
    (hw : ∀ i, 0 ≤ data.weight i)
    (D : MultiPlaceQPilotDonor I)
    (hbad : Nonempty I.initial.badPlaces) :
    arithmeticTupleIQHullCertificateQ_multi places tuple μ pt hpt data hvalue hw
        D hbad =
      arithmeticTupleIQHullCertificateQ places tuple μ pt hpt data hvalue hw
        (qProduct D) (qProduct_log_ne_zero_of_nonempty D hbad) := rfl

/-- The S2716 link evidence for the multi-q Stage A certificate. -/
noncomputable def arithmeticTupleIQHullLinkEvidenceQ_multi
    {label : Type*} [Fintype label]
    (pt : label → ArithmeticTensorTupleBlock places tuple)
    (hpt : ∀ i, pt i ∈
      (arithmeticTupleIQHullLogVolumeInterfaceScaledUnit places tuple μ).imageSet)
    (data : WeightedValues label)
    (hvalue : ∀ i, data.value i =
      (iqHullFiniteHull
        (arithmeticTupleIQHullLogVolumeInterfaceScaledUnit places tuple μ)
        pt hpt).volume i)
    (hw : ∀ i, 0 ≤ data.weight i)
    (D : MultiPlaceQPilotDonor I)
    (hbad : Nonempty I.initial.badPlaces)
    (ipl she apt : Prop) (hipl : ipl) (hshe : she) (hapt : apt) :
    FiniteStepXILinkEvidence
      (arithmeticTupleIQHullCertificateQ_multi places tuple μ pt hpt data hvalue
        hw D hbad) :=
  arithmeticTupleIQHullLinkEvidenceQ places tuple μ pt hpt data hvalue hw
    (qProduct D) (qProduct_log_ne_zero_of_nonempty D hbad)
    ipl she apt hipl hshe hapt

/-- The multi-q link evidence is definitionally the S2716 link evidence
instantiated at `qProduct D`. -/
theorem arithmeticTupleIQHullLinkEvidenceQ_multi_eq
    {label : Type*} [Fintype label]
    (pt : label → ArithmeticTensorTupleBlock places tuple)
    (hpt : ∀ i, pt i ∈
      (arithmeticTupleIQHullLogVolumeInterfaceScaledUnit places tuple μ).imageSet)
    (data : WeightedValues label)
    (hvalue : ∀ i, data.value i =
      (iqHullFiniteHull
        (arithmeticTupleIQHullLogVolumeInterfaceScaledUnit places tuple μ)
        pt hpt).volume i)
    (hw : ∀ i, 0 ≤ data.weight i)
    (D : MultiPlaceQPilotDonor I)
    (hbad : Nonempty I.initial.badPlaces)
    (ipl she apt : Prop) (hipl : ipl) (hshe : she) (hapt : apt) :
    arithmeticTupleIQHullLinkEvidenceQ_multi places tuple μ pt hpt data hvalue
        hw D hbad ipl she apt hipl hshe hapt =
      arithmeticTupleIQHullLinkEvidenceQ places tuple μ pt hpt data hvalue hw
        (qProduct D) (qProduct_log_ne_zero_of_nonempty D hbad)
        ipl she apt hipl hshe hapt := rfl

/-- The S2716 Corollary 3.12 conclusion for the multi-q Stage A certificate. -/
theorem arithmeticTupleIQHullCor312ConclusionQ_multi
    {label : Type*} [Fintype label]
    (pt : label → ArithmeticTensorTupleBlock places tuple)
    (hpt : ∀ i, pt i ∈
      (arithmeticTupleIQHullLogVolumeInterfaceScaledUnit places tuple μ).imageSet)
    (data : WeightedValues label)
    (hvalue : ∀ i, data.value i =
      (iqHullFiniteHull
        (arithmeticTupleIQHullLogVolumeInterfaceScaledUnit places tuple μ)
        pt hpt).volume i)
    (hw : ∀ i, 0 ≤ data.weight i)
    (D : MultiPlaceQPilotDonor I)
    (hbad : Nonempty I.initial.badPlaces)
    (ipl she apt : Prop) (hipl : ipl) (hshe : she) (hapt : apt) :
    Cor312Conclusion
      ((arithmeticTupleIQHullCertificateQ_multi places tuple μ pt hpt data hvalue
          hw D hbad).toContract
        (arithmeticTupleIQHullLinkEvidenceQ_multi places tuple μ pt hpt data hvalue
          hw D hbad ipl she apt hipl hshe hapt)) :=
  arithmeticTupleIQHullCor312ConclusionQ places tuple μ pt hpt data hvalue hw
    (qProduct D) (qProduct_log_ne_zero_of_nonempty D hbad)
    ipl she apt hipl hshe hapt

end StageACertificate

/-! ## 4. Axiom audit surface -/

#check qProduct
#check qProduct_pos
#check qProduct_le_one
#check qProduct_lt_one_of_nonempty
#check qProduct_lt_one_iff_nonempty
#check qProduct_eq_one_of_isEmpty
#check qProduct_log
#check qProduct_log_ne_zero_of_nonempty
#check qProduct_log_ne_zero_iff_nonempty
#check qProduct_abs_log
#check stageAQParameterSigned_multi
#check stageAQParameterSigned_multi_eq
#check stageAQParameterSigned_multi_neg
#check paperQPilotLogVolume_multi_eq_zero_of_isEmpty
#check stageAQParameterSigned_multi_eq_zero_of_isEmpty
#check arithmeticTupleIQHullCertificateQ_multi
#check arithmeticTupleIQHullCertificateQ_multi_eq
#check arithmeticTupleIQHullCertificateQ_multi_qSigned
#check arithmeticTupleIQHullLinkEvidenceQ_multi
#check arithmeticTupleIQHullLinkEvidenceQ_multi_eq
#check arithmeticTupleIQHullCor312ConclusionQ_multi

#print axioms qProduct_abs_log
#print axioms stageAQParameterSigned_multi_eq
#print axioms arithmeticTupleIQHullCertificateQ_multi_eq
#print axioms arithmeticTupleIQHullCertificateQ_multi_qSigned
#print axioms arithmeticTupleIQHullLinkEvidenceQ_multi_eq
#print axioms arithmeticTupleIQHullCor312ConclusionQ_multi

end LeanFormal.IUT.XiFPaper.S2717StageAMultiQActual
end
