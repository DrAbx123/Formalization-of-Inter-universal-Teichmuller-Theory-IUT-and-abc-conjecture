import LeanFormal.IUT.ABCBridge.Geometry.FinitePlaceIQHullCertificateActual

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.checkUnivs false

namespace LeanFormal.IUT.NumberFieldFinitePlace

open MeasureTheory
open LeanFormal.IUT

universe u v w

variable {K : Type u} [Field K] [NumberField K] {p : ℕ} [Fact p.Prime]
variable {ι : Type v} [Fintype ι] {V : ι → Type w}
variable (places : (i : ι) → V i → FinitePlaceAtPrime K p) (tuple : (i : ι) → V i)
variable [MeasurableSpace (ArithmeticTensorTupleBlock places tuple)]
variable (μ : Measure (ArithmeticTensorTupleBlock places tuple))
variable [BorelSpace (ArithmeticTensorTupleBlock places tuple)]
variable [Measure.IsAddHaarMeasure μ]

/-- Stage A signed q endpoint: the actual negative absolute logarithmic q-value
of a positive q-parameter. -/
def arithmeticTupleQParameterSigned (qParameter : Real) : Real :=
  -|Real.log qParameter|

theorem arithmeticTupleQParameterSigned_neg
    {qParameter : Real} (hq : Real.log qParameter ≠ 0) :
    arithmeticTupleQParameterSigned qParameter < 0 :=
  neg_lt_zero.mpr (abs_pos.mpr hq)

theorem arithmeticTupleQParameterSigned_ofReal_le
    {qParameter : Real} (hq : Real.log qParameter ≠ 0) :
    ENNReal.ofReal (arithmeticTupleQParameterSigned qParameter) ≤
      (arithmeticTupleIQHullLogVolumeInterfaceScaledUnit places tuple μ).logVolume
        (arithmeticTupleIQHullLogVolumeInterfaceScaledUnit places tuple μ).imageSet := by
  rw [ENNReal.ofReal_of_nonpos
    (le_of_lt (arithmeticTupleQParameterSigned_neg hq))]
  exact zero_le

/-- The Step-XI certificate with the non-vacuous Stage A q endpoint
`q = -|log qParameter|`, replacing the vacuous `q = -1`. -/
noncomputable def arithmeticTupleIQHullCertificateQ
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
    (qParameter : Real) (hq : Real.log qParameter ≠ 0) :
    StepXIFiniteCertificate label :=
  iqHullCertificate
    (arithmeticTupleIQHullLogVolumeInterfaceScaledUnit places tuple μ)
    pt hpt data hvalue hw (arithmeticTupleQParameterSigned qParameter)
    (arithmeticTupleIQHullTheta places tuple μ)
    (arithmeticTupleQParameterSigned_ofReal_le places tuple μ hq)
    (arithmeticTupleIQHullLogVolumeInterfaceScaledUnit_hull_le_ofReal_theta places tuple μ)
    (arithmeticTupleIQHullTheta_nonneg places tuple μ)
    (arithmeticTupleQParameterSigned_neg hq)

theorem arithmeticTupleIQHullCertificateQ_qSigned
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
    (qParameter : Real) (hq : Real.log qParameter ≠ 0) :
    (arithmeticTupleIQHullCertificateQ places tuple μ pt hpt data hvalue hw
      qParameter hq).qSigned = -|Real.log qParameter| := rfl

noncomputable def arithmeticTupleIQHullLinkEvidenceQ
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
    (qParameter : Real) (hq : Real.log qParameter ≠ 0)
    (ipl she apt : Prop) (hipl : ipl) (hshe : she) (hapt : apt) :
    FiniteStepXILinkEvidence
      (arithmeticTupleIQHullCertificateQ places tuple μ pt hpt data hvalue hw
        qParameter hq) :=
  iqHullLinkEvidence
    (arithmeticTupleIQHullLogVolumeInterfaceScaledUnit places tuple μ)
    pt hpt data hvalue hw (arithmeticTupleQParameterSigned qParameter)
    (arithmeticTupleIQHullTheta places tuple μ)
    (arithmeticTupleQParameterSigned_ofReal_le places tuple μ hq)
    (arithmeticTupleIQHullLogVolumeInterfaceScaledUnit_hull_le_ofReal_theta places tuple μ)
    (arithmeticTupleIQHullTheta_nonneg places tuple μ)
    (arithmeticTupleQParameterSigned_neg hq)
    ipl she apt hipl hshe hapt

theorem arithmeticTupleIQHullCor312ConclusionQ
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
    (qParameter : Real) (hq : Real.log qParameter ≠ 0)
    (ipl she apt : Prop) (hipl : ipl) (hshe : she) (hapt : apt) :
    Cor312Conclusion
      ((arithmeticTupleIQHullCertificateQ places tuple μ pt hpt data hvalue hw
          qParameter hq).toContract
        (arithmeticTupleIQHullLinkEvidenceQ places tuple μ pt hpt data hvalue hw
          qParameter hq ipl she apt hipl hshe hapt)) :=
  cor312_of_finite_certificate
    (arithmeticTupleIQHullCertificateQ places tuple μ pt hpt data hvalue hw
      qParameter hq)
    (arithmeticTupleIQHullLinkEvidenceQ places tuple μ pt hpt data hvalue hw
      qParameter hq ipl she apt hipl hshe hapt)

#check arithmeticTupleIQHullCertificateQ
#check arithmeticTupleIQHullCertificateQ_qSigned
#check arithmeticTupleIQHullCor312ConclusionQ
#print axioms arithmeticTupleIQHullCertificateQ_qSigned
#print axioms arithmeticTupleIQHullCor312ConclusionQ
end LeanFormal.IUT.NumberFieldFinitePlace
end
