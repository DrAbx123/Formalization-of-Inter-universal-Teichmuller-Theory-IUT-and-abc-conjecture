import LeanFormal.IUT.ABCBridge.Geometry.FinitePlaceIQHullInterfaceScaledUnit
import LeanFormal.IUT.IUTIII.Corollary312.StepXI.CertificateHullWiring

/-!
# Step-XI certificate from the actual arithmetic-tuple IQ hull

This file connects the proved `IQHullLogVolumeInterface` on the actual
finite-place arithmetic tensor tuple to the finite Step-XI certificate
consumer.  The upper-bound datum is the real Haar log-volume of the actual
canonical hull, and its finiteness is the already proved compactness fact for
the canonical hull.

The lower endpoint is fixed at `q = -1`.  This makes the certificate's
`hq` field automatically true because `ENNReal.ofReal (-1) = 0`.  Thus the
`hq` slot is vacuous here and does **not** encode a signed q-side comparison
with the theta image union.  What is actually supplied by this file is the
finite hull upper bound, together with the certificate and Corollary 3.12
assembly.  No source N5 realization, paper-level `1,circ U` compactness, or
actual signed `q` comparison is claimed.
-/

set_option linter.unusedSectionVars false

namespace LeanFormal.IUT.NumberFieldFinitePlace

open MeasureTheory
open LeanFormal.IUT

noncomputable section

universe u v w

variable {K : Type u} [Field K] [NumberField K] {p : ℕ} [Fact p.Prime]
variable {ι : Type v} [Fintype ι] {V : ι → Type w}
variable (places : (i : ι) → V i → FinitePlaceAtPrime K p) (tuple : (i : ι) → V i)
variable [MeasurableSpace (ArithmeticTensorTupleBlock places tuple)]
variable (μ : Measure (ArithmeticTensorTupleBlock places tuple))

/-! ## 1. The actual hull theta -/

/-- The real Haar log-volume of the actual canonical arithmetic-tuple hull. -/
def arithmeticTupleIQHullTheta : ℝ :=
  (haarLogVolume μ (arithmeticTupleCanonicalHull places tuple)).toReal

/-- The actual hull theta is nonnegative. -/
theorem arithmeticTupleIQHullTheta_nonneg :
    0 ≤ arithmeticTupleIQHullTheta places tuple μ :=
  ENNReal.toReal_nonneg

variable [BorelSpace (ArithmeticTensorTupleBlock places tuple)]
variable [Measure.IsAddHaarMeasure μ]

/-! ## 2. The actual finite hull upper bound -/

/-- The hull of the scaled-unit actual interface is the canonical hull. -/
@[simp] theorem arithmeticTupleIQHullLogVolumeInterfaceScaledUnit_hull :
    (arithmeticTupleIQHullLogVolumeInterfaceScaledUnit places tuple μ).hull =
      arithmeticTupleCanonicalHull places tuple :=
  rfl

/-- The log-volume of the scaled-unit actual interface is the Haar log-volume. -/
@[simp] theorem arithmeticTupleIQHullLogVolumeInterfaceScaledUnit_logVolume :
    (arithmeticTupleIQHullLogVolumeInterfaceScaledUnit places tuple μ).logVolume =
      haarLogVolume μ :=
  rfl

/-- The actual canonical hull has finite Haar measure. -/
theorem arithmeticTupleCanonicalHull_measure_lt_top :
    μ (arithmeticTupleCanonicalHull places tuple) < ⊤ :=
  (measure_arithmeticTupleCanonicalRegions_pos_lt_top places tuple μ).1.2

/-- Finiteness of the actual hull log-volume in the scaled-unit interface. -/
theorem arithmeticTupleIQHullLogVolumeInterfaceScaledUnit_hull_logVolume_lt_top :
    (arithmeticTupleIQHullLogVolumeInterfaceScaledUnit places tuple μ).logVolume
      (arithmeticTupleIQHullLogVolumeInterfaceScaledUnit places tuple μ).hull < ⊤ :=
  arithmeticTupleIQHullLogVolumeInterfaceScaledUnit_hull_lt_top places tuple μ

/-- The actual finite hull log-volume is bounded by the `ofReal` of its real
Haar log-volume.  This is the genuine upper-bound datum used by the Step-XI
certificate. -/
theorem arithmeticTupleIQHullLogVolumeInterfaceScaledUnit_hull_le_ofReal_theta :
    (arithmeticTupleIQHullLogVolumeInterfaceScaledUnit places tuple μ).logVolume
        (arithmeticTupleIQHullLogVolumeInterfaceScaledUnit places tuple μ).hull ≤
      ENNReal.ofReal (arithmeticTupleIQHullTheta places tuple μ) := by
  rw [arithmeticTupleIQHullLogVolumeInterfaceScaledUnit_logVolume,
    arithmeticTupleIQHullLogVolumeInterfaceScaledUnit_hull,
    arithmeticTupleIQHullTheta,
    haarLogVolume_of_lt_top (arithmeticTupleCanonicalHull_measure_lt_top places tuple μ)]
  rw [ENNReal.ofReal_toReal (ENNReal.ofReal_ne_top)]

/-- The `q = -1` lower-bound slot of the certificate.  Since
`ENNReal.ofReal (-1) = 0`, this is the vacuous endpoint discussed in the
module header. -/
theorem arithmeticTupleIQHullScaledUnit_hq :
    ENNReal.ofReal (-1 : ℝ) ≤
      (arithmeticTupleIQHullLogVolumeInterfaceScaledUnit places tuple μ).logVolume
        ((arithmeticTupleIQHullLogVolumeInterfaceScaledUnit places tuple μ).imageSet) := by
  rw [ENNReal.ofReal_of_nonpos (by norm_num : (-1 : ℝ) ≤ 0)]
  exact zero_le

/-! ## 3. Certificate and Corollary 3.12 assembly -/

/-- The Step-XI finite certificate obtained from the actual arithmetic-tuple
IQ hull.  The theta endpoint is the finite real hull log-volume, while the
lower endpoint is the vacuous value `q = -1`. -/
noncomputable def arithmeticTupleIQHullCertificate
    {label : Type*} [Fintype label]
    (pt : label → ArithmeticTensorTupleBlock places tuple)
    (hpt : ∀ i, pt i ∈
      (arithmeticTupleIQHullLogVolumeInterfaceScaledUnit places tuple μ).imageSet)
    (data : WeightedValues label)
    (hvalue : ∀ i, data.value i =
      (iqHullFiniteHull
        (arithmeticTupleIQHullLogVolumeInterfaceScaledUnit places tuple μ)
        pt hpt).volume i)
    (hw : ∀ i, 0 ≤ data.weight i) :
    StepXIFiniteCertificate label :=
  iqHullCertificate
    (arithmeticTupleIQHullLogVolumeInterfaceScaledUnit places tuple μ)
    pt hpt data hvalue hw (-1) (arithmeticTupleIQHullTheta places tuple μ)
    (arithmeticTupleIQHullScaledUnit_hq places tuple μ)
    (arithmeticTupleIQHullLogVolumeInterfaceScaledUnit_hull_le_ofReal_theta places tuple μ)
    (arithmeticTupleIQHullTheta_nonneg places tuple μ) (by norm_num)

/-- Link evidence for the actual certificate.  The signed target is the real
hull log-volume; IPL/SHE/APT remain explicit supplied propositions. -/
noncomputable def arithmeticTupleIQHullLinkEvidence
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
    (ipl she apt : Prop) (hipl : ipl) (hshe : she) (hapt : apt) :
    FiniteStepXILinkEvidence
      (arithmeticTupleIQHullCertificate places tuple μ pt hpt data hvalue hw) :=
  iqHullLinkEvidence
    (arithmeticTupleIQHullLogVolumeInterfaceScaledUnit places tuple μ)
    pt hpt data hvalue hw (-1) (arithmeticTupleIQHullTheta places tuple μ)
    (arithmeticTupleIQHullScaledUnit_hq places tuple μ)
    (arithmeticTupleIQHullLogVolumeInterfaceScaledUnit_hull_le_ofReal_theta places tuple μ)
    (arithmeticTupleIQHullTheta_nonneg places tuple μ) (by norm_num)
    ipl she apt hipl hshe hapt

/-- The Corollary 3.12 conclusion obtained from the actual arithmetic-tuple
IQ certificate and explicit IPL/SHE/APT evidence. -/
theorem arithmeticTupleIQHullCor312Conclusion
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
    (ipl she apt : Prop) (hipl : ipl) (hshe : she) (hapt : apt) :
    Cor312Conclusion
      ((arithmeticTupleIQHullCertificate places tuple μ pt hpt data hvalue hw).toContract
        (arithmeticTupleIQHullLinkEvidence places tuple μ pt hpt data hvalue hw
          ipl she apt hipl hshe hapt)) :=
  cor312_of_finite_certificate
    (arithmeticTupleIQHullCertificate places tuple μ pt hpt data hvalue hw)
    (arithmeticTupleIQHullLinkEvidence places tuple μ pt hpt data hvalue hw
      ipl she apt hipl hshe hapt)

end

end LeanFormal.IUT.NumberFieldFinitePlace
