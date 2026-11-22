import tmp.sheaf.xif.paper.S663ActualAverageNormalizedHaarActual
import LeanFormal.IUT.Foundations.Theta.SignedLabelEquiv

/-! # S715: audit of S663's normalized-Haar theta surrogate

S663 chooses the Haar scale from the target average `a`:
  s663Measure a = exp(a - unitLog - log nu(unit)) • nu,
so the interface equation logVolume hull = ofReal a holds by construction.
The `hnormal` field of s663PaperSignedHull is therefore supplied by this
scaled measure, not by the actual C6 Haar normalization.
Separately, s663Average averages the positive theta magnitudes over
SignedLabel (card l), while the paper procession is over F_l^x (card l-1).
This file records the exact formulas and the missing paper bridge.
-/

noncomputable section
open scoped BigOperators
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 3000000

namespace LeanFormal.IUT.XiFPaper.S715S663SurrogateAuditActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.N8C6ActualIQ
open LeanFormal.IUT.XiFPaper
open LeanFormal.IUT.XiFPaper.S663ActualAverageNormalizedHaarActual
open LeanFormal.IUT.XiFPaper.S657RootSignedHullIndependentActual
open MeasureTheory

universe ua uv uK uW uX
variable {l : PrimeGeFive}
variable {K : Type uK} [Field K] [NumberField K] {p : Nat} [Fact p.Prime]
variable {iota : Type uv} [Fintype iota] {W : iota → Type uW}
variable (places : (i : iota) → W i → FinitePlaceAtPrime K p)
variable (tuple : (i : iota) → W i)
variable [MeasurableSpace (ArithmeticTensorTupleBlock places tuple)]
variable [BorelSpace (ArithmeticTensorTupleBlock places tuple)]
variable (nu : Measure (ArithmeticTensorTupleBlock places tuple))
variable [Measure.IsAddHaarMeasure nu]
variable (T : SourceNativeInitialThetaData.{0} l)
variable (b : Bad (nativePlaceSelection T))

/-- The S663 interface equation is built from the chosen scale, for every target a. -/
theorem s663Interface_target_builtin (a : Real) :
    (s663Interface (K := K) (p := p) places tuple nu a).logVolume
        (s663Interface (K := K) (p := p) places tuple nu a).hull =
      ENNReal.ofReal a :=
  s663Interface_logVolume_hull (K := K) (p := p) places tuple nu a

/-- The hnormal field of S663 is exactly the built-in interface equation. -/
theorem s663PaperSignedHull_hnormal_is_builtin :
    (s663PaperSignedHull (l := l) (K := K) (p := p) places tuple nu T b).ambient.logVolume
        (s663PaperSignedHull (l := l) (K := K) (p := p) places tuple nu T b).ambient.hull =
      ENNReal.ofReal (s663Average T b) :=
  (s663PaperSignedHull (l := l) (K := K) (p := p) places tuple nu T b).hull_logVolume_eq_average

/-- Exact weighted-sum formula for the S663 average. -/
theorem s663Average_eq_sum_div_card :
    s663Average T b =
      (∑ j : SignedLabel l.value, rootThetaMagnitudeValue T b j) /
        (Fintype.card (SignedLabel l.value) : Real) := by
  unfold s663Average WeightedValues.average rootThetaMagnitudeProcession
  rw [div_one, div_eq_mul_inv]
  change (∑ j : SignedLabel l.value,
      (Fintype.card (SignedLabel l.value) : Real)⁻¹ *
        rootThetaMagnitudeValue T b j) =
    (∑ j : SignedLabel l.value, rootThetaMagnitudeValue T b j) *
      (Fintype.card (SignedLabel l.value) : Real)⁻¹
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- Paper-style average over F_l^x: divide the same nonzero theta values by
card(SignedLabel)-1 instead of card(SignedLabel). -/
noncomputable def paperUnitThetaAverage : Real :=
  (∑ j : SignedLabel l.value, rootThetaMagnitudeValue T b j) /
    ((Fintype.card (SignedLabel l.value) : Real) - 1)

/-- Exact ratio between S663's average and the F_l^x average. -/
theorem s663Average_eq_paperUnitThetaAverage_mul_ratio :
    s663Average T b =
      paperUnitThetaAverage (l := l) T b *
        (((Fintype.card (SignedLabel l.value) : Real) - 1) /
          (Fintype.card (SignedLabel l.value) : Real)) := by
  rw [s663Average_eq_sum_div_card]
  unfold paperUnitThetaAverage
  have hcard : Fintype.card (SignedLabel l.value) = l.value := SignedLabel.card_signedLabel l
  have hl5 : 5 ≤ l.value := l.ge_five
  have hcpos : (0 : Real) < (Fintype.card (SignedLabel l.value) : Real) := by
    rw [hcard]
    exact_mod_cast (by omega : 0 < l.value)
  have hc1pos : (0 : Real) < (Fintype.card (SignedLabel l.value) : Real) - 1 := by
    rw [hcard]
    exact sub_pos.mpr (by exact_mod_cast (by omega : 1 < l.value))
  have hcne : (Fintype.card (SignedLabel l.value) : Real) ≠ 0 := ne_of_gt hcpos
  have hc1ne : (Fintype.card (SignedLabel l.value) : Real) - 1 ≠ 0 := ne_of_gt hc1pos
  field_simp [hcne, hc1ne]

/-- Exact missing bridge: S663's average must equal the paper F_l^x theta
average (and the actual C6 Haar normalization must produce it independently). -/
structure S663PaperThetaHullBridge where
  paperThetaAverage : Real
  paperThetaAverage_eq_unit : paperThetaAverage = paperUnitThetaAverage (l := l) T b
  s663Average_eq_paper : s663Average T b = paperThetaAverage
  c6_haar_independent : Prop

def S663PaperThetaHullBridgeRequired : Prop :=
  Nonempty (S663PaperThetaHullBridge (l := l) T b)

end LeanFormal.IUT.XiFPaper.S715S663SurrogateAuditActual
end
