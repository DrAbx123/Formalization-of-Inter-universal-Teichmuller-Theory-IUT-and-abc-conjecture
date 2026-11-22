/- F-side bad place index (paper V(F)^bad 全 fiber) for kurt 的 F-side 体积链重建。

BadF := {P : Ideal (O_F) // P ∈ badFPrimeSet T}（Finset subtype, Fintype 自动）;
fPlaceWeight := f_P/[F:Q] = paperDifferentWeight F P;
badFPlaceOf := 该 prime 对应的 F-位（复用 QPilotMagnitudeV2Actual.badFPlaceOfIdeal）;
ksDifferentOrderF := F_P 的 localDifferentGenerator 的 localNormOrder（paper d_i 的 F 版）。 -/
import Mathlib.Tactic
import tmp.sheaf.xif.paper.Mzk1ULQPilotMagnitudeV2Actual
import tmp.sheaf.xif.paper.Mzk1HT82PaperWeightDiffActual
import LeanFormal.IUT.Foundations.LocalFields.IntegralTraceDualTensorInclusion
import LeanFormal.IUT.Foundations.LocalFields.LocalDifferentNormOrder
import LeanFormal.IUT.ABCBridge.Geometry.FinitePlaceCommonPrimeCompletion

noncomputable section
set_option linter.unusedSectionVars false
namespace LeanFormal.IUT.XiFPaper.Mzk1ULFBadPlaceIndexActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.VbadPlaceIndexingActual
open LeanFormal.IUT.XiFPaper.Mzk1ULBadFPrimeSetActual
open LeanFormal.IUT.XiFPaper.Mzk1ULQPilotMagnitudeV2Actual
open LeanFormal.IUT.XiFPaper.Mzk1HT82AbsDifferentSumActual
open LeanFormal.IUT.XiFPaper.Mzk1HT82PaperWeightDiffActual
open LeanFormal.IUT.LocalFieldLogarithm
open NumberField
open scoped BigOperators

variable {l : PrimeGeFive} (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]

/-- F-side bad prime index（V(F)^bad 全 fiber）。 -/
def BadF : Type := {P : Ideal (𝓞 (T.arithmetic.F)) // P ∈ badFPrimeSet T}

instance badFFintype : Fintype (BadF T) :=
  Fintype.subtype (badFPrimeSet T) (fun _ => Iff.rfl)

/-- F 权重 f_P/[F:Q]。 -/
noncomputable def fPlaceWeight (x : BadF T) : ℝ :=
  paperDifferentWeight T.arithmetic.F x.1

/-- F-位（由 prime 构造）。 -/
noncomputable def badFPlaceOf (x : BadF T) : NumberField.FinitePlace T.arithmetic.F :=
  badFPlaceOfIdeal (T := T)
    (b := Classical.choose (Finset.mem_biUnion.mp x.2))
    x.1 (Classical.choose_spec (Finset.mem_biUnion.mp x.2)).2

/-- badFPlaceOf 的 comap 到 Fmod 是选取的 moduli 位。 -/
theorem badFPlaceOf_comap (x : BadF T) :
    NumberFieldFinitePlace.comap (k := T.arithmetic.Fmod) (badFPlaceOf T x) =
      (Classical.choose (Finset.mem_biUnion.mp x.2)).1 :=
  badFPlaceOfIdeal_comap (T := T)
    (b := Classical.choose (Finset.mem_biUnion.mp x.2))
    x.1 (Classical.choose_spec (Finset.mem_biUnion.mp x.2)).2

/-- F 权重非负。 -/
theorem fPlaceWeight_nonneg (x : BadF T) : 0 ≤ fPlaceWeight T x := by
  unfold fPlaceWeight paperDifferentWeight
  exact div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)

/-- F_P 的 local different order（paper d_i 的 F 版）。 -/
noncomputable def ksDifferentOrderF (x : BadF T) : ℝ := by
  let p := (completionRationalPrime (badFPlaceOf T x)).val
  letI : Fact p.Prime := completionRationalPrime_fact (badFPlaceOf T x)
  exact localNormOrder p
    ((LeanFormal.IUT.IntegralTraceDualTensorInclusion.localDifferentGenerator (p := p)
      (L := CommonPrimeCompletion (⟨badFPlaceOf T x, rfl⟩ : FinitePlaceAtPrime T.arithmetic.F p))) :
      CommonPrimeCompletion (⟨badFPlaceOf T x, rfl⟩ : FinitePlaceAtPrime T.arithmetic.F p))

end LeanFormal.IUT.XiFPaper.Mzk1ULFBadPlaceIndexActual