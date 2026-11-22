/- D1b consumer: C4 with actual paper letters S_ar := SAr_tripodal T, d_mod := dMod T。

这是 uc_c4_paperConstants_of_p6 的实际字母实例化（S_ar/d_mod 用 Mzk1ULPaperLettersActual 的
实际对象；Q/eta_prm/eMod/eta0/hpi/htheta/hstepVIII 是 route §5.4 的剩余实际义务参数，
不在本包装内假闭合）。供 andrew 的 D1b upper_estimate 直接接线。 -/
import tmp.sheaf.xif.paper.Mzk1UCHpktActual
import tmp.sheaf.xif.paper.Mzk1ULPaperLettersActual
import Mathlib.Tactic

noncomputable section
open scoped BigOperators
namespace LeanFormal.IUT.XiFPaper.Mzk1UCC4Actual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.Mzk1UCC3Actual
open LeanFormal.IUT.XiFPaper.Mzk1UCHpktActual
open LeanFormal.IUT.XiFPaper.Mzk1UCC3ProducerActual
open LeanFormal.IUT.XiFPaper.Mzk1ULHpktActual
open LeanFormal.IUT.XiFPaper.Mzk1ULPaperLettersActual
open LeanFormal.IUT.XiFPaper.PaperLevelXiFTargetActual

variable {l : PrimeGeFive} (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]
variable [∀ b, MeasurableSpace (qVFamTensorBlock T b)]
variable [∀ b, BorelSpace (qVFamTensorBlock T b)]

/-- C4 with actual paper letters: S_ar := SAr_tripodal T，d_mod := dMod T;
Q/eta_prm/eMod/eta0/hpi/htheta/hstepVIII 为剩余实际义务参数。 -/
theorem uc_c4_actual {ι : Type*} [Fintype ι] (w V B : ι → ℝ)
    (hw : ∀ i, 0 ≤ w i) (hVB : ∀ i, V i ≤ B i)
    {η0 : ℝ} (hη0 : 0 < η0)
    (hπ : ∀ η : ℝ, η0 ≤ η →
      (Nat.primeCounting ⌊η⌋₊ : ℝ) ≤ 4 * η / (3 * Real.log η))
    {eMod : Nat} (he : 1 ≤ eMod)
    (eta_prm Q : ℝ) (hl : 5 ≤ (l.value : ℝ)) (heta : η0 ≤ eta_prm)
    (htheta : actualThetaHullLogRoot (l := l) T ≤ ucWeightedHpkt w V)
    (hstepVIII :
      (∑ i : ι, w i * B i) ≤
        LeanFormal.IUT.XiFPaper.Mzk1UCC3Actual.kappa (l.value : ℝ) * ((1 + 12 * dMod T / (l.value : ℝ)) * SAr_tripodal T
          + 2 * Real.log (l.value : ℝ) + 56
          - LeanFormal.IUT.XiFPaper.Mzk1UCC3Actual.cL (l.value : ℝ) * Q
          + (20 / 3) * paperLstarLogs eMod (l.value : ℝ))
          - actualQPilotMagnitudeClassical (l := l) T) :
    LeanFormal.IUT.XiFPaper.Mzk1UCC3Actual.cL (l.value : ℝ) * Q ≤ paperA (dMod T) (l.value : ℝ) (SAr_tripodal T)
      (paperEar eMod (l.value : ℝ) eta_prm) :=
  uc_c4_paperConstants_of_p6 T w V B hw hVB hη0 hπ he eta_prm
    (SAr_tripodal T) Q (dMod T) hl heta htheta hstepVIII

#print axioms uc_c4_actual

end LeanFormal.IUT.XiFPaper.Mzk1UCC4Actual