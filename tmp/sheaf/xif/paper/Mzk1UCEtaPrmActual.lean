/- route §5.4 实际字母 etaPrm（owner david）: accepted donor
iutIVProp16_primeCounting_le_four_thirds_eventually 的见证，及其 pos/π 界；并给
uc_c4_actual 的 eta 侧实例化包装（Q/eMod 仍为实际字母参数）。 -/
import Mathlib.Tactic
import LeanFormal.IUT.IUTIV.Estimates.Section2
import tmp.sheaf.xif.paper.Mzk1UCC4Actual

noncomputable section
namespace LeanFormal.IUT.XiFPaper.Mzk1UCEtaPrmActual

open LeanFormal.IUT.IUTIV.Estimates

/-- paper 的 eta_prm（IUT IV Prop 1.6 的见证，L901-926）。 -/
noncomputable def etaPrm : ℝ :=
  Classical.choose iutIVProp16_primeCounting_le_four_thirds_eventually

/-- eta_prm > 0。 -/
theorem etaPrm_pos : 0 < etaPrm :=
  (Classical.choose_spec iutIVProp16_primeCounting_le_four_thirds_eventually).1

/-- pi(⌊η⌋) <= 4 η/(3 log η) for η >= eta_prm。 -/
theorem primeCounting_le_four_thirds {η : ℝ} (h : etaPrm ≤ η) :
    (Nat.primeCounting ⌊η⌋₊ : ℝ) ≤ 4 * η / (3 * Real.log η) :=
  (Classical.choose_spec iutIVProp16_primeCounting_le_four_thirds_eventually).2 η h

open scoped BigOperators

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.Mzk1UCHpktActual
open LeanFormal.IUT.XiFPaper.Mzk1UCC3ProducerActual
open LeanFormal.IUT.XiFPaper.Mzk1UCC3Actual
open LeanFormal.IUT.XiFPaper.Mzk1ULHpktActual
open LeanFormal.IUT.XiFPaper.Mzk1ULPaperLettersActual
open LeanFormal.IUT.XiFPaper.PaperLevelXiFTargetActual

variable {l : PrimeGeFive} (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]
variable [∀ b, MeasurableSpace (qVFamTensorBlock T b)]
variable [∀ b, BorelSpace (qVFamTensorBlock T b)]

/-- eta 侧已实例化的 C4：eta_prm := etaPrm；Q/eMod/htheta/hstepVIII 为剩余实际字母。 -/
theorem uc_c4_actual_eta {ι : Type*} [Fintype ι] (w V B : ι → ℝ)
    (hw : ∀ i, 0 ≤ w i) (hVB : ∀ i, V i ≤ B i)
    (Q : ℝ) {eMod : Nat} (he : 1 ≤ eMod) (hl : 5 ≤ (l.value : ℝ))
    (htheta : actualThetaHullLogRoot (l := l) T ≤ ucWeightedHpkt w V)
    (hstepVIII :
      (∑ i : ι, w i * B i) ≤
        kappa (l.value : ℝ) * ((1 + 12 * dMod T / (l.value : ℝ)) * SAr_tripodal T
          + 2 * Real.log (l.value : ℝ) + 56
          - cL (l.value : ℝ) * Q
          + (20 / 3) * paperLstarLogs eMod (l.value : ℝ))
          - actualQPilotMagnitudeClassical (l := l) T) :
    cL (l.value : ℝ) * Q ≤ paperA (dMod T) (l.value : ℝ) (SAr_tripodal T)
      (paperEar eMod (l.value : ℝ) etaPrm) :=
  LeanFormal.IUT.XiFPaper.Mzk1UCC4Actual.uc_c4_actual (eMod := eMod) T w V B hw hVB
    etaPrm_pos (fun η h => primeCounting_le_four_thirds h) he etaPrm Q hl le_rfl htheta hstepVIII

#print axioms uc_c4_actual_eta

#print axioms etaPrm_pos
#print axioms primeCounting_le_four_thirds

end LeanFormal.IUT.XiFPaper.Mzk1UCEtaPrmActual