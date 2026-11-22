/- F-side hstepVIII instantiation (single file, no new packetV):
   instantiate Mzk1ULStepVIIILambdaActual.hstepVIII_of_collectionLayer_gen with
   w := nativeBadLocalWeight and Vh_b := ulQVFamPacketV T b (varpi b) (Phi b) (actual qVFamily packet
   volume from Mzk1ULPacketHullActual), then feed Mzk1UCC4PaperActual.uc_c4_actual_paper_letters.
   The per-label hVh comparison is the explicit StepV input (from ulQVFamPacketV_le_paperBound
   + label bridge); the per-b actual packet value is ulQVFamPacketV, not actualLocalHullLog. -/
import tmp.sheaf.xif.paper.Mzk1ULStepVIIILambdaActual
import tmp.sheaf.xif.paper.Mzk1ULPacketHullActual
import tmp.sheaf.xif.paper.Mzk1UCC4PaperActual
import tmp.sheaf.xif.paper.Mzk1ULHpktActual
import tmp.sheaf.xif.paper.Mzk1URThetaHullActual
import Mathlib.Analysis.SpecialFunctions.Log.Basic

noncomputable section
set_option linter.unusedSectionVars false
open scoped BigOperators
namespace LeanFormal.IUT.XiFPaper.FsideHstepVIIIInstantiationActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.VbadPlaceIndexingActual
open LeanFormal.IUT.XiFPaper.Mzk1ULStepVIIILambdaActual
open LeanFormal.IUT.XiFPaper.Mzk1ULPacketHullActual
open LeanFormal.IUT.XiFPaper.Mzk1ULHpktActual
open LeanFormal.IUT.XiFPaper.Mzk1ULPaperLettersActual
open LeanFormal.IUT.XiFPaper.Mzk1ULEModActual
open LeanFormal.IUT.XiFPaper.Mzk1UCEtaPrmActual
open LeanFormal.IUT.XiFPaper.Mzk1P6C3C4Actual
open LeanFormal.IUT.XiFPaper.PaperLevelXiFTargetActual
open NumberField

variable {l : PrimeGeFive} (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]
variable [∀ b : Bad (nativePlaceSelection T), MeasurableSpace (qVFamTensorBlock T b)]
variable [∀ b : Bad (nativePlaceSelection T), BorelSpace (qVFamTensorBlock T b)]

/-- nativeBadLocalWeight is nonnegative (inverse completion degree). -/
theorem nativeBadLocalWeight_nonneg' (b : Bad (nativePlaceSelection T)) :
    0 ≤ nativeBadLocalWeight T b := by
  rw [nativeBadLocalWeight_eq_inv]
  exact inv_nonneg.mpr (Nat.cast_nonneg _)

/-- F-side hstepVIII for the actual qVFamily packet values ulQVFamPacketV. -/
theorem hstepVIII_of_ulQVFamPacketV
    (varpi : ∀ b : Bad (nativePlaceSelection T), CommonPrimeCompletion ((qVFamTensorPlaces T b) () ()))
    (Phi : ∀ b : Bad (nativePlaceSelection T), Set (qVFamTensorBlock T b ≃ₗ[ℚ_[qVFamTensorP T b]] qVFamTensorBlock T b))
    (X : Nat) (hX : ∀ b : Bad (nativePlaceSelection T), qVFamTensorP T b ≤ X)
    (n : Nat) (hn : 2 ≤ n) (hl_eq : (l.value : Real) = 2 * (n : Real) + 1)
    (S_ar M d_mod : Real) (hl : 5 ≤ (l.value : Real))
    (D Q T' logP : Bad (nativePlaceSelection T) → Real)
    (hlogP : ∀ b, logP b = Real.log (qVFamTensorP T b : Real))
    (hVh : ∀ i, ∀ label ∈ Finset.Icc 1 n,
      ulQVFamPacketV T i (varpi i) (Phi i) ≤ LeanFormal.IUT.IUTIV.StepVProcessionAverage.collectionBound
        (2 * (n : Real) + 1) (D i) (Q i) (logP i) (T' i) label)
    (hM : M = (∑ i : Bad (nativePlaceSelection T), nativeBadLocalWeight T i * Q i) /
      (2 * (l.value : Real)))
    (hD0 : ∀ i, 0 ≤ D i) (hQ0 : ∀ i, 0 ≤ Q i) (hT0 : ∀ i, 0 ≤ T' i)
    (hii : (1 + 4 / (l.value : Real)) *
      (∑ i : Bad (nativePlaceSelection T), nativeBadLocalWeight T i * D i)
      ≤ (1 + 4 / (l.value : Real)) * S_ar + 2 * Real.log (l.value : Real) + 46)
    (hsQ : (4 / (l.value : Real)) *
      ((∑ i : Bad (nativePlaceSelection T), nativeBadLocalWeight T i) *
        Real.log (LeanFormal.IUT.XiFPaper.Mzk1URSmallPrimeActual.urSQ X : Real))
      ≤ (8 * d_mod / (l.value : Real)) * S_ar + 6)
    (hS_ar : 0 ≤ S_ar) (hd_mod : 1 ≤ d_mod) :
    (∑ i : Bad (nativePlaceSelection T),
        nativeBadLocalWeight T i * ulQVFamPacketV T i (varpi i) (Phi i)) ≤
      Mzk1P6C3C4Actual.kappa (l.value : Real) *
        ((1 + 12 * d_mod / (l.value : Real)) * S_ar +
          2 * Real.log (l.value : Real) + 56 -
          Mzk1P6C3C4Actual.cL (l.value : Real) *
            (∑ i : Bad (nativePlaceSelection T), nativeBadLocalWeight T i * Q i) +
          (20 / 3) * (∑ i : Bad (nativePlaceSelection T), nativeBadLocalWeight T i * T' i)) - M := by
  have hconst : ∀ i, (1 / (n : Real)) *
      (∑ _label ∈ Finset.Icc 1 n, ulQVFamPacketV T i (varpi i) (Phi i)) =
      ulQVFamPacketV T i (varpi i) (Phi i) := by
    intro i
    rw [Finset.sum_const, Nat.card_Icc]
    have hn0 : (n : Real) ≠ 0 := by positivity
    simp only [nsmul_eq_mul, Nat.add_sub_cancel]
    field_simp
  have h := hstepVIII_of_collectionLayer_gen (T := T) (nativeBadLocalWeight T)
    (nativeBadLocalWeight_nonneg' T) X hX n hn hl_eq S_ar M d_mod hl
    D Q T' logP (fun i _ => ulQVFamPacketV T i (varpi i) (Phi i)) hlogP hVh
    hM hD0 hQ0 hT0 hii hsQ hS_ar hd_mod
  simpa only [hconst] using h

/-- C4 F-side terminal via the actual qVFamily packet values. -/
theorem C4_fside_of_ulQVFamPacketV
    (varpi : ∀ b : Bad (nativePlaceSelection T), CommonPrimeCompletion ((qVFamTensorPlaces T b) () ()))
    (Phi : ∀ b : Bad (nativePlaceSelection T), Set (qVFamTensorBlock T b ≃ₗ[ℚ_[qVFamTensorP T b]] qVFamTensorBlock T b))
    (Q M : Real) (hl : 5 ≤ (l.value : Real))
    (hP5 : -M ≤ actualThetaHullLogRoot (l := l) T)
    (htheta : actualThetaHullLogRoot (l := l) T ≤
      LeanFormal.IUT.XiFPaper.Mzk1UCC3ProducerActual.ucWeightedHpkt
        (nativeBadLocalWeight T) (fun b => ulQVFamPacketV T b (varpi b) (Phi b)))
    (hstepVIII :
      (∑ i : Bad (nativePlaceSelection T),
          nativeBadLocalWeight T i * ulQVFamPacketV T i (varpi i) (Phi i)) ≤
        Mzk1P6C3C4Actual.kappa (l.value : Real) *
          ((1 + 12 * Mzk1ULPaperLettersActual.dMod T / (l.value : Real)) *
              Mzk1ULPaperLettersActual.SAr_tripodal T +
            2 * Real.log (l.value : Real) + 56 -
            Mzk1P6C3C4Actual.cL (l.value : Real) * Q +
            (20 / 3) * Mzk1ULHpktActual.paperLstarLogs
              (Mzk1ULEModActual.eMod T) (l.value : Real)) - M) :
    Mzk1P6C3C4Actual.cL (l.value : Real) * Q ≤
      Mzk1ULHpktActual.paperA (Mzk1ULPaperLettersActual.dMod T) (l.value : Real)
        (Mzk1ULPaperLettersActual.SAr_tripodal T)
        (Mzk1ULHpktActual.paperEar (Mzk1ULEModActual.eMod T) (l.value : Real)
          Mzk1UCEtaPrmActual.etaPrm) :=
  Mzk1UCC4PaperActual.uc_c4_actual_paper_letters (T := T)
    (nativeBadLocalWeight T) (fun b => ulQVFamPacketV T b (varpi b) (Phi b))
    (fun b => ulQVFamPacketV T b (varpi b) (Phi b))
    (nativeBadLocalWeight_nonneg' T) (fun _ => le_refl _) Q M hl hP5 htheta hstepVIII

#print axioms nativeBadLocalWeight_nonneg'
#print axioms hstepVIII_of_ulQVFamPacketV
#print axioms C4_fside_of_ulQVFamPacketV

end LeanFormal.IUT.XiFPaper.FsideHstepVIIIInstantiationActual