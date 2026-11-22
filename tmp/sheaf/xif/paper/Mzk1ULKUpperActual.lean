/- K-side upper instantiation: feed actual urPacketV_K and hVh into
   Mzk1ULStepVIIILambdaActual.hstepVIII_of_collectionLayer_gen, then compose with
   Mzk1URThetaKC3UpperActual.theta_lam_le_paperRHS.
   No new math: the per-label hVh hypothesis is the DONE hVh shape
   (Mzk1ULHviTableInstanceActual.hVh_of_paperBound_letters conclusion). -/
import tmp.sheaf.xif.paper.Mzk1ULStepVIIILambdaActual
import tmp.sheaf.xif.paper.Mzk1ULThetaMWeightActual
import tmp.sheaf.xif.paper.Mzk1ULHviTableInstanceActual
import tmp.sheaf.xif.paper.Mzk1URSmallPrimeActual
import Mathlib.Analysis.SpecialFunctions.Log.Basic

noncomputable section
set_option linter.unusedSectionVars false
open scoped BigOperators
namespace LeanFormal.IUT.XiFPaper.Mzk1ULKUpperActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.Mzk1URThetaKSideActual
open LeanFormal.IUT.XiFPaper.Mzk1ULStepVIIILambdaActual
open LeanFormal.IUT.XiFPaper.Mzk1P6C3C4Actual
open NumberField

variable {l : PrimeGeFive} (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]
variable [∀ b : Bad (nativePlaceSelection T), MeasurableSpace (qVFamTensorBlock T b)]
variable [∀ b : Bad (nativePlaceSelection T), BorelSpace (qVFamTensorBlock T b)]

/-- hstepVIII with Vh := urPacketV_K (constant in the label). -/
theorem hstepVIII_of_urPacketV
    (w : Bad (nativePlaceSelection T) → Real) (hw : ∀ i, 0 ≤ w i)
    (X : Nat) (hX : ∀ b : Bad (nativePlaceSelection T), qVFamTensorP T b ≤ X)
    (n : Nat) (hn : 2 ≤ n) (hl_eq : (l.value : Real) = 2 * (n : Real) + 1)
    (S_ar M d_mod : Real) (hl : 5 ≤ (l.value : Real))
    (D Q T' logP : Bad (nativePlaceSelection T) → Real)
    (hlogP : ∀ b, logP b = Real.log (qVFamTensorP T b : Real))
    (hVh : ∀ i, ∀ label ∈ Finset.Icc 1 n,
      urPacketV_K (l := l) T i ≤ LeanFormal.IUT.IUTIV.StepVProcessionAverage.collectionBound (2 * (n : Real) + 1)
        (D i) (Q i) (logP i) (T' i) label)
    (hM : M = (∑ i : Bad (nativePlaceSelection T), w i * Q i) / (2 * (l.value : Real)))
    (hD0 : ∀ i, 0 ≤ D i) (hQ0 : ∀ i, 0 ≤ Q i) (hT0 : ∀ i, 0 ≤ T' i)
    (hii : (1 + 4 / (l.value : Real)) *
      (∑ i : Bad (nativePlaceSelection T), w i * D i)
      ≤ (1 + 4 / (l.value : Real)) * S_ar + 2 * Real.log (l.value : Real) + 46)
    (hsQ : (4 / (l.value : Real)) *
      ((∑ i : Bad (nativePlaceSelection T), w i) * Real.log (LeanFormal.IUT.XiFPaper.Mzk1URSmallPrimeActual.urSQ X : Real))
      ≤ (8 * d_mod / (l.value : Real)) * S_ar + 6)
    (hS_ar : 0 ≤ S_ar) (hd_mod : 1 ≤ d_mod) :
    (∑ i : Bad (nativePlaceSelection T), w i * urPacketV_K (l := l) T i) ≤
      Mzk1P6C3C4Actual.kappa (l.value : Real) *
        ((1 + 12 * d_mod / (l.value : Real)) * S_ar +
          2 * Real.log (l.value : Real) + 56 -
          Mzk1P6C3C4Actual.cL (l.value : Real) *
            (∑ i : Bad (nativePlaceSelection T), w i * Q i) +
          (20 / 3) * (∑ i : Bad (nativePlaceSelection T), w i * T' i)) - M := by
  have hconst : ∀ i, (1 / (n : Real)) *
      (∑ _label ∈ Finset.Icc 1 n, urPacketV_K (l := l) T i) =
      urPacketV_K (l := l) T i := by
    intro i
    rw [Finset.sum_const, Nat.card_Icc]
    have hn0 : (n : Real) ≠ 0 := by positivity
    simp only [nsmul_eq_mul, Nat.add_sub_cancel]
    field_simp
  have h := hstepVIII_of_collectionLayer_gen (T := T) w hw X hX n hn hl_eq S_ar M d_mod hl
    D Q T' logP (fun i _ => urPacketV_K (l := l) T i) hlogP
    (fun i label hlabel => hVh i label hlabel) hM hD0 hQ0 hT0 hii hsQ hS_ar hd_mod
  simpa only [hconst] using h

#print axioms hstepVIII_of_urPacketV

end LeanFormal.IUT.XiFPaper.Mzk1ULKUpperActual