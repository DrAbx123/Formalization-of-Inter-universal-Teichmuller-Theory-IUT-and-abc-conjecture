/- U-C T-side instance: letters-level hviTable instantiation.

Low-risk glue: this file instantiates david's hviTable_instance (DONE 17:33:43)
with the label letters from Mzk1URLabelDataActual, so the conclusion has the
exact collectionBound/RHS letters needed by hstepVIII_of_collectionLayer.

Consumption recipe for the (A) hVh (documented, NOT asserted here): at the T-side
concrete point, for each b : Bad (nativePlaceSelection T) take
  D b : LabelStepVHullData (qVFamTensorPlaces T b) qVFamTensorTuple istar_b
        (exceptional b) n (oq b) eMod
then
  V b j := urCollHullLogFamily (qVFamTensorPlaces T b) qVFamTensorTuple (D b).hullSet j
  hVh b label hlabel := hVh_of_labelData (qVFamTensorPlaces T b) qVFamTensorTuple istar_b
        (exceptional b) n hn (oq b) eMod (D b) label hlabel
and the letters below with P b := qVFamTensorP T b, Dl b := labelD (labelDifferentSum
(qVFamTensorPlaces T b) qVFamTensorTuple) (labelLogP (P b)), Ql b := labelQ (oq b)
(labelLogP (P b)), Tl b := labelTl eMod (2n+1).  The concrete wiring additionally
needs the per-b prime instance Fact (qVFamTensorP T b).Prime and the index istar_b;
those are checked in the next batch (no hidden assumptions here).  Lead ruling (x):
-/
import tmp.sheaf.xif.paper.Mzk1ULHviTableInstanceActual
import tmp.sheaf.xif.paper.Mzk1URLabelDataActual
import tmp.sheaf.xif.paper.Mzk1ULPacketHullActual
import tmp.sheaf.xif.paper.QVFamTensorCoefficientActual
import Mathlib.Tactic

noncomputable section
open scoped BigOperators
namespace LeanFormal.IUT.XiFPaper.Mzk1ULStepVIIIInstancesActual

open LeanFormal.IUT
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.Mzk1ULHviTableInstanceActual
open LeanFormal.IUT.XiFPaper.Mzk1URLabelDataActual
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.XiFPaper.PaperLevelXiFTargetActual
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.VbadPlaceIndexingActual
open LeanFormal.IUT.XiFPaper.Mzk1ULPacketHullActual

variable {l : PrimeGeFive} (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]

/-- Letters-level hviTable: with logP b := labelLogP (P b), david's
hviTable_instance gives the aggregated collectionBound upper bound with the
label letters.  No normalisation and no extra hypothesis. -/
theorem hviTable_instance_letters
    (n : ℕ) (hn : 2 ≤ n) (P : Bad (nativePlaceSelection T) → ℕ)
    (Dl Ql Tl : Bad (nativePlaceSelection T) → ℝ)
    (V : Bad (nativePlaceSelection T) → ℕ → ℝ)
    (hVh : ∀ b : Bad (nativePlaceSelection T), ∀ label ∈ Finset.Icc 1 n,
      V b label ≤ LeanFormal.IUT.IUTIV.StepVProcessionAverage.collectionBound
        (2 * (n : ℝ) + 1) (Dl b) (Ql b) (labelLogP (P b)) (Tl b) label) :
    hviTableS3014 T V n ≤
      (1 / (n : ℝ)) * (∑ j ∈ Finset.Icc 1 n,
        LeanFormal.IUT.IUTIV.StepVProcessionAverage.collectionBound
          (2 * (n : ℝ) + 1)
          (∑ b : Bad (nativePlaceSelection T), nativeBadLocalWeight T b * Dl b)
          (∑ b : Bad (nativePlaceSelection T), nativeBadLocalWeight T b * Ql b)
          (∑ b : Bad (nativePlaceSelection T), nativeBadLocalWeight T b * labelLogP (P b))
          (∑ b : Bad (nativePlaceSelection T), nativeBadLocalWeight T b * Tl b) j) :=
  hviTable_instance T n hn (fun b => labelLogP (P b)) Dl Ql Tl V hVh


end LeanFormal.IUT.XiFPaper.Mzk1ULStepVIIIInstancesActual
end