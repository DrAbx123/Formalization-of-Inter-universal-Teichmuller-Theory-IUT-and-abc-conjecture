/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.Mzk1P0LNormReadoutActual
import tmp.sheaf.xif.paper.Mzk1P0LNormReadoutProductActual
import tmp.sheaf.xif.paper.Mzk1P1NormalizedSourceConditionalActual
import tmp.sheaf.xif.paper.Mzk1P1PaperSumsToS3137BridgeActual
import tmp.sheaf.xif.paper.Mzk1P1PaperSumsA1DataActual
import tmp.sheaf.xif.paper.Mzk1P0LPaperInstanceActual
import tmp.sheaf.xif.paper.BadPlacePaperNormalizedComparisonActual
import tmp.sheaf.xif.paper.QVFamTensorCoefficientActual
import tmp.sheaf.xif.paper.ProcessionNormalizationWeightsActual
import tmp.sheaf.xif.paper.QVFamNormalizedCoefficientBridgeActual
import tmp.sheaf.xif.paper.Mzk1RouteAFinalNoS45WrapperActual
import tmp.sheaf.xif.paper.Mzk1P0QVFamNormBridgeDonorActual
import tmp.sheaf.xif.paper.QVFamTensorCoefficientActual
import tmp.sheaf.xif.paper.QVFamNormalizedCoefficientBridgeActual
import Mathlib.Tactic

/-! # P0/P1: `PaperS3137ReadingDictionary` with constructed (a)(b)(c) and a
**substantive** object lock (not a bare Prop).

(a) theta product identity: green `thetaNormReadProduct_eq_closedForm_sub_one`.
(b) q paper expansion: definitional (rfl).
(c) coefficient equality under S45 ratio=1: green `c_norm_eq_paperCoefficient_sub_normRatio`.
(d) Object lock: substantive data — per-b relative factor `B`, its positivity, the weight
    relation `d_b = B_b * [K_w:F_v]`, the unit-mass equality, and the L/global readout
    sign/unitMass identity.  These equalities are NOT trivially instantiable; the lock is
    kept explicit and never assumed. -/

noncomputable section
open scoped BigOperators ENNReal
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 2000000

namespace LeanFormal.IUT.XiFPaper.Mzk1P0FinalS3137DictionaryActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.XiFPaper.C3LogShellTensorLActual
open LeanFormal.IUT.XiFPaper.Mzk1P0LPaperInstanceActual
open LeanFormal.IUT.XiFPaper.Mzk1P0LNormReadoutActual
open LeanFormal.IUT.XiFPaper.Mzk1P0LNormReadoutProductActual
open LeanFormal.IUT.XiFPaper.Mzk1P1NormalizedSourceConditionalActual
open LeanFormal.IUT.XiFPaper.Mzk1P1PaperSumsToS3137BridgeActual
open LeanFormal.IUT.XiFPaper.Mzk1P1PaperSumsA1DataActual
open LeanFormal.IUT.XiFPaper.ProcessionNormalizationWeightsActual
open LeanFormal.IUT.XiFPaper.QVFamNormalizedCoefficientBridgeActual
open LeanFormal.IUT.XiFPaper.BadPlacePaperNormalizedComparisonActual
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.Mzk1RouteAFinalNoS45WrapperActual
open LeanFormal.IUT.XiFPaper.Mzk1P0QVFamNormBridgeDonorActual
open LeanFormal.IUT.XiFPaper.VbadPlaceIndexingActual
open LeanFormal.IUT.XiFPaper.BadPlaceRationalDegreeFactorActual
open LeanFormal.IUT.XiFPaper.S1915ThetaHullA0Actual
open MeasureTheory

universe ua upi umon ui
variable {l : PrimeGeFive}
variable (I : OriginalInput.{0, 0, upi, umon, ui} l (FinitePrimePlace 2 7))
variable {p : Nat} [Fact p.Prime]
variable (place : FinitePlaceAtPrime (I.initial.arithmetic.Fmod) p)
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]
variable [hM : ∀ b : Bad (nativePlaceSelection T),
  MeasurableSpace (qVFamTensorBlock T b)]
variable [hB : ∀ b : Bad (nativePlaceSelection T),
  BorelSpace (qVFamTensorBlock T b)]
include hM hB

/-- Substantive object lock: actual data-equations between the paper/global and L/local
representations.  Each field is an equality of defined quantities (not `True`). -/
structure PaperS3137ObjectLock
    (I : OriginalInput.{0, 0, upi, umon, ui} l (FinitePrimePlace 2 7))
    (place : FinitePlaceAtPrime (I.initial.arithmetic.Fmod) p)
    (T : SourceNativeInitialThetaData.{0} l)
    [Fintype (Bad (nativePlaceSelection T))] where
  /-- per-b relative factor `B_b`. -/
  B : Bad (nativePlaceSelection T) → Nat
  B_pos : ∀ b, 0 < B b
  /-- Weight relation: `d_b = B_b * [K_w:F_v]`. -/
  weight_relation : ∀ b : Bad (nativePlaceSelection T),
    s1915LocalDegree T b = B b * localCompletionDegree T.arithmetic (nativeBadToKPlace T b)
  /-- Unit-mass equality: the L unit-ball mass is the S1915 product unit mass. -/
  unitMass_eq : actualUnitMassL I place = (s1915UnitMass T).toReal
  /-- L/global readout sign+unitMass identity. -/
  theta_sign : thetaNormReadL I place = thetaNormReadProduct T

/-- The reading dictionary: (a)(b)(c) are constructed; (d) is the substantive lock. -/
structure PaperS3137ReadingDictionary
    (I : OriginalInput.{0, 0, upi, umon, ui} l (FinitePrimePlace 2 7))
    (place : FinitePlaceAtPrime (I.initial.arithmetic.Fmod) p)
    (T : SourceNativeInitialThetaData.{0} l)
    [Fintype (Bad (nativePlaceSelection T))]
    (hM : forall b : Bad (nativePlaceSelection T),
      MeasurableSpace (qVFamTensorBlock T b))
    (hB : forall b : Bad (nativePlaceSelection T),
      BorelSpace (qVFamTensorBlock T b))
    (lock : PaperS3137ObjectLock I place T) where
  theta_product_eq : thetaNormReadProduct T = s1915ClosedForm T - 1
  q_paper_eq : paperNormalizedQPilotSum T =
    ∑ b : Bad (nativePlaceSelection T),
      nativeBadLocalWeight T b *
        (paperNormalizedCoefficient T b * Real.log (qVFamTensorP T b : Real))
  coeff_eq_of_ratio : ∀ b : Bad (nativePlaceSelection T),
    qVFamNormRatio T b = 1 →
      QVFamNormalizedGeneratorSupplyActual.qVFamNormalizedCoefficient T b = paperNormalizedCoefficient T b

/-- Construct (a)(b)(c) from green lemmas; only the lock stays as explicit data. -/
noncomputable def paperS3137ReadingDictionary_of
    (hM : forall b : Bad (nativePlaceSelection T),
      MeasurableSpace (qVFamTensorBlock T b))
    (hB : forall b : Bad (nativePlaceSelection T),
      BorelSpace (qVFamTensorBlock T b))
    (lock : PaperS3137ObjectLock I place T) :
    PaperS3137ReadingDictionary (I := I) (place := place) (T := T)
      (hM := hM) (hB := hB) (lock := lock) where
  theta_product_eq := thetaNormReadProduct_eq_closedForm_sub_one (T := T)
  q_paper_eq := rfl
  coeff_eq_of_ratio := by
    intro b h
    have hc := c_norm_eq_paperCoefficient_sub_normRatio (T := T) (b := b)
    rw [h, Real.log_one, zero_div, sub_zero] at hc
    exact hc

/-- Combined final target: S45 + relative-factor data + substantive object lock give
the paper comparison, the relative-factor data, and the reading dictionary. -/
theorem finalDictionaryCombined
    (S : S45SourceFields (T := T))
    (rel : RelativeFactorTowerData (T := T))
    (lock : PaperS3137ObjectLock I place T) :
    (paperNormalizedThetaSum T ≤ paperNormalizedQPilotSum T) ∧
      RelativeFactorTowerData (T := T) ∧
      Nonempty (PaperS3137ReadingDictionary (I := I) (place := place) (T := T)
        (hM := hM) (hB := hB) (lock := lock)) := by
  refine ⟨?_, rel, ?_⟩
  · rcases S with ⟨Sfields⟩
    exact paperNormalizedComparison_of_sourceFields T Sfields
  · exact ⟨paperS3137ReadingDictionary_of (I := I) (place := place) (T := T) hM hB lock⟩

/-- **Dictionary with S45-free comparison (conditional on the pointwise norm bridge).**
Once the norm bridge is unconditional this drops `S45SourceFields` from the comparison
conjunct; `rel` and `lock` are still consumed. -/
theorem finalDictionaryCombined_ofNormBridge
    (hbridge : ∀ b : Bad (nativePlaceSelection T),
      qVFamNormalizedNorm T b =
        (qVFamDefaultNorm T b) ^
          (1 / (relativeCompletionDegree (k := ℚ) (qVFamTensorPlace T b) : ℝ)))
    (rel : RelativeFactorTowerData (T := T))
    (lock : PaperS3137ObjectLock I place T) :
    (paperNormalizedThetaSum T ≤ paperNormalizedQPilotSum T) ∧
      RelativeFactorTowerData (T := T) ∧
      Nonempty (PaperS3137ReadingDictionary (I := I) (place := place) (T := T)
        (hM := hM) (hB := hB) (lock := lock)) := by
  refine ⟨?_, rel, ?_⟩
  · exact finalPaperNormalizedComparison_noS45_of_norm_bridge T
      (fun b => relativeCompletionDegree (k := ℚ) (qVFamTensorPlace T b))
      (fun b => Nat.succ_le_of_lt (relativeCompletionDegree_pos (k := ℚ) (qVFamTensorPlace T b)))
      (fun b => by simpa using hbridge b)
  · exact ⟨paperS3137ReadingDictionary_of (I := I) (place := place) (T := T) hM hB lock⟩

/-- **Unconditional drop-S combined target.**  The comparison comes from the hull
provider (Route A, no S45 equality); `rel`/`lock` remain consumed. -/
theorem finalDictionaryCombined_noS45
    (rel : RelativeFactorTowerData (T := T))
    (lock : PaperS3137ObjectLock I place T) :
    (paperNormalizedThetaSum T ≤ paperNormalizedQPilotSum T) ∧
      RelativeFactorTowerData (T := T) ∧
      Nonempty (PaperS3137ReadingDictionary (I := I) (place := place) (T := T)
        (hM := hM) (hB := hB) (lock := lock)) := by
  refine ⟨?_, rel, ?_⟩
  · exact Mzk1P0QVFamNormBridgeDonorActual.finalPaperNormalizedComparison_noS45 (T := T)
  · exact ⟨paperS3137ReadingDictionary_of (I := I) (place := place) (T := T) hM hB lock⟩

def dictionaryRows : List (String × String × String) :=
  [ ("PaperS3137ObjectLock", "B_b, B_pos, d_b = B_b*[K_w:F_v], unitMass eq, theta sign", "EXPLICIT SUBSTANTIVE LOCK"),
    ("theta_product_eq", "green: thetaNormReadProduct = closedForm - 1", "CONSTRUCTED"),
    ("q_paper_eq", "definitional expansion of paperNormalizedQPilotSum", "CONSTRUCTED (rfl)"),
    ("coeff_eq_of_ratio", "S45 ratio=1 => c_norm = paperCoeff", "CONSTRUCTED (green chain)"),
    ("PaperS3137ReadingDictionary", "dictionary with substantive object lock", "CONSTRUCTED (given lock)"),
    ("finalDictionaryCombined", "S45 => comparison ∧ rel ∧ dictionary", "PROVED (conditional, kept)"),
    ("finalDictionaryCombined_ofNormBridge", "pointwise power bridge => drop-S combined", "PROVED (conditional on bridge)"),
    ("finalDictionaryCombined_noS45", "UNCONDITIONAL comparison (donor noS45) ∧ rel ∧ dictionary", "PROVED (unconditional, no S45)") ]

theorem dictionaryRows_length : dictionaryRows.length = 8 := rfl

end LeanFormal.IUT.XiFPaper.Mzk1P0FinalS3137DictionaryActual

end