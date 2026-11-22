/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.Mzk1RamifiedPlaceDataActual
import tmp.sheaf.xif.paper.Mzk1FinalIndexDecompActual
import tmp.sheaf.xif.paper.Mzk1IndexQFEConnectionActual
import tmp.sheaf.xif.paper.Mzk1Paper312AssemblyActual
import LeanFormal.IUT.ABCBridge.Geometry.FinitePlaceFullPrimePacket
import LeanFormal.IUT.ABCBridge.Geometry.FinitePlaceCommonPrimeCompletion
import LeanFormal.IUT.Foundations.LocalFields.IntegralLogShellSharpBounds
import LeanFormal.IUT.Foundations.LocalFields.IntegralTraceDualTensorInclusion
import tmp.sheaf.xif.paper.Mzk1PerPlaceInequalityActual
import Mathlib.Tactic
/-! # Actual ramified place data from a finite-place fiber -/
noncomputable section
namespace LeanFormal.IUT.XiFPaper.Mzk1ActualRamifiedDataActual
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.Mzk1RamifiedPlaceActual
open LeanFormal.IUT.XiFPaper.Mzk1RamifiedPlaceDataActual
open LeanFormal.IUT.LocalFieldLogarithm
open LeanFormal.IUT.XiFPaper.Mzk1PerPlaceInequalityActual
open LeanFormal.IUT.XiFPaper.Mzk1FinalIndexDecompActual
open LeanFormal.IUT.XiFPaper.Mzk1IndexQFEConnectionActual
open LeanFormal.IUT.LocalFieldIntegralUnits
open LeanFormal.IUT.IntegralTraceDualTensorInclusion
open scoped NNReal NormedField
variable {F : Type*} [Field F] [NumberField F] {p : Nat} [Fact p.Prime]
/-- Actual completion bundle, keeping the place prime definitional. -/
def ofAtPrime (place : FinitePlaceAtPrime F p) : RamifiedPlace where
  p := (completionRationalPrime place.val).val
  factPrime := inferInstance
  K := NormalizedCompletion place.val
  normed := inferInstance
  charZero := inferInstance
  complete := inferInstance
  ultrametric := inferInstance
  proper := inferInstance
  alg := inferInstance
  finDim := inferInstance
/-- Residue degree of an actual place, chosen from the residue-card theorem. -/
def actualFn (place : FinitePlaceAtPrime F p) : Nat := by
  letI : NormedField (NormalizedCompletion place.val) := inferInstance
  letI : CharZero (NormalizedCompletion place.val) := inferInstance
  letI : CompleteSpace (NormalizedCompletion place.val) := inferInstance
  letI : IsUltrametricDist (NormalizedCompletion place.val) := inferInstance
  letI : ProperSpace (NormalizedCompletion place.val) := inferInstance
  letI : Fact (Nat.Prime (completionRationalPrime place.val).val) := inferInstance
  letI : NormedAlgebra (Padic (completionRationalPrime place.val).val)
    (NormalizedCompletion place.val) := inferInstance
  letI : FiniteDimensional (Padic (completionRationalPrime place.val).val)
    (NormalizedCompletion place.val) := inferInstance
  exact Classical.choose (logShellResidueCard_eq_prime_pow
    (K := NormalizedCompletion place.val)
    (p := (completionRationalPrime place.val).val))
/-- Spec of the chosen residue degree. -/
theorem actualFn_spec (place : FinitePlaceAtPrime F p) :
    1 ≤ actualFn place ∧
      logShellResidueCard (K := NormalizedCompletion place.val) =
        (completionRationalPrime place.val).val ^ actualFn place := by
  unfold actualFn
  letI : NormedField (NormalizedCompletion place.val) := inferInstance
  letI : CharZero (NormalizedCompletion place.val) := inferInstance
  letI : CompleteSpace (NormalizedCompletion place.val) := inferInstance
  letI : IsUltrametricDist (NormalizedCompletion place.val) := inferInstance
  letI : ProperSpace (NormalizedCompletion place.val) := inferInstance
  letI : Fact (Nat.Prime (completionRationalPrime place.val).val) := inferInstance
  letI : NormedAlgebra (Padic (completionRationalPrime place.val).val)
    (NormalizedCompletion place.val) := inferInstance
  letI : FiniteDimensional (Padic (completionRationalPrime place.val).val)
    (NormalizedCompletion place.val) := inferInstance
  exact Classical.choose_spec (logShellResidueCard_eq_prime_pow
    (K := NormalizedCompletion place.val)
    (p := (completionRationalPrime place.val).val))
/-- Per-place `T*index = q^A*(q-1)`. -/
def hdecompOf (place : FinitePlaceAtPrime F p) :
    Nat.card (CommGroup.torsion (Integers (NormalizedCompletion place.val))ˣ) *
        logShellIntegerIndex (K := NormalizedCompletion place.val)
          (p := (completionRationalPrime place.val).val) =
      logShellResidueCard (K := NormalizedCompletion place.val) ^
          (logShellRamificationExponent (K := NormalizedCompletion place.val)
            (p := (completionRationalPrime place.val).val) *
            logShellScaleExponentFactor
              (p := (completionRationalPrime place.val).val) - 1) *
        (logShellResidueCard (K := NormalizedCompletion place.val) - 1) := by
  letI : NormedField (NormalizedCompletion place.val) := inferInstance
  letI : CharZero (NormalizedCompletion place.val) := inferInstance
  letI : CompleteSpace (NormalizedCompletion place.val) := inferInstance
  letI : IsUltrametricDist (NormalizedCompletion place.val) := inferInstance
  letI : ProperSpace (NormalizedCompletion place.val) := inferInstance
  letI : Fact (Nat.Prime (completionRationalPrime place.val).val) := inferInstance
  letI : NormedAlgebra (Padic (completionRationalPrime place.val).val)
    (NormalizedCompletion place.val) := inferInstance
  letI : FiniteDimensional (Padic (completionRationalPrime place.val).val)
    (NormalizedCompletion place.val) := inferInstance
  have hdec : Nat.card ((Integers (NormalizedCompletion place.val))ˣ ⧸
      logShellCongruenceUnits (K := NormalizedCompletion place.val)
        (p := (completionRationalPrime place.val).val)) =
      Nat.card (CommGroup.torsion (Integers (NormalizedCompletion place.val))ˣ) *
        logShellIntegerIndex (K := NormalizedCompletion place.val)
          (p := (completionRationalPrime place.val).val) :=
    logShellCongruenceQuotient_card_eq_torsion_mul_logShellIntegerIndex
      (K := NormalizedCompletion place.val)
      (p := (completionRationalPrime place.val).val)
  have hquot := qfe_quotient_card_actual (K := NormalizedCompletion place.val)
    (p := (completionRationalPrime place.val).val)
  exact hdec.symm.trans hquot
/-- Chosen correction exponent. -/
def chosenA (place : FinitePlaceAtPrime F p) : Nat :=
  Classical.choose (index_decomp_with_correction
    (K := NormalizedCompletion place.val)
    (p := (completionRationalPrime place.val).val)
    (f := actualFn place) (actualFn_spec place).1 (actualFn_spec place).2
    (hdecompOf place))
/-- Chosen correction factor. -/
def chosenC (place : FinitePlaceAtPrime F p) : Nat :=
  Classical.choose (Classical.choose_spec (index_decomp_with_correction
    (K := NormalizedCompletion place.val)
    (p := (completionRationalPrime place.val).val)
    (f := actualFn place) (actualFn_spec place).1 (actualFn_spec place).2
    (hdecompOf place)))

/-- Spec of the chosen correction pair. -/
theorem chosenSpec (place : FinitePlaceAtPrime F p) :
    logShellIntegerIndex (K := NormalizedCompletion place.val)
        (p := (completionRationalPrime place.val).val) =
      logShellResidueCard (K := NormalizedCompletion place.val) ^ chosenA place *
        chosenC place ∧
      LogShellResiduePowerCardCorrectionHypothesis (K := NormalizedCompletion place.val)
        (p := (completionRationalPrime place.val).val) (chosenA place) (chosenC place) := by
  exact Classical.choose_spec (Classical.choose_spec (index_decomp_with_correction
    (K := NormalizedCompletion place.val)
    (p := (completionRationalPrime place.val).val)
    (f := actualFn place) (actualFn_spec place).1 (actualFn_spec place).2
    (hdecompOf place)))
/-- Actual data with hcoef supplied explicitly. -/
def actualData
    (Fdeg l : ℝ) (logp logMu logIdx diff : FinitePlaceAtPrime F p → ℝ)
    (mult : FinitePlaceAtPrime F p → ℝ)
    (hcoef : ∀ i : FinitePlaceAtPrime F p, CoeffComparison ((actualFn i : ℝ)) Fdeg l ((chosenA i : ℝ))) :
    RamifiedPlaceData (FinitePlaceAtPrime F p) where
  places := ofAtPrime
  fn := actualFn
  mult := mult
  Fdeg := fun _ => Fdeg
  l := l
  logp := logp
  logMu := logMu
  logIdx := logIdx
  diff := diff
  aExp := chosenA
  cCorr := chosenC


/-- Log index of an actual place. -/
def actualLogIdx (place : FinitePlaceAtPrime F p) : ℝ := by
  letI : NormedField (NormalizedCompletion place.val) := inferInstance
  letI : CharZero (NormalizedCompletion place.val) := inferInstance
  letI : CompleteSpace (NormalizedCompletion place.val) := inferInstance
  letI : IsUltrametricDist (NormalizedCompletion place.val) := inferInstance
  letI : ProperSpace (NormalizedCompletion place.val) := inferInstance
  letI : Fact (Nat.Prime (completionRationalPrime place.val).val) := inferInstance
  letI : NormedAlgebra (Padic (completionRationalPrime place.val).val)
    (NormalizedCompletion place.val) := inferInstance
  letI : FiniteDimensional (Padic (completionRationalPrime place.val).val)
    (NormalizedCompletion place.val) := inferInstance
  exact Real.log (logShellIntegerIndex (K := NormalizedCompletion place.val)
    (p := (completionRationalPrime place.val).val) : ℝ)
/-- Actual data with log-index and diff definitional. -/
def actualDataCore (Fdeg l : ℝ)
    (logMu : FinitePlaceAtPrime F p → ℝ)
    (mult : FinitePlaceAtPrime F p → ℝ)
    (hcoef : ∀ i : FinitePlaceAtPrime F p,
      CoeffComparison ((actualFn i : ℝ)) Fdeg l ((chosenA i : ℝ))) :
    RamifiedPlaceData (FinitePlaceAtPrime F p) where
  places := ofAtPrime
  fn := actualFn
  mult := mult
  Fdeg := fun _ => Fdeg
  l := l
  logp := fun i => Real.log (((completionRationalPrime (i.val)).val : ℕ) : ℝ)
  logMu := logMu
  logIdx := actualLogIdx
  diff := fun i => logMu i - (1 / (2 * l)) * actualLogIdx i
  aExp := chosenA
  cCorr := chosenC

theorem actualDataCore_hasCorrection (Fdeg l : ℝ)
    (logMu : FinitePlaceAtPrime F p → ℝ)
    (mult : FinitePlaceAtPrime F p → ℝ)
    (hcoef : ∀ i : FinitePlaceAtPrime F p,
      CoeffComparison ((actualFn i : ℝ)) Fdeg l ((chosenA i : ℝ))) :
    HasCorrection (actualDataCore (F := F) (p := p) Fdeg l logMu mult hcoef) := by
  intro i
  dsimp [HasCorrection, actualDataCore]
  exact (chosenSpec i).2

theorem actualDataCore_hasRes (Fdeg l : ℝ)
    (logMu : FinitePlaceAtPrime F p → ℝ)
    (mult : FinitePlaceAtPrime F p → ℝ)
    (hcoef : ∀ i : FinitePlaceAtPrime F p,
      CoeffComparison ((actualFn i : ℝ)) Fdeg l ((chosenA i : ℝ))) :
    HasRes (actualDataCore (F := F) (p := p) Fdeg l logMu mult hcoef) := by
  intro i
  dsimp [HasRes, actualDataCore]
  exact (actualFn_spec i).2

theorem actualDataCore_hasLogIdx (Fdeg l : ℝ)
    (logMu : FinitePlaceAtPrime F p → ℝ)
    (mult : FinitePlaceAtPrime F p → ℝ)
    (hcoef : ∀ i : FinitePlaceAtPrime F p,
      CoeffComparison ((actualFn i : ℝ)) Fdeg l ((chosenA i : ℝ))) :
    HasLogIdx (actualDataCore (F := F) (p := p) Fdeg l logMu mult hcoef) := by
  intro i
  dsimp [HasLogIdx, actualDataCore, actualLogIdx]
  rfl

theorem actualDataCore_hasCoeff (Fdeg l : ℝ)
    (logMu : FinitePlaceAtPrime F p → ℝ)
    (mult : FinitePlaceAtPrime F p → ℝ)
    (hcoef : ∀ i : FinitePlaceAtPrime F p,
      CoeffComparison ((actualFn i : ℝ)) Fdeg l ((chosenA i : ℝ))) :
    HasCoeff (actualDataCore (F := F) (p := p) Fdeg l logMu mult hcoef) := by
  intro i
  exact hcoef i
theorem actualDataCore_perPlace_bounds (Fdeg l : ℝ)
    (logMu : FinitePlaceAtPrime F p → ℝ)
    (mult : FinitePlaceAtPrime F p → ℝ)
    (hcoef : ∀ i : FinitePlaceAtPrime F p,
      CoeffComparison ((actualFn i : ℝ)) Fdeg l ((chosenA i : ℝ)))
    (hmu0 : ∀ i : FinitePlaceAtPrime F p, 0 ≤ logMu i) (hl : 1 ≤ 2 * l)
    (hc : ∀ i : FinitePlaceAtPrime F p, 1 ≤ chosenC i) :
    ∀ i, (actualFn i : ℝ) / (Fdeg * (2 * l)) *
        Real.log (((completionRationalPrime (i.val)).val : ℕ) : ℝ) ≤
      actualLogIdx i + (logMu i - (1 / (2 * l)) * actualLogIdx i) := by
  let d := actualDataCore (F := F) (p := p) Fdeg l logMu mult hcoef
  have hcard : HasCorrection d := actualDataCore_hasCorrection Fdeg l logMu mult hcoef
  have hlogIdx : HasLogIdx d := actualDataCore_hasLogIdx Fdeg l logMu mult hcoef
  have hcoef : HasCoeff d := actualDataCore_hasCoeff Fdeg l logMu mult hcoef
  have hres : HasRes d := actualDataCore_hasRes Fdeg l logMu mult hcoef
  have hdiff : ∀ i, d.diff i = d.logMu i - (1 / (2 * d.l)) * d.logIdx i := by
    intro i; rfl
  have hlogp_eq : ∀ i, d.logp i = Real.log ((d.places i).p : ℝ) := by
    intro i; rfl
  simpa [d, actualDataCore] using
    perPlace_bounds_of_data d hcard hlogIdx hcoef hres hlogp_eq hmu0 hl hc hdiff



open LeanFormal.IUT.XiFPaper.Mzk1Paper312AssemblyActual

theorem actual_A_le_Lbar_add_Dbar (Fdeg l : ℝ)
    (logMu : FinitePlaceAtPrime F p → ℝ)
    (mult : FinitePlaceAtPrime F p → ℝ)
    (hcoef : ∀ i : FinitePlaceAtPrime F p,
      CoeffComparison ((actualFn i : ℝ)) Fdeg l ((chosenA i : ℝ)))
    (hmu0 : ∀ i : FinitePlaceAtPrime F p, 0 ≤ logMu i) (hl : 1 ≤ 2 * l)
    (hc : ∀ i : FinitePlaceAtPrime F p, 1 ≤ chosenC i) :
    (1 / (2 * l)) * (∑ i : FinitePlaceAtPrime F p,
        (actualFn i : ℝ) / Fdeg * Real.log (((completionRationalPrime (i.val)).val : ℕ) : ℝ)) ≤
      ∑ i : FinitePlaceAtPrime F p,
        (actualLogIdx i + (logMu i - (1 / (2 * l)) * actualLogIdx i)) := by
  apply A_le_Lbar_add_Dbar_of_correction
    (fn := fun i : FinitePlaceAtPrime F p => (actualFn i : ℝ)) (Fdeg := fun _ => Fdeg)
    (logp := fun i => Real.log (((completionRationalPrime (i.val)).val : ℕ) : ℝ))
    (logIdx := actualLogIdx)
    (diff := fun i => logMu i - (1 / (2 * l)) * actualLogIdx i)
  intro i
  exact actualDataCore_perPlace_bounds Fdeg l logMu mult hcoef hmu0 hl hc i

/-- R1 with the actual q-vanishing multiplicity `mult` in the A-term
(replacing the residue degree `actualFn`).  The per-place multiplicity bound is the
explicit arithmetic input; it is not derived from the residue-degree bound. -/
theorem actual_A_le_Lbar_add_Dbar_mult (Fdeg l : ℝ)
    (mult : FinitePlaceAtPrime F p → ℝ)
    (logMu : FinitePlaceAtPrime F p → ℝ)
    (hperPlace : ∀ i : FinitePlaceAtPrime F p,
      mult i / (Fdeg * (2 * l)) *
          Real.log (((completionRationalPrime (i.val)).val : ℕ) : ℝ) ≤
        actualLogIdx i + (logMu i - (1 / (2 * l)) * actualLogIdx i)) :
    (1 / (2 * l)) * (∑ i : FinitePlaceAtPrime F p,
        mult i / Fdeg * Real.log (((completionRationalPrime (i.val)).val : ℕ) : ℝ)) ≤
      ∑ i : FinitePlaceAtPrime F p,
        (actualLogIdx i + (logMu i - (1 / (2 * l)) * actualLogIdx i)) := by
  exact A_le_Lbar_add_Dbar_of_correction
    (fn := mult) (Fdeg := fun _ => Fdeg)
    (logp := fun i => Real.log (((completionRationalPrime (i.val)).val : ℕ) : ℝ))
    (logIdx := actualLogIdx)
    (diff := fun i => logMu i - (1 / (2 * l)) * actualLogIdx i)
    hperPlace

theorem actual_paper312 (Fdeg l : ℝ)
    (logMu : FinitePlaceAtPrime F p → ℝ)
    (mult : FinitePlaceAtPrime F p → ℝ)
    (hcoef : ∀ i : FinitePlaceAtPrime F p,
      CoeffComparison ((actualFn i : ℝ)) Fdeg l ((chosenA i : ℝ)))
    (hmu0 : ∀ i : FinitePlaceAtPrime F p, 0 ≤ logMu i) (hl : 1 ≤ 2 * l)
    (hc : ∀ i : FinitePlaceAtPrime F p, 1 ≤ chosenC i)
    (sFactor : ℝ) (hs0 : 0 ≤ sFactor - 1) (hs1 : sFactor - 1 ≤ 1)
    (hA0 : 0 ≤ (1 / (2 * l)) *
      (∑ i : FinitePlaceAtPrime F p,
        (actualFn i : ℝ) / Fdeg * Real.log (((completionRationalPrime (i.val)).val : ℕ) : ℝ))) :
    LeanFormal.IUT.XiFPaper.Mzk1Paper312ExplicitActual.ExplicitPaper312Inequality
      sFactor
      ((1 / (2 * l)) *
        (∑ i : FinitePlaceAtPrime F p,
          (actualFn i : ℝ) / Fdeg * Real.log (((completionRationalPrime (i.val)).val : ℕ) : ℝ)))
      (∑ i : FinitePlaceAtPrime F p, actualLogIdx i)
      (∑ i : FinitePlaceAtPrime F p,
        (logMu i - (1 / (2 * l)) * actualLogIdx i)) := by
  exact paper312_of_correction_bounds (l := l) hs0 hs1 hA0
    (fun i => actualDataCore_perPlace_bounds Fdeg l logMu mult hcoef hmu0 hl hc i)
end LeanFormal.IUT.XiFPaper.Mzk1ActualRamifiedDataActual
end