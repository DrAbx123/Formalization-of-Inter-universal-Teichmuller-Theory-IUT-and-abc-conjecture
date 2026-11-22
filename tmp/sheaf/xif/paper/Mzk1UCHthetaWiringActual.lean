/-
# U-C: htheta wiring (sealed original form)

Lead 2026-11-16 task: prepare the wiring of the U-R C2 htheta (kurt) into the U-C
C4 slot, in the SEALED original form

  htheta : actualThetaHullLogRoot (l := l) T <= ucWeightedHpkt (nativeBadLocalWeight T) packetV

with the bad-place index and weights fixed (index = Bad places, gamma =
nativeBadLocalWeight, no sum-to-one requirement).

This file supplies:
* htheta_of_hperB: kurt's per-b form  (forall b, actualLocalHullLog T b <= packetV b)
  gives the sealed htheta through the actual weighted monotone sum
  (Mzk1P6P5ThetaHullControl2.thetaHullLog_le_ucHpkt);
* uc_c4_of_htheta: the sealed htheta + the hstepVIII retained shape give the U-C C4
  conclusion cL l * Q <= paperA d_mod l S_ar (paperEar eMod l eta_prm), through
  uc_c4_paperConstants_of_p6 (all other inputs actual: hprime via Section2, hconst
  via paper constants, and the accepted P5 lower bound -M <= theta);
* HthetaInput: a named Prop wrapper for the sealed htheta (PENDING REPLACEMENT by
  kurt's final theorem once its exact name lands; no sorry is used anywhere).

The two compatibility declarations are marked "PENDING" in their docstrings and
are hypotheses at the wiring sites, not axioms.
-/
import tmp.sheaf.xif.paper.Mzk1ULStepVIIIActual
import tmp.sheaf.xif.paper.Mzk1P6P5ThetaHullControl2
import tmp.sheaf.xif.paper.Mzk1URThetaHthetaActual
import tmp.sheaf.xif.paper.Mzk1URThetaHullNonzeroActual
import Mathlib.Tactic

noncomputable section
open scoped BigOperators
namespace LeanFormal.IUT.XiFPaper.Mzk1UCHthetaWiringActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.N8Closure.NativeInput
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.PaperLevelXiFTargetActual
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.VbadPlaceIndexingActual
open LeanFormal.IUT.XiFPaper.Mzk1ActualHullTargetMagnitudeActual

/-- Adapter: kurt's per-b form gives the sealed htheta (actual weighted monotone
sum; index = Bad places, weights nativeBadLocalWeight). -/
theorem htheta_of_hperB {l : PrimeGeFive} (T : SourceNativeInitialThetaData.{0} l)
    [Fintype (Bad (nativePlaceSelection T))]
    [∀ b : Bad (nativePlaceSelection T), MeasurableSpace (qVFamTensorBlock T b)]
    [∀ b : Bad (nativePlaceSelection T), BorelSpace (qVFamTensorBlock T b)]
    (packetV : Bad (nativePlaceSelection T) → ℝ)
    (hperB : ∀ b : Bad (nativePlaceSelection T),
      LeanFormal.IUT.XiFPaper.PaperLevelXiFTargetActual.actualLocalHullLog (l := l) T b ≤ packetV b) :
    LeanFormal.IUT.XiFPaper.PaperLevelXiFTargetActual.actualThetaHullLogRoot (l := l) T ≤
      LeanFormal.IUT.XiFPaper.Mzk1UCC3ProducerActual.ucWeightedHpkt
        (LeanFormal.IUT.XiFPaper.VbadPlaceIndexingActual.nativeBadLocalWeight T) packetV :=
  LeanFormal.IUT.XiFPaper.Mzk1P6P5ThetaHullControl2.thetaHullLog_le_ucHpkt
    (l := l) T packetV hperB

/-- The seamless wrapper of the sealed htheta (PENDING: to be replaced by kurt's
final theorem once its exact name lands; currently a named hypothesis). -/
structure HthetaInput {l : PrimeGeFive} (T : SourceNativeInitialThetaData.{0} l)
    [Fintype (Bad (nativePlaceSelection T))]
    [∀ b : Bad (nativePlaceSelection T), MeasurableSpace (qVFamTensorBlock T b)]
    [∀ b : Bad (nativePlaceSelection T), BorelSpace (qVFamTensorBlock T b)]
    (packetV : Bad (nativePlaceSelection T) → ℝ) :
    Prop where
  htheta : LeanFormal.IUT.XiFPaper.PaperLevelXiFTargetActual.actualThetaHullLogRoot (l := l) T ≤
    LeanFormal.IUT.XiFPaper.Mzk1UCC3ProducerActual.ucWeightedHpkt
      (LeanFormal.IUT.XiFPaper.VbadPlaceIndexingActual.nativeBadLocalWeight T) packetV

/-- U-C C4 from the sealed htheta + the retained hstepVIII shape (through
uc_c4_paperConstants_of_p6).  All non-retained inputs (hprime from Section2,
hconst from the paper constants, the accepted P5 lower bound) are handled inside. -/
theorem uc_c4_of_htheta {l : PrimeGeFive} (T : SourceNativeInitialThetaData.{0} l)
    [Fintype (Bad (nativePlaceSelection T))]
    [∀ b : Bad (nativePlaceSelection T), MeasurableSpace (qVFamTensorBlock T b)]
    [∀ b : Bad (nativePlaceSelection T), BorelSpace (qVFamTensorBlock T b)]
    (V B : Bad (nativePlaceSelection T) → ℝ)
    (hVB : ∀ b : Bad (nativePlaceSelection T), V b ≤ B b)
    {η0 : ℝ} (hη0 : 0 < η0)
    (hπ : ∀ η : ℝ, η0 ≤ η →
      (Nat.primeCounting ⌊η⌋₊ : ℝ) ≤ 4 * η / (3 * Real.log η))
    {eMod : Nat} (he : 1 ≤ eMod)
    (eta_prm S_ar Q d_mod : ℝ) (hl : 5 ≤ (l.value : ℝ)) (heta : η0 ≤ eta_prm)
    (htheta : LeanFormal.IUT.XiFPaper.PaperLevelXiFTargetActual.actualThetaHullLogRoot (l := l) T ≤
      LeanFormal.IUT.XiFPaper.Mzk1UCC3ProducerActual.ucWeightedHpkt
        (LeanFormal.IUT.XiFPaper.VbadPlaceIndexingActual.nativeBadLocalWeight T) V)
    (hstepVIII :
      (∑ i : Bad (nativePlaceSelection T),
          LeanFormal.IUT.XiFPaper.VbadPlaceIndexingActual.nativeBadLocalWeight T i * B i) ≤
        LeanFormal.IUT.XiFPaper.Mzk1UCC3Actual.kappa (l.value : ℝ) *
            ((1 + 12 * d_mod / (l.value : ℝ)) * S_ar
              + 2 * Real.log (l.value : ℝ) + 56
              - LeanFormal.IUT.XiFPaper.Mzk1UCC3Actual.cL (l.value : ℝ) * Q
              + (20 / 3) * LeanFormal.IUT.XiFPaper.Mzk1ULHpktActual.paperLstarLogs eMod (l.value : ℝ))
          - actualQPilotMagnitudeClassical
              (l := l) T) :
    LeanFormal.IUT.XiFPaper.Mzk1UCC3Actual.cL (l.value : ℝ) * Q ≤
      LeanFormal.IUT.XiFPaper.Mzk1ULHpktActual.paperA d_mod (l.value : ℝ) S_ar
        (LeanFormal.IUT.XiFPaper.Mzk1ULHpktActual.paperEar eMod (l.value : ℝ) eta_prm) :=
  LeanFormal.IUT.XiFPaper.Mzk1UCHpktActual.uc_c4_paperConstants_of_p6 (l := l) T
    (LeanFormal.IUT.XiFPaper.VbadPlaceIndexingActual.nativeBadLocalWeight T) V B
    (fun b => LeanFormal.IUT.XiFPaper.PaperLevelXiFTargetActual.actualTargetWeight_nonneg (l := l) T b)
    hVB hη0 hπ he eta_prm S_ar Q d_mod hl heta htheta hstepVIII

/-- Composite: kurt's per-b form + the retained hstepVIII give the U-C C4
conclusion (no sealed hypothesis needed beyond the per-b bounds). -/
theorem uc_c4_of_hperB {l : PrimeGeFive} (T : SourceNativeInitialThetaData.{0} l)
    [Fintype (Bad (nativePlaceSelection T))]
    [∀ b : Bad (nativePlaceSelection T), MeasurableSpace (qVFamTensorBlock T b)]
    [∀ b : Bad (nativePlaceSelection T), BorelSpace (qVFamTensorBlock T b)]
    (V B : Bad (nativePlaceSelection T) → ℝ)
    (hperB : ∀ b : Bad (nativePlaceSelection T),
      LeanFormal.IUT.XiFPaper.PaperLevelXiFTargetActual.actualLocalHullLog (l := l) T b ≤ V b)
    (hVB : ∀ b : Bad (nativePlaceSelection T), V b ≤ B b)
    {η0 : ℝ} (hη0 : 0 < η0)
    (hπ : ∀ η : ℝ, η0 ≤ η →
      (Nat.primeCounting ⌊η⌋₊ : ℝ) ≤ 4 * η / (3 * Real.log η))
    {eMod : Nat} (he : 1 ≤ eMod)
    (eta_prm S_ar Q d_mod : ℝ) (hl : 5 ≤ (l.value : ℝ)) (heta : η0 ≤ eta_prm)
    (hstepVIII :
      (∑ i : Bad (nativePlaceSelection T),
          LeanFormal.IUT.XiFPaper.VbadPlaceIndexingActual.nativeBadLocalWeight T i * B i) ≤
        LeanFormal.IUT.XiFPaper.Mzk1UCC3Actual.kappa (l.value : ℝ) *
            ((1 + 12 * d_mod / (l.value : ℝ)) * S_ar
              + 2 * Real.log (l.value : ℝ) + 56
              - LeanFormal.IUT.XiFPaper.Mzk1UCC3Actual.cL (l.value : ℝ) * Q
              + (20 / 3) * LeanFormal.IUT.XiFPaper.Mzk1ULHpktActual.paperLstarLogs eMod (l.value : ℝ))
          - actualQPilotMagnitudeClassical
              (l := l) T) :
    LeanFormal.IUT.XiFPaper.Mzk1UCC3Actual.cL (l.value : ℝ) * Q ≤
      LeanFormal.IUT.XiFPaper.Mzk1ULHpktActual.paperA d_mod (l.value : ℝ) S_ar
        (LeanFormal.IUT.XiFPaper.Mzk1ULHpktActual.paperEar eMod (l.value : ℝ) eta_prm) :=
  uc_c4_of_htheta (l := l) T V B hVB hη0 hπ he eta_prm S_ar Q d_mod hl heta
    (htheta_of_hperB (l := l) T V hperB) hstepVIII

#print axioms htheta_of_hperB
#print axioms uc_c4_of_htheta
#print axioms uc_c4_of_hperB


/-- C2 theta object switch (audit ruling (c)): the C4 evidence must use the
paper-faithful route object paperThetaHullLogRoot (:= kurt's nz object, e.g.
urNonzeroThetaHullLogRoot), NOT the zero-collapsed actualRootTheta observation.
Fields: theta (the real read-off), hThetaEq (theta = paperThetaHullLogRoot),
hThetaLower (the P5 lower bound -M <= theta transported to this object) and
hThetaUpper (nz htheta: paperThetaHullLogRoot <= ucWeightedHpkt gamma packetV).
The zero-collapse of actualThetaHullLogRoot stays an observation only. -/
structure C2ThetaInput {l : PrimeGeFive} (T : SourceNativeInitialThetaData.{0} l)
    [Fintype (Bad (nativePlaceSelection T))]
    (packetV : Bad (nativePlaceSelection T) → ℝ) where
  /-- the paper-faithful route theta object (kurt's nonzero-label object) -/
  paperThetaHullLogRoot : ℝ
  /-- the real read-off used in the sandwich -/
  theta : ℝ
  hThetaEq : theta = paperThetaHullLogRoot
  /-- P5 lower bound transported to the paper object (route C2: -M <= theta_P5) -/
  hThetaLower : -actualQPilotMagnitudeClassical (l := l) T ≤ theta
  /-- nz htheta in the original form for the paper object -/
  hThetaUpper : paperThetaHullLogRoot
    ≤ LeanFormal.IUT.XiFPaper.Mzk1UCC3ProducerActual.ucWeightedHpkt
        (LeanFormal.IUT.XiFPaper.VbadPlaceIndexingActual.nativeBadLocalWeight T) packetV

/-- U-C C4 with the audit-correct theta object: paperTheta (via C2ThetaInput)
instead of actualThetaHullLogRoot.  Same retained inputs as the old variant
(hstepVIII shape); the old `uc_c4_of_htheta` is kept unchanged. -/
theorem uc_c4_of_htheta_paper {l : PrimeGeFive} (T : SourceNativeInitialThetaData.{0} l)
    [Fintype (Bad (nativePlaceSelection T))]
    [∀ b : Bad (nativePlaceSelection T), MeasurableSpace (qVFamTensorBlock T b)]
    [∀ b : Bad (nativePlaceSelection T), BorelSpace (qVFamTensorBlock T b)]
    (V B : Bad (nativePlaceSelection T) → ℝ)
    (hC : C2ThetaInput (l := l) T V)
    (hVB : ∀ b : Bad (nativePlaceSelection T), V b ≤ B b)
    {η0 : ℝ} (hη0 : 0 < η0)
    (hπ : ∀ η : ℝ, η0 ≤ η →
      (Nat.primeCounting ⌊η⌋₊ : ℝ) ≤ 4 * η / (3 * Real.log η))
    {eMod : Nat} (he : 1 ≤ eMod)
    (eta_prm S_ar Q d_mod : ℝ) (hl : 5 ≤ (l.value : ℝ)) (heta : η0 ≤ eta_prm)
    (hstepVIII :
      (∑ i : Bad (nativePlaceSelection T),
          LeanFormal.IUT.XiFPaper.VbadPlaceIndexingActual.nativeBadLocalWeight T i * B i) ≤
        LeanFormal.IUT.XiFPaper.Mzk1UCC3Actual.kappa (l.value : ℝ) *
            ((1 + 12 * d_mod / (l.value : ℝ)) * S_ar
              + 2 * Real.log (l.value : ℝ) + 56
              - LeanFormal.IUT.XiFPaper.Mzk1UCC3Actual.cL (l.value : ℝ) * Q
              + (20 / 3) * LeanFormal.IUT.XiFPaper.Mzk1ULHpktActual.paperLstarLogs eMod (l.value : ℝ))
          - actualQPilotMagnitudeClassical (l := l) T) :
    LeanFormal.IUT.XiFPaper.Mzk1UCC3Actual.cL (l.value : ℝ) * Q ≤
      LeanFormal.IUT.XiFPaper.Mzk1ULHpktActual.paperA d_mod (l.value : ℝ) S_ar
        (LeanFormal.IUT.XiFPaper.Mzk1ULHpktActual.paperEar eMod (l.value : ℝ) eta_prm) := by
  have hk : 0 < LeanFormal.IUT.XiFPaper.Mzk1UCC3Actual.kappa (l.value : ℝ) := by
    unfold LeanFormal.IUT.XiFPaper.Mzk1UCC3Actual.kappa
    have : (5 : ℝ) ≤ (l.value : ℝ) := hl
    linarith
  have hup : hC.theta ≤ LeanFormal.IUT.XiFPaper.Mzk1UCC3ProducerActual.ucWeightedHpkt
      (LeanFormal.IUT.XiFPaper.VbadPlaceIndexingActual.nativeBadLocalWeight T) V := by
    rw [hC.hThetaEq]
    exact hC.hThetaUpper
  have hC3 := LeanFormal.IUT.XiFPaper.Mzk1UCHpktActual.uc_c3_paperConstants
    (ι := Bad (nativePlaceSelection T))
    (LeanFormal.IUT.XiFPaper.VbadPlaceIndexingActual.nativeBadLocalWeight T) V B
    (fun b => LeanFormal.IUT.XiFPaper.PaperLevelXiFTargetActual.actualTargetWeight_nonneg (l := l) T b)
    hVB hη0 hπ he (l.value : ℝ) eta_prm S_ar Q
    (actualQPilotMagnitudeClassical (l := l) T) d_mod hl heta hstepVIII
  exact LeanFormal.IUT.XiFPaper.Mzk1UCHpktActual.uc_sandwich hk hC.hThetaLower hup hC3


/-- Construct the audit-c theta input from kurt's nonzero-label object (DONE 18:17:24):
(1) paper object `paperThetaHullLogRoot`; (2) nz htheta
`paperThetaHullLogRoot_le_ucWeightedHpkt` from per-b bounds; (3) the P5 lower
bound on the nz object is RETAINED here (kurt's next-batch exact computation). -/
noncomputable def c2ThetaInput_of_hperB {l : PrimeGeFive} (T : SourceNativeInitialThetaData.{0} l)
    [Fintype (Bad (nativePlaceSelection T))]
    [∀ b : Bad (nativePlaceSelection T), MeasurableSpace (qVFamTensorBlock T b)]
    [∀ b : Bad (nativePlaceSelection T), BorelSpace (qVFamTensorBlock T b)]
    (packetV : Bad (nativePlaceSelection T) → ℝ)
    (hperB : ∀ b : Bad (nativePlaceSelection T),
      LeanFormal.IUT.XiFPaper.Mzk1URThetaHullNonzeroActual.urNonzeroLabelHullLog T b ≤ packetV b)
    (hLower : -actualQPilotMagnitudeClassical (l := l) T ≤ LeanFormal.IUT.XiFPaper.Mzk1URThetaHullNonzeroActual.paperThetaHullLogRoot T) :
    C2ThetaInput (l := l) T packetV where
  paperThetaHullLogRoot := LeanFormal.IUT.XiFPaper.Mzk1URThetaHullNonzeroActual.paperThetaHullLogRoot T
  theta := LeanFormal.IUT.XiFPaper.Mzk1URThetaHullNonzeroActual.paperThetaHullLogRoot T
  hThetaEq := rfl
  hThetaLower := hLower
  hThetaUpper := LeanFormal.IUT.XiFPaper.Mzk1URThetaHullNonzeroActual.paperThetaHullLogRoot_le_ucWeightedHpkt T packetV hperB

/-- C4 from kurt's nz theta object: per-b bounds + retained nz P5 lower bound +
the hstepVIII shape.  All other inputs are the actual ones. -/
theorem uc_c4_of_paperTheta {l : PrimeGeFive} (T : SourceNativeInitialThetaData.{0} l)
    [Fintype (Bad (nativePlaceSelection T))]
    [∀ b : Bad (nativePlaceSelection T), MeasurableSpace (qVFamTensorBlock T b)]
    [∀ b : Bad (nativePlaceSelection T), BorelSpace (qVFamTensorBlock T b)]
    (V B : Bad (nativePlaceSelection T) → ℝ)
    (hperB : ∀ b : Bad (nativePlaceSelection T),
      LeanFormal.IUT.XiFPaper.Mzk1URThetaHullNonzeroActual.urNonzeroLabelHullLog T b ≤ V b)
    (hLower : -actualQPilotMagnitudeClassical (l := l) T ≤ LeanFormal.IUT.XiFPaper.Mzk1URThetaHullNonzeroActual.paperThetaHullLogRoot T)
    (hVB : ∀ b : Bad (nativePlaceSelection T), V b ≤ B b)
    {η0 : ℝ} (hη0 : 0 < η0)
    (hπ : ∀ η : ℝ, η0 ≤ η →
      (Nat.primeCounting ⌊η⌋₊ : ℝ) ≤ 4 * η / (3 * Real.log η))
    {eMod : Nat} (he : 1 ≤ eMod)
    (eta_prm S_ar Q d_mod : ℝ) (hl : 5 ≤ (l.value : ℝ)) (heta : η0 ≤ eta_prm)
    (hstepVIII :
      (∑ i : Bad (nativePlaceSelection T),
          LeanFormal.IUT.XiFPaper.VbadPlaceIndexingActual.nativeBadLocalWeight T i * B i) ≤
        LeanFormal.IUT.XiFPaper.Mzk1UCC3Actual.kappa (l.value : ℝ) *
            ((1 + 12 * d_mod / (l.value : ℝ)) * S_ar
              + 2 * Real.log (l.value : ℝ) + 56
              - LeanFormal.IUT.XiFPaper.Mzk1UCC3Actual.cL (l.value : ℝ) * Q
              + (20 / 3) * LeanFormal.IUT.XiFPaper.Mzk1ULHpktActual.paperLstarLogs eMod (l.value : ℝ))
          - actualQPilotMagnitudeClassical (l := l) T) :
    LeanFormal.IUT.XiFPaper.Mzk1UCC3Actual.cL (l.value : ℝ) * Q ≤
      LeanFormal.IUT.XiFPaper.Mzk1ULHpktActual.paperA d_mod (l.value : ℝ) S_ar
        (LeanFormal.IUT.XiFPaper.Mzk1ULHpktActual.paperEar eMod (l.value : ℝ) eta_prm) :=
  uc_c4_of_htheta_paper (l := l) T V B
    (c2ThetaInput_of_hperB (l := l) T V hperB hLower) hVB hη0 hπ he eta_prm S_ar Q d_mod
    hl heta hstepVIII

end LeanFormal.IUT.XiFPaper.Mzk1UCHthetaWiringActual
end