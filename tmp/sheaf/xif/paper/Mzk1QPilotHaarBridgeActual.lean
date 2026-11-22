/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.S2807ThetaHullVolumeIdentityActual
import LeanFormal.IUT.ABCBridge.Geometry.FinitePlaceIQHullInterface
import Mathlib.Tactic

/-! # A1059: QPilotHaarRegionData + real bridge (Option B of QPILOT-HAAR-REGION) -/

/-
| field | value |
|---|---|
| Status | PARTIAL (explicit target data; no fake inhabitant; bridge PROVED conditionally) |
| 目标 | `qPilotLogVolume_le_thetaHullLogVolume_of_bridge`: `S2717QPilotLogVolume <= S2717ThetaHullLogVolume` |
| 数据 | `QPilotHaarRegionData C3`: region/measurable/finite/qLog=-(haarLog region)/thetaRegion ⊆ region |
| GAP | GAP-HAAR-Q: no inhabitant of `QPilotHaarRegionData` (the q-side C3-block region is not constructed) |
| GAP | GAP-THETA-Q: direction thetaRegion ⊆ region (negHaarLog: bigger region ⇒ smaller negLog ⇒ qLog ≤ thetaLog) |
| A1071 | dependency rewrite: imports only green `S2807ThetaHullVolumeIdentityActual` + `FinitePlaceIQHullInterface` (generic `haarLogVolume`/`haarLogVolume_mono`); `Mzk1XiEContainmentMonotoneActual`/`FaithfulXiEContainment` are DEFERRED (historical A520 file is FAIL, not touched). |
| 循环性 | the bridge theorem assumes only explicit data; it does not assume Cor 3.12/SSIneq/variant |

This file contains no sorry and no axiom.  The `QPilotHaarRegionData` record is EXPLICIT
TARGET DATA (no inhabitant is fabricated); the bridge theorem below is a real (measure-
theoretic) proof from the record fields + `S2807_thetaHullVolume_eq_haarRegion`. -/

noncomputable section
open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.XiFPaper
open LeanFormal.IUT.XiFPaper.S2717Cor312FullTargetActual
open LeanFormal.IUT.XiFPaper.S2725GlobalThetaHullActual
open LeanFormal.IUT.XiFPaper.C3LogShellTensorPacketActual
open LeanFormal.IUT.XiFPaper.S1280SourceDefinition31Actual
open LeanFormal.IUT.NumberFieldFinitePlace
open MeasureTheory
open LeanFormal.IUT.N8Closure.C3Actual
open LeanFormal.IUT.XiFPaper.S2711PaperMultiUnconditionalActual
open LeanFormal.IUT.XiFPaper.S2678PaperUnconditionalHcompActual
open LeanFormal.IUT.XiFPaper.S2807ThetaHullVolumeIdentityActual

namespace LeanFormal.IUT.XiFPaper.Mzk1QPilotHaarBridgeActual

variable (R : S1280RemainingClauses fiveLabel)
variable (redCompat : Prop) (hredCompat : redCompat)
variable (torCompat : Prop) (htorCompat : torCompat)
variable (orbCompat : Prop) (horbCompat : orbCompat)
variable (secCompat : Prop) (hsecCompat : secCompat)
variable (cusCompat : Prop) (hcusCompat : cusCompat)
variable {K : Type} [Field K] [NumberField K] {p : Nat} [Fact p.Prime]
variable {iota : Type} [Fintype iota] {W : iota -> Type}
variable (places : (i : iota) -> W i -> LeanFormal.IUT.NumberFieldFinitePlace.FinitePlaceAtPrime K p)
variable (tuple : (i : iota) -> W i)
variable [MeasurableSpace (ArithmeticTensorTupleBlock places tuple)]
variable [BorelSpace (ArithmeticTensorTupleBlock places tuple)]
variable (nu : Measure (ArithmeticTensorTupleBlock places tuple))
variable [Measure.IsAddHaarMeasure nu]
variable (D : SourcePilotRegionDonors (S2711I R redCompat hredCompat torCompat htorCompat orbCompat horbCompat secCompat hsecCompat cusCompat hcusCompat))

local instance qphbMeasurable : MeasurableSpace (C3LogShellTensorBlock (S2717C3 R redCompat hredCompat torCompat htorCompat orbCompat horbCompat secCompat hsecCompat cusCompat hcusCompat D)) := borel _
local instance qphbBorel : BorelSpace (C3LogShellTensorBlock (S2717C3 R redCompat hredCompat torCompat htorCompat orbCompat horbCompat secCompat hsecCompat cusCompat hcusCompat D)) := ⟨rfl⟩

/-- Option B data: an explicit C3-block q-pilot region with its Haar log-volume
identification and the theta-region containment.  This is TARGET DATA, not an axiom;
no inhabitant is provided. -/
structure QPilotHaarRegionData where
  region : Set (C3LogShellTensorBlock (S2717C3 R redCompat hredCompat torCompat htorCompat orbCompat horbCompat secCompat hsecCompat cusCompat hcusCompat D))
  region_measurable : MeasurableSet region
  region_lt_top :
    (actualC3LogShellTensorHaar (S2717C3 R redCompat hredCompat torCompat htorCompat orbCompat horbCompat secCompat hsecCompat cusCompat hcusCompat D)) region < ⊤
  volume_eq :
    S2717QPilotLogVolume R redCompat hredCompat torCompat htorCompat orbCompat horbCompat secCompat hsecCompat cusCompat hcusCompat =
      - (haarLogVolume (actualC3LogShellTensorHaar (S2717C3 R redCompat hredCompat torCompat htorCompat orbCompat horbCompat secCompat hsecCompat cusCompat hcusCompat D)) region).toReal
  theta_subset_region :
    actualC3LogShellTensorRegion (S2717C3 R redCompat hredCompat torCompat htorCompat orbCompat horbCompat secCompat hsecCompat cusCompat hcusCompat D) ⊆ region

/-- **Real bridge (proved)**: the theta-hull log-volume is at least the q-pilot
log-volume, from (i) the S2807 theta Haar identification, (ii) the q-side Haar
identification, (iii) the containment and Haar-log-volume monotonicity. -/
theorem qPilotLogVolume_le_thetaHullLogVolume_of_bridge
    (B : QPilotHaarRegionData R redCompat hredCompat torCompat htorCompat orbCompat horbCompat secCompat hsecCompat cusCompat hcusCompat D) :
    S2717QPilotLogVolume R redCompat hredCompat torCompat htorCompat orbCompat horbCompat secCompat hsecCompat cusCompat hcusCompat ≤
      S2717ThetaHullLogVolume R redCompat hredCompat torCompat htorCompat orbCompat horbCompat secCompat hsecCompat cusCompat hcusCompat places tuple nu D := by
  have htheta :
      S2717ThetaHullLogVolume R redCompat hredCompat torCompat htorCompat orbCompat horbCompat secCompat hsecCompat cusCompat hcusCompat places tuple nu D =
        - (haarLogVolume (actualC3LogShellTensorHaar (S2717C3 R redCompat hredCompat torCompat htorCompat orbCompat horbCompat secCompat hsecCompat cusCompat hcusCompat D))
            (actualC3LogShellTensorRegion (S2717C3 R redCompat hredCompat torCompat htorCompat orbCompat horbCompat secCompat hsecCompat cusCompat hcusCompat D))).toReal :=
    S2807_thetaHullVolume_eq_haarRegion R redCompat hredCompat torCompat htorCompat orbCompat horbCompat secCompat hsecCompat cusCompat hcusCompat places tuple nu D
  rw [B.volume_eq, htheta]
  have hmono :
      haarLogVolume (actualC3LogShellTensorHaar (S2717C3 R redCompat hredCompat torCompat htorCompat orbCompat horbCompat secCompat hsecCompat cusCompat hcusCompat D))
          (actualC3LogShellTensorRegion (S2717C3 R redCompat hredCompat torCompat htorCompat orbCompat horbCompat secCompat hsecCompat cusCompat hcusCompat D))
        ≤ haarLogVolume (actualC3LogShellTensorHaar (S2717C3 R redCompat hredCompat torCompat htorCompat orbCompat horbCompat secCompat hsecCompat cusCompat hcusCompat D)) B.region := by
    exact haarLogVolume_mono B.theta_subset_region
  have hne :
      haarLogVolume (actualC3LogShellTensorHaar (S2717C3 R redCompat hredCompat torCompat htorCompat orbCompat horbCompat secCompat hsecCompat cusCompat hcusCompat D)) B.region ≠ ⊤ := by
    rw [haarLogVolume_of_lt_top B.region_lt_top]
    exact ENNReal.ofReal_ne_top
  have hreal :
      (haarLogVolume (actualC3LogShellTensorHaar (S2717C3 R redCompat hredCompat torCompat htorCompat orbCompat horbCompat secCompat hsecCompat cusCompat hcusCompat D))
          (actualC3LogShellTensorRegion (S2717C3 R redCompat hredCompat torCompat htorCompat orbCompat horbCompat secCompat hsecCompat cusCompat hcusCompat D))).toReal
        ≤ (haarLogVolume (actualC3LogShellTensorHaar (S2717C3 R redCompat hredCompat torCompat htorCompat orbCompat horbCompat secCompat hsecCompat cusCompat hcusCompat D)) B.region).toReal := by
    exact ENNReal.toReal_mono hne hmono
  linarith

def qPilotHaarBridgeRows : List (String × String) :=
  [ ("QPilotHaarRegionData", "explicit target data (region/volume_eq/theta_subset_region), no inhabitant") ,
    ("qPilotLogVolume_le_thetaHullLogVolume_of_bridge", "PROVED from S2807 + Haar monotonicity") ,
    ("GAP-HAAR-Q", "no inhabitant of QPilotHaarRegionData (q-side C3-block region missing)") ,
    ("GAP-THETA-Q", "thetaRegion subset region direction (negHaarLog)") ]

theorem qPilotHaarBridgeRows_length : qPilotHaarBridgeRows.length = 4 := rfl

end LeanFormal.IUT.XiFPaper.Mzk1QPilotHaarBridgeActual