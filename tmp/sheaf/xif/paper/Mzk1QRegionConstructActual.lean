/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.Mzk1C3LogShellTensorLActual
import LeanFormal.IUT.ABCBridge.Geometry.FinitePlaceIQHullInterface
import Mathlib.Tactic

/-! # A1061: explicit q-pilot Haar region construction on the L/C3 carrier

| field | value |
|---|---|---|
| Status | PARTIAL: theta region explicit; q-pilot region built from an explicit **homeomorphism** of the C3 tensor block.  The actual qroot-to-C3 scaling map is NOT constructed (type/field mismatch), so the homeomorphism remains an explicit parameter, not a fake qroot action. |
| Source | `Mzk1C3LogShellTensorLActual.lean`; `PaperRootCompletionTensorActual.lean` (`rootNormedUnit`, `rootNormedElement`) |
| GAP | `rootNormedUnit : (rootNormedExtension T b)ˣ` over `sourceRootField T b`; C3 block is `FinitePadicTensor` of `CommonPrimeCompletion` fibers (ring structure exists, but no element corresponding to qroot); no map `rootNormedExtension → CommonPrimeCompletion` in C3L. |
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT.XiFPaper.Mzk1QRegionConstructActual

open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.C3LogShellTensorLActual
open LeanFormal.IUT.XiFPaper.S1391C3LSourcePilotActual
open MeasureTheory

variable {l : PrimeGeFive}
variable {I : OriginalInput l (FinitePrimePlace 2 7)}
variable (C3L : SourcePilotRegionDataL (I := I))

local instance qRegionBlockMeasurableSpace :
    MeasurableSpace (C3LogShellTensorBlockL (I := I) C3L) := borel _

local instance qRegionBlockBorelSpace :
    BorelSpace (C3LogShellTensorBlockL (I := I) C3L) := ⟨rfl⟩

/-- The explicit theta-side Haar region: the L-carrier tensor integral region. -/
noncomputable def thetaHaarRegion : Set (C3LogShellTensorBlockL (I := I) C3L) :=
  actualC3LogShellTensorRegionL (I := I) C3L

/-- The q-pilot Haar region, defined as the image of the theta region under an
explicit homeomorphism of the C3 tensor block. -/
noncomputable def qPilotHaarRegion
    (e : C3LogShellTensorBlockL (I := I) C3L ≃ₜ
      C3LogShellTensorBlockL (I := I) C3L) :
    Set (C3LogShellTensorBlockL (I := I) C3L) :=
  e '' thetaHaarRegion (I := I) C3L

/-- The image region is compact, from compactness of the theta region. -/
theorem qPilotHaarRegion_compact
    (e : C3LogShellTensorBlockL (I := I) C3L ≃ₜ
      C3LogShellTensorBlockL (I := I) C3L) :
    IsCompact (qPilotHaarRegion (I := I) C3L e) :=
  (actualC3LogShellTensorRegionL_compact (I := I) C3L).image e.continuous

/-- The q-pilot Haar measure on the same block. -/
noncomputable def qPilotHaar : Measure (C3LogShellTensorBlockL (I := I) C3L) :=
  actualC3LogShellTensorHaarL (I := I) C3L

/-- **Volume target** (explicit Prop): the q-pilot Haar region has signed
log-volume `-A`, with `A` the paper `|log q|`. -/
def QPilotVolumeTarget
    (e : C3LogShellTensorBlockL (I := I) C3L ≃ₜ
      C3LogShellTensorBlockL (I := I) C3L)
    (A : Real) : Prop :=
  (haarLogVolume (qPilotHaar (I := I) C3L) (qPilotHaarRegion (I := I) C3L e)).toReal = -A

/-- **Containment target** (explicit Prop): theta region inside the q-pilot region. -/
def ThetaSubsetQPilotTarget
    (e : C3LogShellTensorBlockL (I := I) C3L ≃ₜ
      C3LogShellTensorBlockL (I := I) C3L) : Prop :=
  thetaHaarRegion (I := I) C3L ⊆ qPilotHaarRegion (I := I) C3L e

/-- Exact obstruction record: the qroot unit type is not an element of the block. -/
def qRootScalarObstruction : String :=
  "rootNormedUnit lives in rootNormedExtension over sourceRootField; " ++
  "C3LogShellTensorBlockL has a FinitePadicTensor ring structure but no qroot element; " ++
  "no map rootNormedExtension -> CommonPrimeCompletion is present in C3L."

def rows : List (String × String × String) :=
  [ ("thetaHaarRegion", "actualC3LogShellTensorRegionL", "DEF (green)"),
    ("qPilotHaarRegion", "e '' thetaHaarRegion for homeomorphism e", "DEF (explicit parameter e)"),
    ("qPilotHaarRegion_compact", "compactness of the image", "PROVED from theta compactness"),
    ("QPilotVolumeTarget", "log-volume = -A", "Prop (not proved)"),
    ("ThetaSubsetQPilotTarget", "theta ⊆ q", "Prop (not proved)"),
    ("qRootScalarObstruction", "qroot type vs tensor block", "GAP (exact)") ]

theorem rows_length : rows.length = 6 := rfl

end LeanFormal.IUT.XiFPaper.Mzk1QRegionConstructActual

end