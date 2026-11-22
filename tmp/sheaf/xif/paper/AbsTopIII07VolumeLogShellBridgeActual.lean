import tmp.sheaf.xif.paper.AbsTopIII02LocalVolumesActual
import tmp.sheaf.xif.paper.AbsTopIII06WeightedVolumeBridgeActual
import tmp.sheaf.xif.paper.AbsTopIII01LogShellActual
import tmp.sheaf.xif.paper.AbsTopIII03Cor510Actual

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

/-!
# STEP 0 prior-art: AbsTopIII02|AbsTopIII06|LGPWeightedVolumeBridge|lgpWeightedLogVolume|cor510 -> hits stage4 AbsTopIII02LocalVolumesActual (volume statement ledger) + AbsTopIII06WeightedVolumeBridgeActual (measure->real bridge, CardAMPL slot) + hull AbsTopIII01/03 -> REUSE (no re-proof; combined record only).

# [AbsTopIII] 07: volume-side <-> log-shell bridge record (hull/stage4 joint)

Corpus: papers/motizuki_corpus/text/Topics in Absolute Anabelian Geometry III.txt.
Prop 5.7 (i)(a) normalization mu_k(O_k)=1 (corpus 7915-7935) <-> hull's concrete
unit-reference Haar mass 1 (S3129:151, AbsTopIII03Cor510Actual); Cor 5.10 (i)
finite log-volume <-> cor510_logShell_finite; the weighted/log-volume bridge to
the CardAMPL/hull slot is stage4's AbsTopIII06 (LGPWeightedVolumeBridge).
This file only records the correspondence rows (no new proof, no discharge claim).
-/

namespace LeanFormal.IUT.XiFPaper.AbsTopIII07VolumeLogShellBridgeActual

open LeanFormal.IUT.XiFPaper.AbsTopIII02LocalVolumesActual
open LeanFormal.IUT.XiFPaper.AbsTopIII06WeightedVolumeBridgeActual
open LeanFormal.IUT.XiFPaper.AbsTopIII01LogShellActual
open LeanFormal.IUT.XiFPaper.AbsTopIII03Cor510Actual

/-- A combined bridge row: (AbsTopIII item, stage4 volume anchor, hull log-shell anchor, status). -/
structure VolumeLogShellRow where
  item : String
  volumeAnchor : String
  logShellAnchor : String
  status : String

/-- The volume-side <-> log-shell bridge rows. -/
def volumeLogShellRows : List VolumeLogShellRow :=
  [ { item := "Prop 5.7 (i)(a) normalisation mu_k(O_k) = 1",
      volumeAnchor := "AbsTopIII02LocalVolumesActual absTopIIILocalVolumeStatements (statement ledger)",
      logShellAnchor := "AbsTopIII03Cor510Actual cor510_sourceHullHaar_unit (mass = 1 PROVED); stage4 AbsTopIII07NormalizedLocalVolumeActual.normalizedHaar_unitBall / completionNormalizedHaar_unitBall (mu_k(O_k)=1 PROVED instance)",
      status := "concrete p-adic side PROVED (stage4 normalized instance re-anchored; mu_k^log(m_k^n) formula remains PENDING)" }
  , { item := "Cor 5.10 (i) finite log-volume",
      volumeAnchor := "AbsTopIII02LocalVolumesActual Cor 5.10 row",
      logShellAnchor := "AbsTopIII03Cor510Actual cor510_logShell_finite/cor510_logVolume_unit (PROVED)",
      status := "concrete p-adic side PROVED" }
  , { item := "weighted log-volume <-> hull/CardAMPL slot",
      volumeAnchor := "AbsTopIII06WeightedVolumeBridgeActual LGPWeightedVolumeBridge.le_theta (adapts CardAMPLThetaBoundSupply.realVolume_le)",
      logShellAnchor := "AbsTopIII01LogShellActual log-shell dictionary",
      status := "bridge datum available; hull<=theta remains H4 boundary" }
  , { item := "Prop 5.7 (i)(b) p_v-adic scaling",
      volumeAnchor := "AbsTopIII02LocalVolumesActual scaling row (statement)",
      logShellAnchor := "AbsTopIII08PvAdicScalingActual (reuse S3137LogShellHaarLogVolumeScalingActual, PROVED)",
      status := "concrete p-adic scaling PROVED (tree reuse)" } ]

/-- The bridge record has four rows. -/
theorem volumeLogShellRows_length : volumeLogShellRows.length = 4 := rfl

#check VolumeLogShellRow
#check volumeLogShellRows
#check volumeLogShellRows_length

end LeanFormal.IUT.XiFPaper.AbsTopIII07VolumeLogShellBridgeActual