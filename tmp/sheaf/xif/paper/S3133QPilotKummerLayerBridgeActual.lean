import tmp.sheaf.xif.paper.S3133QPilotFTimesMuCandidateActual
import tmp.sheaf.xif.paper.LogKummerCorrespondenceFromSource
import tmp.sheaf.xif.paper.S3133QPilotBatchAInputActual
import tmp.sheaf.xif.paper.S3133QPilotPaperMissingActual
import tmp.sheaf.xif.paper.S3133QPilotLogVolumeSignActual
import LeanFormal.IUT.IUTII.Kummer.TimesMuQuotient
import LeanFormal.IUT.IUTI.InitialTheta.SourcePlacePartitionReduction
import tmp.sheaf.n8.closure.NativeInput

/-!
# Bridge: actual (1,0) q-pilot candidate strip, 1-column Kummer layer, and the
# procession-normalized reading

Source: IUT II, Corollary 4.10, (i), (iii), pp. 158-159 (F^boxplus-prime-strip and
F^boxplus-triangleright-x-mu-prime-strip); IUT III, Definition 3.8, (i), (ii),
pp. 112-113 (q-pilot object; Theta-times-mu LGP-link); IUT III, p. 16
(iut3.txt 880-893) log-volume -|log q|; Remark 3.1.1, (ii)-(iv), p. 95-97
(procession normalization weights 1/N_v); Step (xi) of Corollary 3.12,
p. 180-183 (iut3.txt 10988-11034).

This file bridges the two actual constructions:

* the actual candidate (1,0) q-pilot F^boxplus-triangleright-x-mu-prime-strip
  (canonical times-mu construction from the actual (1,0) F-prime-strip);
* the actual 1-column log-Kummer layer data (LogKummerCorrespondenceFromSource):
  its vertical Kummer arrows have codomain strip the actual (1,0) strip, and the
  candidate's x-mu fiber/action are the codomain fiber/action of those arrows;
* the actual procession-normalized q-pilot reading (-|log q| with the actual
  Remark 3.1.1 weights), which is the log-volume target of the missing
  representation on 1,circ U_Q.

It also states the exact remaining identification to the paper (1,0) q-pilot
F^boxplus-triangleright-x-mu-prime-strip: the candidate fixes the underlying
F-prime-strip, but the paper strip is the codomain of the Theta-times-mu
LGP-link, identified only up to the full poly-isomorphism of
F^boxplus-triangleright-x-mu-prime-strips; this is exactly
MissingQPilotFTimesMuPrimeStripIdentification of S3133QPilotPaperMissingActual.
No missing datum is asserted.  No inequality.  No sorry/axiom.  WRITE-ONLY.
-/

noncomputable section
open scoped BigOperators
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT.XiFPaper.S3133QPilotKummerLayerBridgeActual

open LeanFormal.IUT
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.N8Closure.NativeInput
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.LogKummerCorrespondenceFromSource
open LeanFormal.IUT.XiFPaper.S3133QPilotFTimesMuCandidateActual
open LeanFormal.IUT.XiFPaper.S3133QPilotPaperMissingActual
open LeanFormal.IUT.XiFPaper.S3133QPilotLogVolumeSignActual
open LeanFormal.IUT.XiFPaper.S3133QPilotReadoutActual
open LeanFormal.IUT.XiFPaper.NativeQVPilotNormalizedLogVolumeActual

universe u ua uv upi umon ui uG

section Strip

variable {l : PrimeGeFive} {V : Type uv}
variable (I : OriginalInput.{ua, uv, upi, umon, ui} l V)

/-- The candidate (1,0) strip's underlying F-prime-strip is the actual (1,0)
F-prime-strip — the actual part of the paper q-pilot strip identification. -/
theorem qPilotCandidate_underlying_strip :
    (qPilotFTimesMuPrimeStripAt10Actual I).toFPrimeStrip = I.fPrimeStripAt 1 0 := rfl

/-- The candidate strip's x-mu fiber is the codomain fiber of the actual vertical
Kummer arrows of the 1-column log-Kummer correspondence. -/
theorem qPilotCandidate_kummerCodomainFiber (m : Int) (v : V) :
    (qPilotFTimesMuPrimeStripAt10Actual I).timesMu v =
      TimesMuQuotient ((I.fPrimeStripAt 1 0).Mon v)ˣ := rfl

/-- The candidate strip's x-mu action is the actual times-mu action of the (1,0)
strip, i.e. the codomain action of the actual vertical Kummer arrows. -/
theorem qPilotCandidate_kummerCodomainAction (v : V) :
    (qPilotFTimesMuPrimeStripAt10Actual I).timesMuAction v =
      actualTimesMuActionAt (I := I) 0 v := rfl

/-- The actual vertical Kummer arrow at m has the candidate (1,0) strip as
codomain strip. -/
noncomputable def qPilotBridgeKummerArrow (m : Int) :
    SourceKummerArrow (ActualKummerGroup (I := I))
      (I.fPrimeStripAt 1 m)
      (qPilotFTimesMuPrimeStripAt10Actual I).toFPrimeStrip :=
  actualKummerArrow (I := I) m

/-- The bridge Kummer arrow is the actual vertical Kummer arrow. -/
theorem qPilotBridgeKummerArrow_eq (m : Int) :
    qPilotBridgeKummerArrow I m = actualKummerArrow (I := I) m := rfl

/-- The actual part of the paper (1,0) q-pilot strip identification: the candidate
fixes the underlying F-prime-strip and the x-mu fiber/action data.  The remaining
identification to the paper strip is exactly
MissingQPilotFTimesMuPrimeStripIdentification, recorded separately. -/
theorem qPilotCandidate_actualPart :
    (qPilotFTimesMuPrimeStripAt10Actual I).toFPrimeStrip = I.fPrimeStripAt 1 0 ∧
      (∀ v, (qPilotFTimesMuPrimeStripAt10Actual I).timesMu v =
        TimesMuQuotient ((I.fPrimeStripAt 1 0).Mon v)ˣ) ∧
      (∀ v, (qPilotFTimesMuPrimeStripAt10Actual I).timesMuAction v =
        actualTimesMuActionAt (I := I) 0 v) :=
  ⟨rfl, fun v => rfl, fun v => rfl⟩

end Strip

section Reading

variable {l : PrimeGeFive}
variable (X : N8NativeInput l)
variable [Fintype (Bad (nativePlaceSelection X.S))]

/-- The procession-normalized Batch A Q_C readout attached to the bridged
construction is the actual native q-pilot scalar -|log q|. -/
theorem qPilotBridge_normalized_readout
    (h : ∀ b : Bad (nativePlaceSelection X.S),
      LeanFormal.IUT.XiFPaper.S2135Layer1SplitActual.S2135PrimeAlignmentRequired X.S b) :
    qPilotNormalizedGlobalReadout X h =
      nativeQVPilotNormalizedSignedLogVolume X.S :=
  qPilotNormalizedGlobalReadout_eq X h

/-- The magnitude |log q| of the procession-normalized reading is positive when
V_bad is nonempty. -/
theorem qPilotBridge_normalized_magnitude_pos
    [Nonempty (Bad (nativePlaceSelection X.S))]
    (h : ∀ b : Bad (nativePlaceSelection X.S),
      LeanFormal.IUT.XiFPaper.S2135Layer1SplitActual.S2135PrimeAlignmentRequired X.S b) :
    0 < -qPilotNormalizedGlobalReadout X h :=
  neg_pos.mpr (qPilotNormalizedGlobalReadout_neg X h)

end Reading

end LeanFormal.IUT.XiFPaper.S3133QPilotKummerLayerBridgeActual
