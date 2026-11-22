import tmp.sheaf.xif.paper.LogKummerCorrespondenceFromSource
import tmp.sheaf.xif.paper.S3133QPilotFTimesMuCandidateActual
import tmp.sheaf.xif.paper.S3133QPilotBatchAInputActual
import tmp.sheaf.xif.paper.S3133QPilotLogVolumeSignActual
import tmp.sheaf.xif.paper.S3130QCLeHCActual
import LeanFormal.IUT.IUTIII.Theorem311.SourceKummerEvaluationArrows
import LeanFormal.IUT.IUTII.Kummer.TimesMuQuotient
import LeanFormal.IUT.IUTI.InitialTheta.SourcePlacePartitionReduction
import tmp.sheaf.n8.closure.NativeInput
import Mathlib

/-!
# Actual log-Kummer correspondence data attached to the q-pilot (1,0) strip

Source: IUT III, Theorem 3.11, (ii), (iii); Proposition 3.10; IUT II, Definition
4.9, (i).  IUT III, p. 17 (iut3.txt lines 950-978): the q-pilot object at (1,0)
is represented by means of the action of the various q_v, v in V_bad, on the
log-shells that arise from the log-link, in the context of the arithmetic
holomorphic structure of the vertical line (1,circ).  IUT III, p. 18 (iut3.txt
lines 993-1013): one must work with the entire log-Kummer correspondence, not a
single Kummer isomorphism, and with the indeterminacy (Ind3).  Step (xi) of the
proof of Corollary 3.12, p. 180-183 (iut3.txt lines 10988-11034): the log-volume
of the region that arises from the representation of the q-pilot object on
1,circ U_Q is -|log q|.

This file constructs, from the actual source log-Kummer data
(LogKummerCorrespondenceFromSource) and the actual candidate (1,0) strip
(S3133QPilotFTimesMuCandidateActual), the REAL log-Kummer correspondence data
attached to the q-pilot strip:

* qPilotOneColumnLogKummer: the actual 1-column log-Kummer correspondence object
  built from the actual source F-prime-strip links;
* qPilotColumnKummerArrow m: the actual vertical Kummer arrow at every m, with
  the candidate (1,0) strip as codomain strip;
* qPilotIPLData: the actual IPL data relating the q-pilot strip to the 1-column;
* the candidate x-mu fiber and x-mu action are identified with the codomain fiber
  and the actual times-mu action of the 1-column Kummer arrows.

The exact missing paper object is recorded at the end: the represented REGION on
1,circ U_Q together with its log-volume -|log q| (the ambient 1,circ U_Q carrier
and its log-volume functional are not constructed in the repository).
No arbitrary/toy carrier is used; the missing region is a documented Missing
structure, not a claim.  No inequality is asserted.  No sorry/axiom.  WRITE-ONLY.
-/

noncomputable section
open scoped BigOperators
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT.XiFPaper.S3133QPilotOneColumnLogKummerActual

open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.LogKummerCorrespondenceFromSource
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.N8Closure.NativeInput
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.XiFPaper.S3133QPilotFTimesMuCandidateActual
open LeanFormal.IUT.XiFPaper.S3133QPilotReadoutActual
open LeanFormal.IUT.XiFPaper.S3133QPilotLogVolumeSignActual

universe u ua uv upi umon ui

variable {l : PrimeGeFive} {V : Type uv}
variable (I : OriginalInput.{ua, uv, upi, umon, ui} l V)

/-- The actual 1-column log-Kummer correspondence of the source input, built from
the actual source F-prime-strip links (Theorem 3.11, (ii)). -/
noncomputable def qPilotOneColumnLogKummer :
    OneColumnLogKummerData (ActualKummerGroup (I := I)) I :=
  actualOneColumnLogKummer (I := I)

/-- The m-th Kummer card of the actual 1-column log-Kummer correspondence is the
actual vertical Kummer arrow. -/
theorem qPilotOneColumnLogKummer_kummer (m : Int) :
    ((qPilotOneColumnLogKummer I).kummer.kummer m) =
      actualKummerArrow (I := I) m := rfl

/-- The actual vertical Kummer arrow at m, with the actual candidate (1,0)
q-pilot strip as codomain strip. -/
noncomputable def qPilotColumnKummerArrow (m : Int) :
    SourceKummerArrow (ActualKummerGroup (I := I))
      (I.fPrimeStripAt 1 m)
      (qPilotFTimesMuPrimeStripAt10Actual I).toFPrimeStrip :=
  actualKummerArrow (I := I) m

/-- The q-pilot column Kummer arrow is the actual vertical Kummer arrow. -/
theorem qPilotColumnKummerArrow_eq (m : Int) :
    qPilotColumnKummerArrow I m = actualKummerArrow (I := I) m := rfl

/-- The candidate (1,0) strip's x-mu fiber at v is the codomain fiber of the
actual 1-column Kummer arrows: the torsion quotient of the actual (1,0) unit
group. -/
theorem qPilotCandidate_timesMu_eq_kummerCodomainFiber (v : V) :
    (qPilotFTimesMuPrimeStripAt10Actual I).timesMu v =
      TimesMuQuotient ((I.fPrimeStripAt 1 0).Mon v)ˣ := rfl

/-- The candidate strip's x-mu action is the actual times-mu action of the (1,0)
strip, i.e. the action on the codomain fibers of the actual Kummer arrows. -/
theorem qPilotCandidate_timesMuAction_eq_actualTimesMuActionAt (v : V) :
    (qPilotFTimesMuPrimeStripAt10Actual I).timesMuAction v =
      actualTimesMuActionAt (I := I) 0 v := rfl

/-- The actual IPL data of the 1-column: the lower horizontal links, the Kummer
arrow and the evaluation unit arrow relating the q-pilot strip to the 1-column. -/
noncomputable def qPilotIPLData :
    IPLActual (G := ActualKummerGroup (I := I))
      (iplIntermediateStrip (I := I)) (iplGauStrip (I := I))
      (iplEnvStrip (I := I)) (iplCoricEnvStrip (I := I))
      (iplQPilotStrip (I := I)) :=
  actualIPLData (I := I)

/-- The q-pilot IPL data is the actual IPL data of the source log-Kummer
correspondence. -/
theorem qPilotIPLData_eq :
    (qPilotIPLData I) = actualIPLData (I := I) := rfl

/-- The q-pilot strip used in the actual IPL data is the actual (1,0) F-prime-strip,
which is the underlying F-prime-strip of the candidate times-mu strip. -/
theorem qPilotIPLData_qPilotStrip :
    iplQPilotStrip (I := I) =
      (qPilotFTimesMuPrimeStripAt10Actual I).toFPrimeStrip := rfl

/-- The actual procession-normalized q-pilot log-volume magnitude on the native
side, which is the target |log q| of the represented region. -/
theorem qPilotOneColumn_targetMagnitude
    (X : N8NativeInput l) [Fintype (Bad (nativePlaceSelection X.S))]
    [Nonempty (Bad (nativePlaceSelection X.S))]
    (h : ∀ b : Bad (nativePlaceSelection X.S),
      LeanFormal.IUT.XiFPaper.S2135Layer1SplitActual.S2135PrimeAlignmentRequired X.S b) :
    0 < -qPilotNormalizedGlobalReadout X h :=
  neg_pos.mpr (qPilotNormalizedGlobalReadout_neg X h)

/-- Exact missing paper object: the log-Kummer REPRESENTATION of the q-pilot
object on 1,circ U_Q — the region of the 1-column that represents the q-pilot
object and its log-volume, which equals the actual q-pilot magnitude |log q|
(Step (xi) of Corollary 3.12, iut3.txt lines 11030-11034).  The actual
log-Kummer correspondence, Kummer arrows, candidate (1,0) strip and IPL data are
constructed in this file; what is missing is the ambient 1,circ U_Q carrier with
its region and log-volume functional.  No field is inhabited here. -/
structure MissingQPilotOneColumnRegion (Ambient : Type u) (qPilotMagnitude : Real) where
  /-- the region of 1,circ U_Q representing the q-pilot object -/
  region : Set Ambient
  /-- the log-volume functional of the ambient 1,circ U_Q carrier -/
  logVolume : Set Ambient → ENNReal
  /-- log-volume is monotone under inclusion -/
  logVolume_mono : ∀ {S T : Set Ambient}, S ⊆ T → logVolume S ≤ logVolume T
  /-- missing: the log-volume of the represented region is |log q| -/
  region_logVolume_eq : logVolume region = ENNReal.ofReal qPilotMagnitude

/-- The existence of the missing 1,circ U_Q representation region data. -/
def MissingQPilotOneColumnRegionData
    (Ambient : Type u) (qPilotMagnitude : Real) : Prop :=
  Nonempty (MissingQPilotOneColumnRegion Ambient qPilotMagnitude)

end LeanFormal.IUT.XiFPaper.S3133QPilotOneColumnLogKummerActual
