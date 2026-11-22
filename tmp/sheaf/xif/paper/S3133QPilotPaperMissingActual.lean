import tmp.sheaf.xif.paper.QPilotGlobalLineBundleActual
import tmp.sheaf.xif.paper.QPilotGlobalLogVolumeFromQActual
import tmp.sheaf.xif.paper.GlobalRealifiedFrobenioidActual
import tmp.sheaf.xif.paper.QPilotGlobalDivisorOnCarrier
import LeanFormal.IUT.IUTIII.Theorem311.SourceFTimesMuPrimeStripPolyIsomorphism
import LeanFormal.IUT.IUTIII.Theorem311.SourceOriginalInput

/-!
# Exact missing paper objects of the global q-pilot chain (IUT III §3)

Source positions: Def 3.8(i), pp. 112-113 (iut3.txt 6740-6769) q-pilot object
in the global realified Frobenioid; §3 p. 16 (880-893) log-volume -|log q|;
p. 17 (950-978) q_v action on log-shells in the arithmetic holomorphic structure
of the vertical line (1,circ); p. 18-19 (993-1084) log-Kummer correspondence and
Kummer-detachment; Step (xi) (10988-11034) log-volume of the region representing
the q-pilot object on 1,circ U_Q is -|log q|.

Actual and available: the realified global Frobenioid carrier C^boxplus_mod
(GlobalRealifiedFrobenioidActual), the zero-locus prime divisors
(QPilotGlobalDivisorOnCarrier), the q-pilot log-volume
(QPilotGlobalLogVolumeFromQActual), the q-pilot arithmetic line-bundle object
(S3133QPilotIdealFamilyObjectActual).

Missing and recorded here as exact structures: the full FrobenioidPresentation
(FrobenioidAxioms) of C^boxplus_mod; the paper (1,0) q-pilot
F^boxplus-triangleright-x-mu-prime-strip and its identification; the log-Kummer
representation on 1,circ U_Q; the paper procession-normalized log-volume.
No missing field is assumed or inhabited.  No toy/True/PUnit/axiom/sorry.
WRITE-ONLY; no local compile; queued.
-/

noncomputable section
open scoped BigOperators
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT.XiFPaper.S3133QPilotPaperMissingActual

open LeanFormal.IUT
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.N8Closure.NativeInput
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.ArithmeticQPilotLogVolume
open LeanFormal.IUT.XiFPaper.GlobalRealifiedFrobenioidActual
open LeanFormal.IUT.XiFPaper.QPilotGlobalDivisorOnCarrier
open LeanFormal.IUT.XiFPaper.QPilotGlobalObjectActual
open LeanFormal.IUT.XiFPaper.QPilotGlobalLogVolumeFromQActual
open LeanFormal.IUT.XiFPaper.QPilotZeroLocusDivisorActual
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.Theorem311Source

universe u ua uv upi umon ui

section RealifiedPresentation

variable {l : PrimeGeFive}
variable (X : N8NativeInput l)

/-- Exact missing object: the full FrobenioidPresentation (Definition 1.3
FrobenioidAxioms) of the realified global Frobenioid C^boxplus_mod (IUT III
Example 3.6(ii); §1-2).  Its actual carrier data is constructed in
GlobalRealifiedFrobenioidActual; missing is the packaging as a presentation
together with the identifications making the q_v zero-locus divisor an object
of it. -/
structure MissingRealifiedGlobalFrobenioidPresentation
    (X : N8NativeInput l) where
  /-- actual realified carrier (GlobalRealifiedFrobenioidActual) -/
  carrier : GlobalRealifiedFrobenioidCarrier
  carrier_eq : carrier = globalRealifiedFrobenioidCarrier X
  /-- missing full FrobenioidPresentation of C^boxplus_mod -/
  presentation : Iut.FrobenioidPresentation
  realified_divisorMonoid_identification : Prop
  realified_degree_identification : Prop
  qPilotRealification_identification : Prop

/-- Existence of the missing realified presentation data. -/
def MissingRealifiedGlobalFrobenioidPresentationData
    (X : N8NativeInput l) : Prop :=
  Nonempty (MissingRealifiedGlobalFrobenioidPresentation X)

end RealifiedPresentation

section PrimeStrip

variable {l : PrimeGeFive} {V : Type uv}
variable (I : OriginalInput.{ua, uv, upi, umon, ui} l V)

/-- The actual candidate F^boxplus-triangleright-x-mu-prime-strip obtained from
the actual (1,0) F-prime-strip (IUT II, Cor. 4.10, (i), (iii)). -/
noncomputable def qPilotTimesMuCandidate :
    SourceFTimesMuPrimeStrip V :=
  SourceFTimesMuPrimeStrip.canonical (I.fPrimeStripAt 1 0)

/-- The candidate's underlying F-prime-strip is the actual (1,0) F-prime-strip. -/
theorem qPilotTimesMuCandidate_toFPrimeStrip :
    (qPilotTimesMuCandidate I).toFPrimeStrip = I.fPrimeStripAt 1 0 := rfl

/-- Exact missing object: the paper (1,0) q-pilot F^boxplus-triangleright-x-mu-
prime-strip (IUT III Def 3.8(i), pp. 112-113) with its identification to the
actual times-mu candidate and the full poly-isomorphism data of the
Theta-times-mu LGP-link (Def 3.8(ii)). -/
structure MissingQPilotFTimesMuPrimeStripIdentification
    (I : OriginalInput.{ua, uv, upi, umon, ui} l V) where
  /-- actual underlying F-prime-strip of the times-mu candidate -/
  candidateUnderlying : FPrimeStrip.{umon, uv, upi} V
  candidateUnderlying_eq :
    candidateUnderlying = (qPilotTimesMuCandidate I).toFPrimeStrip
  /-- missing paper underlying F-prime-strip of the q-pilot strip -/
  paperStripUnderlying : FPrimeStrip.{umon, uv, upi} V
  paperStrip_underlying_identification : Prop
  paperTimesMuLayer_missing : Prop
  paperStrip_polyIso_identification : Prop
  lgpLink_codomain_identification : Prop

/-- Existence of the missing paper q-pilot prime-strip identification. -/
def MissingQPilotFTimesMuPrimeStripIdentificationData
    (I : OriginalInput.{ua, uv, upi, umon, ui} l V) : Prop :=
  Nonempty (MissingQPilotFTimesMuPrimeStripIdentification I)

end PrimeStrip

section OneColumnLogKummer

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]

/-- Exact missing object: the log-Kummer representation of the q-pilot object on
1,circ U_Q (IUT III p. 17-18, iut3.txt 950-1013): the action of the q_v on the
log-shells I_v, the representing region on 1,circ U_Q, and the identification of
its log-volume with the actual -|log q|.  The q_v family and log-volume are
actual; the action, region and log-volume identification are not constructed. -/
structure MissingQPilotLogKummerOneColumn
    (T : SourceNativeInitialThetaData.{0} l)
    [Fintype (Bad (nativePlaceSelection T))] where
  qV : (b : Bad (nativePlaceSelection T)) →
    FinitePlaceQCandidate ((nativeBadLift T).lift b)
  qV_eq : qV = qVFamily T
  logShellAction : Prop
  representedRegion : Prop
  representedRegion_logVolume : Prop

/-- Existence of the missing log-Kummer representation on 1,circ U_Q. -/
def MissingQPilotLogKummerOneColumnData
    (T : SourceNativeInitialThetaData.{0} l)
    [Fintype (Bad (nativePlaceSelection T))] : Prop :=
  Nonempty (MissingQPilotLogKummerOneColumn T)

end OneColumnLogKummer

section ProcessionNormalizedLogVolume

variable {l : PrimeGeFive}
variable (X : N8NativeInput l)
variable [Fintype (Bad (nativePlaceSelection X.S))]

/-- Exact missing object: the paper procession-normalized q-pilot log-volume
-|log q| (IUT III Cor. 3.12, pp. 173-174; IUT IV Thm 1.10) identified with the
actual q-pilot log-volume read off the actual q_v family. -/
structure MissingQPilotProcessionNormalizedLogVolume
    (X : N8NativeInput l) [Fintype (Bad (nativePlaceSelection X.S))] where
  qPilotLogVolume : Real
  qPilotLogVolume_eq : qPilotLogVolume = qPilotQGlobalLogVolume X
  processionNormalization_identification : Prop
  paperLogVolume_identification : Prop

/-- Existence of the missing procession-normalized q-pilot log-volume. -/
def MissingQPilotProcessionNormalizedLogVolumeData
    (X : N8NativeInput l) [Fintype (Bad (nativePlaceSelection X.S))] : Prop :=
  Nonempty (MissingQPilotProcessionNormalizedLogVolume X)

/-- The actual part: the q-pilot log-volume read off the actual q_v family is
- sum_b |log q_v(b)|. -/
theorem qPilotLogVolume_actual_formula :
    qPilotQGlobalLogVolume X =
      -∑ b : Bad (nativePlaceSelection X.S),
        localLogMagnitude (qVFamily X.S b) :=
  qPilotQGlobalLogVolume_eq_neg_sum_qVLogMagnitude X

end ProcessionNormalizedLogVolume

end LeanFormal.IUT.XiFPaper.S3133QPilotPaperMissingActual
