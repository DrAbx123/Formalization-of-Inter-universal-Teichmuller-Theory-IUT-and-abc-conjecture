import LeanFormal.IUT.IUTIII.Corollary312.StepXI.SourceSharedBoundary
import LeanFormal.IUT.IUTIII.Theorem311.SourceKummerEvaluationArrows
import LeanFormal.IUT.IUTIII.Corollary312.StepXI.HolomorphicHull.SourceImageHullVolume
import Mathlib.Tactic

/-!
# Actual Theta-link / log-Kummer comparison layer

This file records the exact source-level obligation layer for the paper's
Theta-link and log-Kummer comparison, using only actual project carriers:

* the 1-column log-Kummer correspondence is the actual
  SourceVerticalKummerCard for the source column n = 1;
* the Theta-link factorization and the four-corner Kummer/evaluation square are
  the actual SourceLinkFactorization and SourceKummerEvaluationSquare records;
* the q-pilot anchor is the actual source prime strip at (1,0), with the
  identification qPilotStrip = I.primeStripAt 1 0 kept as an explicit field;
* the q-pilot signed log-volume is -|log(q)| for the actual one-column q;
* the comparison is the actual source signed image/hull comparison
  sourceSignedImageLogVolume <= sourceSignedHullLogVolume.

No inhabitant of the comparison layer is asserted here: the structures below
are exact named obligations, not surrogates for them.  The paper's q-pilot
object, the analytic log-shell/Kummer carriers, and the signed comparison itself
remain obligations; no True/PUnit/axiom/sorry/placeholder is used.
-/

noncomputable section
set_option maxHeartbeats 1000000
set_option relaxedAutoImplicit false

namespace LeanFormal.IUT
namespace Theorem311Source
namespace OriginalInput

universe uG ua uv upi umon ui

variable {l : PrimeGeFive} {V : Type uv}
variable (G : Type uG) [Group G] [TopologicalSpace G]
variable (I : OriginalInput.{ua, uv, upi, umon, ui} l V)

/-! ## 1. The 1-column log-Kummer correspondence -/

/-- The actual 1-column vertical log-Kummer obligation of Theorem 3.11, (ii):
the source vertical Kummer arrows along the column n = 1. -/
structure OneColumnLogKummerData where
  kummer : SourceVerticalKummerCard G I 1

/-- The 1-column packet used by the log-Kummer correspondence. -/
def oneColumnPacketAtZero : FiniteThetaPacket l :=
  I.oneColumnPacket 0

/-- The actual one-column q parameter. -/
def oneColumnQAtZero : Real :=
  I.oneColumnQ 0

theorem oneColumnQAtZero_eq_packet_q :
    I.oneColumnQAtZero = (I.oneColumnPacket 0).q := rfl

theorem oneColumnQAtZero_pos : 0 < I.oneColumnQAtZero := by
  unfold oneColumnQAtZero oneColumnQ
  exact (I.oneColumnPacket 0).q_pos

theorem oneColumnQAtZero_ne_zero : I.oneColumnQAtZero ≠ 0 :=
  ne_of_gt I.oneColumnQAtZero_pos

/-! ## 2. The q-pilot link identification -/

/-- The actual q-pilot anchor at (1,0): the source prime strip at (1,0).  The
identification with the source qPilotStrip vertex is kept explicit, not
silently assumed. -/
def qPilotStripAtOneZero : FPrimeStrip V :=
  I.primeStripAt 1 0

/-- The signed q-pilot log-volume -|log(q)| for the actual one-column q. -/
def qPilotSignedLogVolume : Real :=
  - |Real.log I.oneColumnQAtZero|

/-- The q-pilot strip identification field: the qPilotStrip vertex of the
Theta-link factorization equals the actual (1,0) source strip. -/
structure QPilotLinkIdentification (qPilotStrip : FPrimeStrip V) where
  qPilotStrip_eq : qPilotStrip = I.qPilotStripAtOneZero
  qPilotLogVolume : Real
  qPilotLogVolume_eq : qPilotLogVolume = I.qPilotSignedLogVolume

theorem qPilotSignedLogVolume_eq :
    I.qPilotSignedLogVolume = - |Real.log I.oneColumnQAtZero| := rfl

theorem qPilotSignedLogVolume_nonpos : I.qPilotSignedLogVolume <= 0 := by
  unfold qPilotSignedLogVolume
  exact neg_nonpos.mpr (abs_nonneg _)

/-- The signed q-pilot log-volume vanishes exactly at q = 1. -/
theorem qPilotSignedLogVolume_eq_zero_iff :
    I.qPilotSignedLogVolume = 0 ↔ I.oneColumnQAtZero = 1 := by
  unfold qPilotSignedLogVolume
  rw [neg_eq_zero, abs_eq_zero, Real.log_eq_zero]
  constructor
  · rintro (h0 | h1 | hneg)
    · exact False.elim ((ne_of_gt I.oneColumnQAtZero_pos) h0)
    · exact h1
    · nlinarith [I.oneColumnQAtZero_pos]
  · intro h
    exact Or.inr (Or.inl h)

/-! ## 3. Theta-link factorization and Kummer/evaluation square -/

/-- The actual Theta-link/IPL factorization obligation of Remark 3.11.1, (iii),
at fixed source strip vertices. -/
structure ThetaLinkFactorizationData
    (intermediateStrip gauStrip envStrip coricEnvStrip qPilotStrip : FPrimeStrip V) where
  link : SourceLinkFactorization G intermediateStrip gauStrip envStrip
    coricEnvStrip qPilotStrip

/-- The Theta-link factorization composite is exactly the actual IPL composite. -/
theorem thetaLink_inputLink_eq_composite
    {intermediateStrip gauStrip envStrip coricEnvStrip qPilotStrip : FPrimeStrip V}
    (F : ThetaLinkFactorizationData G intermediateStrip gauStrip envStrip
      coricEnvStrip qPilotStrip) :
    F.link.inputLink = F.link.composite :=
  F.link.inputLink_eq_composite

/-- The actual four-corner Kummer/evaluation square obligation of Remark 3.10.2
and Theorem 3.11, (iii), (a), (b), at fixed source strip vertices. -/
structure ThetaLinkSquareData
    (upperLeft upperRight lowerLeft lowerRight : FPrimeStrip V) where
  square : SourceKummerEvaluationSquare G upperLeft upperRight lowerLeft lowerRight

/-- The two paths of the actual Kummer/evaluation square agree. -/
theorem thetaLinkSquare_domain_eq_codomain
    {upperLeft upperRight lowerLeft lowerRight : FPrimeStrip V}
    (S : ThetaLinkSquareData G upperLeft upperRight lowerLeft lowerRight) :
    S.square.domainExpression = S.square.codomainExpression :=
  S.square.domainExpression_eq_codomainExpression

/-! ## 4. Signed hull comparison -/

/-- The actual signed image log-volume at the source hull stage. -/
def signedImageLogVolume (v : V) (R : I.SourceImageRealization v)
    (n : ThetaPilotCarrier l) : Real :=
  -(I.sourceSetVolume v (I.possibleThetaPilotImageSet v R n)).toReal

/-- The actual signed hull log-volume at the source hull stage. -/
def signedHullLogVolume (v : V) (R : I.SourceImageRealization v)
    (n : ThetaPilotCarrier l) : Real :=
  -(I.sourceSetVolume v
    (I.sourceHolomorphicHull v R n : Set (I.ThetaPilotPoint v))).toReal

theorem signedImageLogVolume_eq (v : V) (R : I.SourceImageRealization v)
    (n : ThetaPilotCarrier l) :
    I.signedImageLogVolume v R n =
      -(I.sourceSetVolume v (I.possibleThetaPilotImageSet v R n)).toReal := rfl

theorem signedHullLogVolume_eq (v : V) (R : I.SourceImageRealization v)
    (n : ThetaPilotCarrier l) :
    I.signedHullLogVolume v R n =
      -(I.sourceSetVolume v
        (I.sourceHolomorphicHull v R n : Set (I.ThetaPilotPoint v))).toReal := rfl

theorem signedImageLogVolume_nonpos (v : V) (R : I.SourceImageRealization v)
    (n : ThetaPilotCarrier l) : I.signedImageLogVolume v R n <= 0 := by
  unfold signedImageLogVolume
  exact neg_nonpos.mpr ENNReal.toReal_nonneg

theorem signedHullLogVolume_nonpos (v : V) (R : I.SourceImageRealization v)
    (n : ThetaPilotCarrier l) : I.signedHullLogVolume v R n <= 0 := by
  unfold signedHullLogVolume
  exact neg_nonpos.mpr ENNReal.toReal_nonneg

/-- The exact signed comparison obligation of Step (xi-f): the signed image
log-volume is at most the signed hull log-volume.  This is the actual
source-level comparison, recorded as a named field, not asserted. -/
structure SignedHullComparison (v : V) (R : I.SourceImageRealization v)
    (n : ThetaPilotCarrier l) where
  image : Real
  image_eq : image = I.signedImageLogVolume v R n
  hull : Real
  hull_eq : hull = I.signedHullLogVolume v R n
  signedComparison : image <= hull

/-- Any inhabitant of the signed comparison gives the actual Step (xi-f)
inequality in source signed form. -/
theorem signedComparison_holds (v : V) (R : I.SourceImageRealization v)
    (n : ThetaPilotCarrier l) (C : SignedHullComparison I v R n) :
    I.signedImageLogVolume v R n <= I.signedHullLogVolume v R n := by
  rw [← C.image_eq, ← C.hull_eq]
  exact C.signedComparison

/-! ## 5. The actual comparison layer -/

/-- The complete actual Theta-link/log-Kummer comparison layer.  Each field is
an exact source obligation or an actual source identification; no field is a
True/PUnit placeholder. -/
structure ThetaLinkLogKummerActual
    (G : Type uG) [Group G] [TopologicalSpace G]
    (I : OriginalInput.{ua, uv, upi, umon, ui} l V)
    (v : V) (R : I.SourceImageRealization v) (n : ThetaPilotCarrier l)
    (intermediateStrip gauStrip envStrip coricEnvStrip qPilotStrip : FPrimeStrip V)
    (upperLeft upperRight lowerLeft lowerRight : FPrimeStrip V)
    (qPilotStripSquare : FPrimeStrip V) where
  oneColumn : OneColumnLogKummerData G I
  link : ThetaLinkFactorizationData G intermediateStrip gauStrip envStrip
    coricEnvStrip qPilotStrip
  square : ThetaLinkSquareData G upperLeft upperRight lowerLeft lowerRight
  qPilot : QPilotLinkIdentification I qPilotStripSquare
  comparison : SignedHullComparison I v R n

/-- The q-pilot log-volume read out of the actual comparison layer. -/
theorem thetaLinkLogKummer_qPilotLogVolume_eq
    {v : V} {R : I.SourceImageRealization v} {n : ThetaPilotCarrier l}
    {intermediateStrip gauStrip envStrip coricEnvStrip qPilotStrip : FPrimeStrip V}
    {upperLeft upperRight lowerLeft lowerRight qPilotStripSquare : FPrimeStrip V}
    (A : ThetaLinkLogKummerActual G I v R n intermediateStrip gauStrip envStrip
      coricEnvStrip qPilotStrip upperLeft upperRight lowerLeft lowerRight
      qPilotStripSquare) :
    A.qPilot.qPilotLogVolume = I.qPilotSignedLogVolume :=
  A.qPilot.qPilotLogVolume_eq

/-- The comparison layer yields the actual signed Step (xi-f) comparison. -/
theorem thetaLinkLogKummer_signedComparison
    {v : V} {R : I.SourceImageRealization v} {n : ThetaPilotCarrier l}
    {intermediateStrip gauStrip envStrip coricEnvStrip qPilotStrip : FPrimeStrip V}
    {upperLeft upperRight lowerLeft lowerRight qPilotStripSquare : FPrimeStrip V}
    (A : ThetaLinkLogKummerActual G I v R n intermediateStrip gauStrip envStrip
      coricEnvStrip qPilotStrip upperLeft upperRight lowerLeft lowerRight
      qPilotStripSquare) :
    I.signedImageLogVolume v R n <= I.signedHullLogVolume v R n :=
  signedComparison_holds I v R n A.comparison

/-- The 1-column log-Kummer obligation is part of the comparison layer. -/
def thetaLinkLogKummer_oneColumnKummer
    {v : V} {R : I.SourceImageRealization v} {n : ThetaPilotCarrier l}
    {intermediateStrip gauStrip envStrip coricEnvStrip qPilotStrip : FPrimeStrip V}
    {upperLeft upperRight lowerLeft lowerRight qPilotStripSquare : FPrimeStrip V}
    (A : ThetaLinkLogKummerActual G I v R n intermediateStrip gauStrip envStrip
      coricEnvStrip qPilotStrip upperLeft upperRight lowerLeft lowerRight
      qPilotStripSquare) :
    SourceVerticalKummerCard G I 1 :=
  A.oneColumn.kummer

end OriginalInput
end Theorem311Source

end IUT
