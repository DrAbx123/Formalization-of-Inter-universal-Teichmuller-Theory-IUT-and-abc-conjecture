import tmp.sheaf.xif.paper.BasePlaceQCandidateActual
import tmp.sheaf.xif.paper.QPilotZeroLocusDivisorActual
import LeanFormal.IUT.IUTIII.Theorem311.SourceFTimesMuPrimeStripPolyIsomorphism
import LeanFormal.IUT.IUTIII.Theorem311.SourceKummerEvaluationArrows

/-!
# Actual (1,0) F^boxplus-triangleright-x-mu candidate strip and q_v base descent data

IUT II, Corollary 4.10, (i), pp. 158-159: the F^boxplus-prime-strip
†F^boxplus_Δ from the F-prime-strip of the Hodge theater; (iii), p. 159:
the associated F^boxplus-triangleright-x-mu-prime-strip.  IUT III,
Definition 3.8, (i), pp. 112-113: the q-pilot object is determined by q_v
for v in V_bad; IUT III, p. 17: its log-volume is -|log q|.

This file constructs:

* qPilotFTimesMuPrimeStripAt10 I: the actual SourceFTimesMuPrimeStrip
  (the source-facing type for an F^boxplus-triangleright-x-mu-prime-strip)
  obtained from the actual (1,0) F-prime-strip I.fPrimeStripAt 1 0 by the
  canonical times-mu construction;
* QVBaseDescentFamily: the exact V_bad-indexed base q descent data from the
  actual clause-B F-place q_v candidates to q candidates at the base Fmod
  places;
* qVBaseFamily: the conditional actual base q family from such descent data.

It does NOT assert that the constructed SourceFTimesMuPrimeStrip is the paper's
q-pilot F^boxplus-triangleright-x-mu-prime-strip, does not construct the
(1,0) q-pilot object or its base q descent, and does not identify the q_v
parameters.  Those are exact remaining object-level fields.  No inequality is
asserted.  No toy/True/PUnit/axiom/sorry.  WRITE-ONLY; no local compile; queued.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 1000000

namespace LeanFormal.IUT.XiFPaper.QPilotFTimesMuPrimeStripActualAdapted

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.XiFPaper.QPilotZeroLocusDivisorActual

universe ua uv upi umon ui

variable {l : PrimeGeFive} {V : Type uv}
variable (I : OriginalInput.{ua, uv, upi, umon, ui} l V)

/-- The actual source-facing F^boxplus-triangleright-x-mu-prime-strip obtained
from the actual (1,0) F-prime-strip by the canonical times-mu construction. -/
noncomputable def qPilotFTimesMuPrimeStripAt10 :
    SourceFTimesMuPrimeStrip V :=
  SourceFTimesMuPrimeStrip.canonical (I.fPrimeStripAt 1 0)

/-- The underlying F-prime-strip of the constructed candidate is exactly the
actual (1,0) F-prime-strip. -/
theorem qPilotFTimesMuPrimeStripAt10_toFPrimeStrip :
    (qPilotFTimesMuPrimeStripAt10 I).toFPrimeStrip =
      I.fPrimeStripAt 1 0 := rfl

/-- The times-mu fiber of the constructed candidate is the torsion quotient of
the actual unit group at each place. -/
theorem qPilotFTimesMuPrimeStripAt10_timesMu_eq (v : V) :
    (qPilotFTimesMuPrimeStripAt10 I).timesMu v =
      TimesMuQuotient ((I.fPrimeStripAt 1 0).Mon v)ˣ := rfl

/-- Exact base q descent data: for every native bad place b, a descent from the
actual F-completion at the lift of b to the base Fmod-completion, preserving the
actual clause-B q as a nonzero, contracting q candidate.

This is the exact missing local map: the repository has completionMap in the
opposite direction (base -> extension), not a descent extension -> base. -/
structure QVBaseDescentFamily
    (T : SourceNativeInitialThetaData.{0} l) where
  descent : (b : Bad (nativePlaceSelection T)) →
    NumberFieldFinitePlace.Completion ((nativeBadLift T).lift b) →
      NumberFieldFinitePlace.Completion b.1
  q_ne_zero : (b : Bad (nativePlaceSelection T)) →
    descent b (qVFamily T b).q ≠ 0
  valuation_lt_one : (b : Bad (nativePlaceSelection T)) →
    (Valued.v (descent b (qVFamily T b).q) : WithZero (Multiplicative Int)) < 1

/-- The actual base q family obtained from explicit V_bad-indexed descent
data.  The q at the base Fmod place is the descent image of the actual clause-B
q_v at the F-place over b. -/
noncomputable def qVBaseFamily
    (T : SourceNativeInitialThetaData.{0} l)
    (D : QVBaseDescentFamily T)
    (b : Bad (nativePlaceSelection T)) :
    FinitePlaceQCandidate b.1 where
  q := D.descent b (qVFamily T b).q
  q_ne_zero := D.q_ne_zero b
  valuation_lt_one := D.valuation_lt_one b

/-- The base q family is the descent image of the actual clause-B q_v. -/
theorem qVBaseFamily_q
    (T : SourceNativeInitialThetaData.{0} l)
    (D : QVBaseDescentFamily T)
    (b : Bad (nativePlaceSelection T)) :
    (qVBaseFamily T D b).q = D.descent b (qVFamily T b).q := rfl

/-- The exact missing V_bad-indexed base q descent family, as a proposition. -/
def MissingQVBaseDescentFamily
    (T : SourceNativeInitialThetaData.{0} l) : Prop :=
  Nonempty (QVBaseDescentFamily T)


end LeanFormal.IUT.XiFPaper.QPilotFTimesMuPrimeStripActualAdapted
