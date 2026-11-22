import tmp.sheaf.n8.closure.C6ActualEllOutLeTheta
import LeanFormal.IUT.IUTI.InitialTheta.SourceInitialThetaData
import Mathlib

/-!
# O4 paper Theta/ellOut from SourceInitialThetaData (paper input)

Paper input is SourceInitialThetaData l; we use only its actual fields:
candidate.arithmetic, candidate.V, candidate.place, and its actual clauses.
No SourceDefinition31Data shell is used.

From an actual C6 SourceAllowedOutput J whose old-chain arithmetic agrees with
the paper S.candidate.arithmetic, we construct:

- paper Theta_hull := actual C6 hull log-volume (B.iqInterface.logVolume B.hull);
- paper ellOut_hull := actual C6 region log-volume;
and prove unconditionally ellOut_hull <= Theta_hull from J.hullPoss and actual
C6 logVolume monotonicity.

For the Real degree-normalized candidate, the inequality is proved from the
exact C6 data package PaperThetaGapData (compatibility, hullPoss, actual C6
normalization, region-positive/hull-finite).  That package is the exact
remaining paper-data gap; it is not asserted.  No arbitrary J or Theta is
invented.
-/

noncomputable section

open MeasureTheory
open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.N8Closure.NativeInput
open LeanFormal.IUT.N8Closure.P6Comparison
open LeanFormal.IUT.N8Closure.C6ConstructedOutput
open LeanFormal.IUT.N8Closure.C6ActualEllOutLeTheta
open LeanFormal.IUT.N8C6ActualIQ

namespace LeanFormal.IUT.N8Closure.O4PaperTheta

universe ua uv upi umon ui uL

variable {l : PrimeGeFive} (X : N8NativeInput l)

/-- Paper arithmetic, read from the actual SourceInitialThetaData candidate. -/
def paperArithmetic (S : SourceInitialThetaData l) :=
  S.candidate.arithmetic

/-- Paper place type. -/
def paperV (S : SourceInitialThetaData l) :=
  S.candidate.V

/-- Paper place map. -/
def paperPlace (S : SourceInitialThetaData l) (v : paperV S) :=
  S.candidate.place v

/-- The paper clauses supply the actual bad-set nonempty fact. -/
theorem paper_bad_nonempty (S : SourceInitialThetaData l) :
    S.candidate.VbadMod.Nonempty :=
  S.clause_b_bad_nonempty

/-- Compatibility of an actual C6 output bridge with the paper arithmetic. -/
def PaperArithmeticCompatible
    (S : SourceInitialThetaData l) (J : SourceAllowedOutput X) : Prop :=
  J.bridge.input.initial.arithmetic = paperArithmetic S

/-- Paper Theta as the actual C6 hull log-volume. -/
noncomputable def PaperTheta (J : SourceAllowedOutput X) : ENNReal :=
  actualHullLogVolume X J

/-- Paper ellOut as the actual C6 region log-volume. -/
noncomputable def PaperEllOut (J : SourceAllowedOutput X) : ENNReal :=
  actualOutputLogVolume X J

/-- Real degree-normalized paper Theta candidate. -/
noncomputable def PaperThetaReal (J : SourceAllowedOutput X) : ℝ :=
  actualThetaCandidate X J

/-- Real degree-normalized paper ellOut. -/
noncomputable def PaperEllOutReal (J : SourceAllowedOutput X) : ℝ :=
  actualEllOut X J

/-- Actual paper ellOut <= paper Theta in the C6 hull-log sense. -/
theorem paperEllOut_le_paperTheta
    (J : SourceAllowedOutput X) (hHull : J.hullPoss) :
    PaperEllOut X J ≤ PaperTheta X J :=
  actualOutputLogVolume_le_hullLogVolume X J hHull

/-- Exact paper C6 data package needed for the Real normalization comparison. -/
def PaperThetaGapData
    (S : SourceInitialThetaData l) (J : SourceAllowedOutput X) : Prop :=
  PaperArithmeticCompatible X S J ∧
    J.hullPoss ∧
    C6NormalizedLogVolumeActual X J ∧
    C6RegionPositiveFinite X J

/-- Conditional Real comparison from the exact C6 data package. -/
theorem paperEllOutReal_le_paperThetaReal_of_gapData
    (S : SourceInitialThetaData l) (J : SourceAllowedOutput X)
    (h : PaperThetaGapData X S J) :
    PaperEllOutReal X J ≤ PaperThetaReal X J :=
  actualEllOut_le_actualThetaCandidate X J h.2.1 h.2.2.1 h.2.2.2

/-- The unconditional paper-data gap target: existence of an actual C6 output
compatible with the paper arithmetic and satisfying the exact C6 package.
This is not asserted; it is the remaining paper-data obligation. -/
def PaperThetaDataGap (S : SourceInitialThetaData l) : Prop :=
  ∃ J : SourceAllowedOutput X, PaperThetaGapData X S J

end LeanFormal.IUT.N8Closure.O4PaperTheta
