import tmp.sheaf.n8.closure.C7QOTensorNormalization

/-!
# C7 qO/region identification: actual sign criterion

Q = qORegionLogVolume X < 0 is actual.  R = c6RegionVolume.toReal is the
actual C6 region log-volume (a signed Haar log-volume).  The target Q=R is
therefore impossible whenever R >= 0: Q<0 <= R.

If R is interpreted as a positive log-volume magnitude, the sign-correct
normalization is Q = -R.  Production proves neither R>=0 nor Q=R; this file
records the exact sign/normalization gap.  No arbitrary A/Z.
-/

noncomputable section

set_option linter.unusedSectionVars false
set_option linter.checkUnivs false
set_option linter.overlappingInstances false
set_option linter.unusedVariables false

open LeanFormal.IUT
open LeanFormal.IUT.N8Closure.NativeInput
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.N8Closure.PaperC6RegionConstructed2
open LeanFormal.IUT.N8Closure.C7PaperDivisorActual2
open LeanFormal.IUT.N8Closure.C7QOTensorNormalization

namespace LeanFormal.IUT.N8Closure.C7QORegionIdentificationActual

variable {l : PrimeGeFive} (X : N8NativeInput l) (S : SourceInitialThetaData l)
  (P : PaperC6RegionInput S)

/-- Actual qO Q is negative. -/
theorem Q_neg_actual : Q X < 0 := Q_neg X

/-- Symbolic sign obstruction: a nonnegative region log-volume cannot equal
the negative qO log-volume. -/
theorem Q_ne_region_of_region_nonneg (hR : 0 <= rRegion S P) :
    Q X ≠ rRegion S P := by
  intro h
  have hQ := Q_neg X
  linarith

/-- Correct sign convention if R is a positive magnitude. -/
def NegativeNormalization : Prop := Q X = -rRegion S P

/-- The negative normalization is the sign-correct alternative to Q=R when
R is a positive log-volume magnitude. -/
theorem negativeNormalization_iff :
    NegativeNormalization X S P ↔ Q X = -rRegion S P :=
  Iff.rfl

/-- Exact missing sign premise for the current Q=R target. -/
def MissingRegionNonnegative : Prop := 0 <= rRegion S P

/-- Exact target remains Q=R; no production proof. -/
def MissingQORegionIdentificationActual : Prop := Q X = rRegion S P

/-- Verdict: if R>=0, the only consistent normalization is Q=-R; Q=R would
require R<0, which is not proved. -/
theorem correct_normalization_under_nonnegative (hR : 0 <= rRegion S P) :
    Q X = -rRegion S P ∨ Q X ≠ rRegion S P :=
  Or.inr (Q_ne_region_of_region_nonneg X S P hR)

end LeanFormal.IUT.N8Closure.C7QORegionIdentificationActual
