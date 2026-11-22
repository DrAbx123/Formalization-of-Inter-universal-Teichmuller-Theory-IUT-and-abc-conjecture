import tmp.sheaf.xif.paper.ArithmeticLineBundleActual
import tmp.sheaf.xif.paper.VbadPlaceIndexingActual
import Mathlib.Tactic

/-! # CONDITIONAL: actual q-pilot line-bundle source from bad-prime ideals

Construction: the product over the actual native bad K-places of their maximal
prime ideals is an actual ideal of O_K.  This gives an actual
PaperQPilotLineBundleSource, with the definitional identification
  qPilotIdeal = product_b (nativeBadToKPlace T b).maximalIdeal
as its source_identification proposition.

Exact GAP: this product of bad-prime ideals is not claimed to equal the paper
q-pilot q-parameter divisor (which may include powers/label weights).  The
paper semantic identification remains a named missing proposition.
-/

noncomputable section
set_option linter.unusedVariables false

namespace LeanFormal.IUT.XiFPaper.Mzk1PaperQPilotLineBundleSourceActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.XiFPaperArithmeticLineBundle
open LeanFormal.IUT.XiFPaper.VbadPlaceIndexingActual

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]

/-- Product of the actual bad-place maximal ideals in O_K. -/
noncomputable def badPrimeIdealProduct : Ideal (SourceOK (A := T.arithmetic)) := by
  classical
  exact ∏ b : Bad (nativePlaceSelection T),
    (nativeBadToKPlace T b).maximalIdeal.asIdeal

/-- The actual q-pilot ideal candidate: the bad-prime product. -/
noncomputable def qPilotIdealOfBadPrimes : Ideal (SourceOK (A := T.arithmetic)) :=
  badPrimeIdealProduct T

/-- Definitional factorised form of the candidate ideal. -/
theorem qPilotIdealOfBadPrimes_eq :
    qPilotIdealOfBadPrimes T =
      ∏ b : Bad (nativePlaceSelection T),
        (nativeBadToKPlace T b).maximalIdeal.asIdeal := rfl

/-- Source-identification proposition attached to the construction. -/
def BadPrimeProductIdentification : Prop :=
  qPilotIdealOfBadPrimes T =
    ∏ b : Bad (nativePlaceSelection T),
      (nativeBadToKPlace T b).maximalIdeal.asIdeal

theorem badPrimeProductIdentification_holds : BadPrimeProductIdentification T :=
  qPilotIdealOfBadPrimes_eq T

/-- Actual q-pilot line-bundle source from the bad-prime ideal product. -/
noncomputable def qPilotLineBundleSourceOfBadPrimes :
    PaperQPilotLineBundleSource (A := T.arithmetic) where
  qPilotLineBundle :=
    (qPilotIdealOfBadPrimes T :
      FractionalIdeal (nonZeroDivisors (SourceOK (A := T.arithmetic)))
        T.arithmetic.K)
  qPilotIdeal := qPilotIdealOfBadPrimes T
  qPilot_lineBundle_eq := rfl
  qPilot_source_identification := BadPrimeProductIdentification T

/-- Constructed source has the bad-prime product ideal. -/
theorem qPilotLineBundleSourceOfBadPrimes_ideal :
    (qPilotLineBundleSourceOfBadPrimes T).qPilotIdeal = qPilotIdealOfBadPrimes T := rfl

/-- Constructed source's line bundle is the fractional ideal of the product. -/
theorem qPilotLineBundleSourceOfBadPrimes_lineBundle :
    (qPilotLineBundleSourceOfBadPrimes T).qPilotLineBundle =
      (qPilotIdealOfBadPrimes T :
        FractionalIdeal (nonZeroDivisors (SourceOK (A := T.arithmetic)))
          T.arithmetic.K) := rfl

/-- The source-identification proposition is inhabited for this construction. -/
theorem qPilotLineBundleSourceOfBadPrimes_identification :
    (qPilotLineBundleSourceOfBadPrimes T).qPilot_source_identification :=
  badPrimeProductIdentification_holds T

#check badPrimeIdealProduct
#check qPilotIdealOfBadPrimes
#check qPilotIdealOfBadPrimes_eq
#check BadPrimeProductIdentification
#check qPilotLineBundleSourceOfBadPrimes
#check qPilotLineBundleSourceOfBadPrimes_identification
end LeanFormal.IUT.XiFPaper.Mzk1PaperQPilotLineBundleSourceActual
end
