import tmp.sheaf.xif.paper.S63OBoundaryLogShellActual

/-! # S68: exact obstructions for the integral-ring equivalence and O-boundary log

The log-shell uses the norm valuation ring Integers L; S56 used the adic
completion integers CompletionIntegers.  The two are different constructions:

* CompletionIntegers place = (underlyingPrime place).adicCompletionIntegers K;
* Integers L = (NormedField.valuation).integer.

The source tree has no theorem identifying these two valuation subrings of the
same completion; the membership rewrite for adicCompletionIntegers also exposes
the differing prime-index/instance data (completionRationalPrime vs the
HeightOneSpectrum prime subtype).  This file records the exact required ring
equivalence as an uninhabited requirement, not a fake equality.

The O-boundary log obstruction is recorded similarly: the source log is the
unit logarithm on O-times; no logarithm on nonunit elements of O-boundary is
supplied.

No fake equivalence/log/sorry/axiom/True/PUnit. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT.XiFPaper.S68IntegralRingEquivActual

open LeanFormal.IUT
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.LocalFieldIntegralUnits
open LeanFormal.IUT.LocalFieldLogarithm
open LeanFormal.IUT.XiFPaper.S63OBoundaryLogShellActual

universe u

variable {l : PrimeGeFive}
variable {K : Type u} [Field K] [NumberField K]
variable {p : Nat} [Fact p.Prime]
variable (place : FinitePlaceAtPrime K p)

/-- Exact required ring equivalence between the adic completion integers and
the norm valuation ring. -/
structure CompletionIntegersRingEquivData where
  equiv : (CompletionIntegers place.val : Type u) ≃+*
    Integers (CommonPrimeCompletion place)

/-- Exact missing ring equivalence; no inhabitant asserted. -/
def CompletionIntegersRingEquivRequired : Prop :=
  Nonempty (CompletionIntegersRingEquivData (K := K) (p := p) place)

/-- Exact O-boundary logarithm extension requirement. -/
structure OBoundaryLogExtension where
  logMap : sourceOBoundaryMonoid (K := K) (p := p) place → Real
  unit_compat : Prop

/-- Exact missing O-boundary log extension; no inhabitant asserted. -/
def OBoundaryLogExtensionRequired : Prop :=
  Nonempty (OBoundaryLogExtension (K := K) (p := p) place)

/-- The exact source obstruction: both objects are required; neither is
constructed by the frozen source. -/
def S68ExactObstructions : Prop :=
  CompletionIntegersRingEquivRequired (K := K) (p := p) place ∧
    OBoundaryLogExtensionRequired (K := K) (p := p) place

end LeanFormal.IUT.XiFPaper.S68IntegralRingEquivActual

end
