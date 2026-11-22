import tmp.sheaf.xif.paper.S3133S3131PlaceIndexComparisonActual
import tmp.sheaf.xif.paper.S3133M1InjectionReductionActual

/-!
# M1 concrete donor: tensorIndex := Bad and prime=5 match (component, not a paper object)

COMPONENT, not a paper object.  Named consumers: qpilot M1 concrete donor,
lattice model-route record, mainline/lattice in-model R1.

M1's own recorded obstruction is 'bad <-> C3.tensorIndex equivalence + base-place
equality'.  In the CONCRETE Gaussian donor these are constructible: take
tensorIndex := Bad (nativePlaceSelection T) with the refl equivalence, and use
the hypothesis that every bad base place lies above the rational prime 5 (for
the concrete Gaussian stage-4 spec this is citable from
S3132ConcreteGaussianPlaceSpecActual.packet_rationalPrime_eq_five).  Then the
actual prime-level match qVFamTensorP T b = C3.p holds whenever C3.p = 5, i.e.
the TensorIndexPlaceCompatibility residual CLOSES on the concrete donor.  The
remaining exact field is the index identification C3.tensorIndex = Bad (...)
(plus the place-compatible transport), recorded as the donor structure below.
No sorry/axiom/toy.  WRITE-ONLY.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 2000000

namespace LeanFormal.IUT.XiFPaper.S3133M1ConcretePrimeMatchActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.N8Closure.SourcePilotRegion
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.VbadPlaceIndexingActual
open LeanFormal.IUT.XiFPaper.S3133S3131PlaceIndexComparisonActual
open LeanFormal.IUT.XiFPaper.S3133M1InjectionReductionActual

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable {V : Type} {I : OriginalInput l V}
variable (C3 : SourcePilotRegionData (l := l) (V := V) I)

/-- The concrete tensor index type: the actual Bad index set (Lead/M1 recipe). -/
abbrev S3133ConcreteTensorIndex : Type := Bad (nativePlaceSelection T)

/-- The concrete bad <-> tensorIndex equivalence: refl on the Bad index set. -/
def S3133ConcreteTensorIndexEquiv :
    Bad (nativePlaceSelection T) ≃ S3133ConcreteTensorIndex T :=
  Equiv.refl _

/-- On the concrete donor every bad base place above 5 gives q-parameter prime 5. -/
theorem S3133ConcreteTensorPrime_eq_five
    (hbad5 : ∀ b : Bad (nativePlaceSelection T),
      (completionRationalPrime b.1).val = 5)
    (b : Bad (nativePlaceSelection T)) :
    qVFamTensorP T b = 5 := by
  rw [qVFamTensorP_eq_base_val T b]
  exact hbad5 b

/-- Prime-level M1 match CLOSES on the concrete donor: all bad q-parameter primes
equal C3.p once C3.p = 5. -/
theorem S3131BadTensorPrimeMatch_concrete
    (hbad5 : ∀ b : Bad (nativePlaceSelection T),
      (completionRationalPrime b.1).val = 5)
    (hp : C3.p = 5) : S3131BadTensorPrimeMatch T C3 := by
  intro b
  rw [S3133ConcreteTensorPrime_eq_five T hbad5 b, hp]

/-- Concrete M1 donor data: the index identification and the C3 prime.  The
index identification C3.tensorIndex = Bad (...) is the exact remaining donor
field (it is the V_mod_bijection/index side of IUT I Def 3.1(b),(e)); the place
compatibility is recorded separately by S3133M1Remaining. -/
structure S3133M1ConcreteDonor where
  index_eq : C3.tensorIndex = S3133ConcreteTensorIndex T
  p_eq : C3.p = 5

end LeanFormal.IUT.XiFPaper.S3133M1ConcretePrimeMatchActual
