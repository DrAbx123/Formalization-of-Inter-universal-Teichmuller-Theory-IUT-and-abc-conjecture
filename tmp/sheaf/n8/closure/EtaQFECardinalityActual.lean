import tmp.sheaf.n8.closure.EtaVolumeIndexFormulaAttempt
import LeanFormal.IUT.IUTIII.Corollary312.ArithmeticQPilotBaseChange

/-!
# Eta q/e/f cardinality actual attempt

Candidate actual e/f at the native F-place are the production absolute local
ramification index and residue degree:

  e_X := localRamificationIndex (k := Q) (nativeFPlaceOverBad X)
  f_X := localResidueDegree   (k := Q) (nativeFPlaceOverBad X).

They do not by themselves prove LogShellQFECardinalityHypothesis.  The missing
production piece is the p*-congruence quotient cardinality

  #((Integers K)^x / logShellCongruenceUnits) =
    residueCard ^ (e*s - 1) * (residueCard - 1),

i.e. the DVR/principal-congruence-filtration computation.  Also no production
theorem relates native q.order to these e/f.  We record the exact QFE target and
the missing-data gap; no e/f is fabricated.
-/

noncomputable section

namespace LeanFormal.IUT.N8Closure.EtaQFECardinalityActual

open scoped Padic

open LeanFormal.IUT
open LeanFormal.IUT.N8Closure.NativeInput
open LeanFormal.IUT.N8Closure.NativeC3
open LeanFormal.IUT.N8Closure.C9QPilotRegion
open LeanFormal.IUT.N8Closure.EtaFPlaceNormalizedComparison
open LeanFormal.IUT.N8Closure.EtaVolumeIndexFormulaAttempt
open LeanFormal.IUT.LocalFieldLogarithm
open LeanFormal.IUT.LocalFieldIntegralUnits
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.ArithmeticQPilotBaseChange

variable {l : PrimeGeFive}
variable {X : N8NativeInput l}

/-- Actual candidate absolute ramification exponent at the native F-place. -/
def fPlaceRamificationCandidate (X : N8NativeInput l) : Nat :=
  ArithmeticQPilotBaseChange.localRamificationIndex (k := ℚ)
    (nativeFPlaceOverBad X)

/-- Actual candidate absolute residue degree at the native F-place. -/
def fPlaceResidueDegreeCandidate (X : N8NativeInput l) : Nat :=
  ArithmeticQPilotBaseChange.localResidueDegree (k := ℚ)
    (nativeFPlaceOverBad X)

/-- Exact QFE target at the actual candidates. -/
def EtaFPlaceQFECandidateTarget (X : N8NativeInput l) : Prop :=
  LogShellQFECardinalityHypothesis (K := FPlaceCompletion X)
    (p := nativePrime X) (fPlaceRamificationCandidate X)
    (fPlaceResidueDegreeCandidate X)

/-- The missing p*-congruence cardinality (third QFE field), stated without
assuming it. -/
def FPlaceCongruenceCardinalityTarget (X : N8NativeInput l) : Prop :=
  Nat.card ((Integers (FPlaceCompletion X))ˣ ⧸
      logShellCongruenceUnits (K := FPlaceCompletion X) (p := nativePrime X)) =
    logShellResidueCard (K := FPlaceCompletion X) ^
        (fPlaceRamificationCandidate X *
            logShellScaleExponentFactor (p := nativePrime X) - 1) *
      (logShellResidueCard (K := FPlaceCompletion X) - 1)

/-- The missing residue-card component at the actual candidate f. -/
def FPlaceResidueCardTarget (X : N8NativeInput l) : Prop :=
  logShellResidueCard (K := FPlaceCompletion X) =
    (nativePrime X) ^ fPlaceResidueDegreeCandidate X

/-- Exact missing-data package: QFE would follow from the two displayed
arithmetic targets plus one_le e, but neither target is in production. -/
structure EtaQFECardinalityMissingData (X : N8NativeInput l) where
  one_le_ramification :
    1 ≤ fPlaceRamificationCandidate X
  residueCard_target : FPlaceResidueCardTarget X
  congruenceCard_target : FPlaceCongruenceCardinalityTarget X

/-- QFE target is equivalent to its three literal fields; this records that
the congruence-cardinality field is the missing arithmetic content. -/
theorem qfeCandidateTarget_iff_fields (X : N8NativeInput l) :
    EtaFPlaceQFECandidateTarget X ↔
      (1 ≤ fPlaceRamificationCandidate X ∧
        FPlaceResidueCardTarget X ∧
        FPlaceCongruenceCardinalityTarget X) := by
  constructor
  · intro h
    exact ⟨h.one_le_ramificationExponent,
      h.residueCard_eq_prime_pow_inertiaDegree,
      h.congruenceQuotient_card_eq_residueUnits⟩
  · rintro ⟨h1, h2, h3⟩
    exact ⟨h1, h2, h3⟩

/-- No production theorem currently supplies the missing confluence; the
target remains exactly this QFE package. -/
def EtaQFECardinalityUnresolved (X : N8NativeInput l) : Prop :=
  EtaFPlaceQFECandidateTarget X

end LeanFormal.IUT.N8Closure.EtaQFECardinalityActual
