import Mathlib.RingTheory.DedekindDomain.AdicValuation
import Mathlib.NumberTheory.NumberField.Basic
import LeanFormal.IUT.Audit.Status

/-!
# S3137: M2a bridge status record (task-67) — M2a OPEN, closure in flight

CORRECTION (03:49): M2a is NOT closed.  The earlier closed claim cited qpilot
result 147613 SIZE=2578, which is their DOC-ONLY PARKED module (0 declarations),
not a proof; reverted on qpilot's retraction.  Verification rule (recorded in
the maintenance protocol): a citable closure needs EXIT=0 on a file containing
ACTUAL declarations plus a trio/no-axiom probe — doc-only files are not evidence.

Bridge candidate: Mathlib's
`IsDedekindDomain.HeightOneSpectrum.valuedAdicCompletion_eq_valuation'`
(Mathlib/RingTheory/DedekindDomain/AdicValuation.lean:950):
  Valued.v ((k : K) : v.adicCompletion K) = v.valuation K k.
Presentation caveat: this form is the WithVal/global presentation; the goal in
`S3133RationalFiveCompletionNorm` uses the Coe/algebraMap presentation, and in
our imports the two did not unify definitionally (Elab attempt EXIT=1), which is
exactly the remaining glue qpilot is fixing.  Nothing here is asserted as proved.
Data only.  WRITE-ONLY.
-/

open scoped WithZero Valued

namespace LeanFormal.IUT.XiFPaper.S3137M2aBridgeMissingActual

open LeanFormal.IUT.Audit

/-- The M2a bridge statement shape (recorded, NOT proved here). -/
def S3137ValuedCoeRatStatement : Prop :=
  ∀ (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ℚ)) (x : ℚ),
    Valued.v ((x : ℚ) : v.adicCompletion ℚ) = v.valuation ℚ x

/-- **M2a OPEN record** (do NOT count closed). -/
def S3137M2aClosureInFlightRecord : Obligation :=
  { id := "INDEX.R1.M2.base-q-transport"
    source := "IUT I, Example 3.2, (iv); IUT III, Definition 3.8, (i), p. 112; Mathlib AdicValuation.lean:950"
    status := VerificationStatus.pending
    note := "M2a OPEN — CLOSURE IN FLIGHT. Bridge candidate: Mathlib IsDedekindDomain.HeightOneSpectrum.valuedAdicCompletion_eq_valuation' (AdicValuation.lean:950), with WithVal-vs-Coe presentation caveat (our elaboration of S3137ValuedCoeRatStatement from it was EXIT=1; not asserted). qpilot's S3133M2aClosedActual is NOT citable yet (147613/2578 was doc-only; current version EXIT=1). Green lattice tools S3137M2aToolActual cited in the closure attempt. R1 = M1 + M2a + M2b until qpilot's non-doc EXIT0 + probe."
    dependsOn := ["S3137M2aToolActual", "R1.M2M3M5.sameC-q-theta-readout"] }

end LeanFormal.IUT.XiFPaper.S3137M2aBridgeMissingActual

#check LeanFormal.IUT.XiFPaper.S3137M2aBridgeMissingActual.S3137ValuedCoeRatStatement
#check LeanFormal.IUT.XiFPaper.S3137M2aBridgeMissingActual.S3137M2aClosureInFlightRecord