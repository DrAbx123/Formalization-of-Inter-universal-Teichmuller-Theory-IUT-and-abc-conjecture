import tmp.sheaf.xif.paper.NativeTateQSquaresIntegralityActual
import LeanFormal.IUT.Foundations.Geometry.LocalReduction

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

/-!
# Basic q-series integrality API at an adic completion

For a general q with valuation less than one, this file proves the
foundational membership lemmas used by the q-series integrality route:
q and all its powers lie in the adic completion integers. The closedness of
the integer subring is recorded as the closure input for the limiting step.
-/

noncomputable section

namespace LeanFormal.IUT.XiFPaper.NativeTateQSquaresBasicIntegrality

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open IsDedekindDomain.HeightOneSpectrum

universe u

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable (b : Bad (LeanFormal.IUT.N8Closure.nativePlaceSelection T))

noncomputable abbrev localPrime :
    IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers T.arithmetic.F) :=
  NumberFieldFinitePlace.underlyingPrime ((nativeBadLift T).lift b)

noncomputable abbrev localField : Type :=
  (localPrime (l := l) T b).adicCompletion T.arithmetic.F

noncomputable abbrev localRing :
    ValuationSubring (localField (l := l) T b) :=
  (localPrime (l := l) T b).adicCompletionIntegers T.arithmetic.F

noncomputable abbrev tateParameter :
    NumberFieldFinitePlace.FinitePlaceQCandidate ((nativeBadLift T).lift b) :=
  (nativeBadTateWitness T (nativeBadLift T) b).parameter

/-- q with valuation at most one lies in the completion integers. -/
theorem q_mem_adicIntegers
    (hq : Valued.v (tateParameter (l := l) T b).q ≤ 1) :
    (tateParameter (l := l) T b).q ∈ localRing (l := l) T b := by
  exact (mem_adicCompletionIntegers
    (R := NumberField.RingOfIntegers T.arithmetic.F)
    (K := T.arithmetic.F)
    (v := localPrime (l := l) T b)).mpr hq

/-- All powers of q lie in the completion integers. -/
theorem q_pow_mem_adicIntegers
    (hq : Valued.v (tateParameter (l := l) T b).q ≤ 1) (n : ℕ) :
    (tateParameter (l := l) T b).q ^ n ∈ localRing (l := l) T b := by
  induction n with
  | zero =>
      simpa using (localRing (l := l) T b).one_mem
  | succ n ih =>
      rw [pow_succ]
      exact ValuationSubring.mul_mem (localRing (l := l) T b)
        ((tateParameter (l := l) T b).q ^ n)
        ((tateParameter (l := l) T b).q) ih
        (q_mem_adicIntegers (l := l) T b hq)

/-- The adic completion integer subring is closed in the completion. -/
theorem localRing_isClosed :
    IsClosed ((localRing (l := l) T b : Set (localField (l := l) T b))) := by
  have h : ((localRing (l := l) T b : Set (localField (l := l) T b))) =
      ((Valued.v.integer : Subring (localField (l := l) T b)) :
        Set (localField (l := l) T b)) := rfl
  rw [h]
  exact Valued.isClosed_integer (R := localField (l := l) T b)

/-- If a sequence in a closed subring converges, its limit is in the subring. -/
theorem closedSubring_limit_mem
    {S : Set (localField (l := l) T b)} (hS : IsClosed S)
    {f : ℕ → S} {x : localField (l := l) T b}
    (hf : Filter.Tendsto (fun n => (f n : localField (l := l) T b))
      Filter.atTop (nhds x)) :
    x ∈ S :=
  hS.mem_of_tendsto hf (Filter.Eventually.of_forall fun n => (f n).2)

/-- A convergent series of elements of the closed integer subring has its
limit in the subring. -/
theorem localRing_tsum_mem
    {f : ℕ → localRing (l := l) T b}
    {x : localField (l := l) T b}
    (hsum : Filter.Tendsto
      (fun N : ℕ => (Finset.range N).sum
        (fun n => ((f n : localRing (l := l) T b) : localField (l := l) T b)))
      Filter.atTop (nhds x)) :
    x ∈ localRing (l := l) T b := by
  let g : ℕ → localRing (l := l) T b := fun N =>
    ⟨(Finset.range N).sum
      (fun n => ((f n : localRing (l := l) T b) : localField (l := l) T b)),
      (localRing (l := l) T b).sum_mem (fun n _ => (f n).2)⟩
  exact closedSubring_limit_mem (l := l) T b
    (localRing_isClosed (l := l) T b) (f := g) (by
      simpa [g] using hsum)

end LeanFormal.IUT.XiFPaper.NativeTateQSquaresBasicIntegrality

end
