import Mathlib.MeasureTheory.Group.FundamentalDomain
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed
import tmp.sheaf.xif.paper.S355OrbifoldRootStackCandidateActual
/-! # S769: stacky 1/(2l) normalization from a fundamental domain
The measure-theoretic part is Mathlib's
`IsFundamentalDomain.measure_eq_card_smul_of_smul_ae_eq_self`: an invariant
set has card(G) times the measure of its intersection with a fundamental
domain.  The root log part is Mathlib's log_pow.  The identification with
`paperRootThetaHullLog` is recorded as an exact gap, not asserted. -/
noncomputable section
open scoped BigOperators
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000
namespace LeanFormal.IUT.XiFPaper.S769StackyLogVolumeNormalizationActual
open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.S355OrbifoldRootStackCandidateActual
open LeanFormal.IUT.XiFPaper.QPilotZeroLocusDivisorActual
open MeasureTheory
universe u
variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable (b : Bad (nativePlaceSelection T))
/-- The mu_{2l} group has cardinal 2l in the algebraic closure. -/
theorem stackyMuCard :
    Nat.card (rootsOfUnity (2 * l.value) (AC T b)) = 2 * l.value := by
  haveI : NeZero (2 * l.value) := ⟨Nat.ne_of_gt (n_pos (l := l))⟩
  exact natCard_rootsOfUnity (AC T b) (2 * l.value)
/-- Root log normalization: if r^n = q for positive reals, then
log r = (1/n) log q. -/
theorem stackyRootLog_eq_inv_card_mul
    {q r : Real} (hq : 0 < q) (hr : 0 < r) {n : Nat} (hn : 0 < n)
    (h : r ^ n = q) :
    Real.log r = (n : Real)⁻¹ * Real.log q := by
  rw [← h, Real.log_pow]
  field_simp
/-- Measure of a G-invariant set is card(G) times the measure of its
fundamental-domain piece. -/
theorem stackyMeasure_eq_card_smul
    {G X : Type*} [Group G] [Finite G] [MulAction G X] [MeasurableSpace X]
    (mu : Measure X) {s t : Set X}
    (hs : IsFundamentalDomain G s mu)
    (ht : ∀ g : G, (g • t : Set X) =ᵐ[mu] t) :
    mu t = Nat.card G • mu (t ∩ s) :=
  hs.measure_eq_card_smul_of_smul_ae_eq_self t ht
/-- Stacky log-volume of an invariant region, normalized by card(G). -/
noncomputable def stackyLogVolume
    {G X : Type*} [Group G] [Finite G] [MulAction G X] [MeasurableSpace X]
    (mu : Measure X) (t : Set X) : Real :=
  Real.log ((mu t).toReal / (Nat.card G : Real))
/-- The normalized stacky log-volume is the log of the fundamental-domain
measure, from the exact measure identity. -/
theorem stackyLogVolume_eq_fundamental
    {G X : Type*} [Group G] [Finite G] [MulAction G X] [MeasurableSpace X]
    (mu : Measure X) {s t : Set X}
    (hs : IsFundamentalDomain G s mu)
    (ht : ∀ g : G, (g • t : Set X) =ᵐ[mu] t) :
    stackyLogVolume mu t = Real.log ((mu (t ∩ s)).toReal) := by
  have hcard : (Nat.card G : Real) ≠ 0 := by
    haveI : Nonempty G := ⟨1⟩
    exact_mod_cast Nat.card_ne_zero.mpr ⟨1⟩
  have h := stackyMeasure_eq_card_smul mu hs ht
  unfold stackyLogVolume
  rw [h, ENNReal.toReal_nsmul]
  field_simp [hcard]
/-- Exact paper identification gap: the stacky log-volume is not identified
with `paperRootThetaHullLog` by the measure theory above. -/
def PaperRootThetaHullStackyGap
    (mu : Measure (CandidateRoots T b)) (t : Set (CandidateRoots T b))
    (paperRootLog : Real) : Prop :=
  stackyLogVolume mu t = paperRootLog
end LeanFormal.IUT.XiFPaper.S769StackyLogVolumeNormalizationActual
