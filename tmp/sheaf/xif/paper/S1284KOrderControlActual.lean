import tmp.sheaf.xif.paper.S467KrootOrderControlAuditActual
import tmp.sheaf.xif.paper.S472TorsionKInputAuditActual
/-! # S1284: K-side order control, exact reduction
The actual factorization order_K = e * order_F and gcd(order_F,l)=1 give
  (2l) | order_K  <->  l | e  and  2 | order_K.
The two right-hand conditions are exactly the unproved source inputs
(l-divisibility of local ramification and q-order parity). -/
noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
namespace LeanFormal.IUT.XiFPaper.S1284KOrderControlActual
open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.QPilotZeroLocusDivisorActual
open LeanFormal.IUT.XiFPaper.S438QVFamilyKSideCandidateActual
open LeanFormal.IUT.XiFPaper.S467KrootOrderControlAuditActual
open LeanFormal.IUT.XiFPaper.S472TorsionKInputAuditActual
universe u
variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable (b : Bad (nativePlaceSelection T))
theorem twoL_dvd_order_K_iff_ramification_and_two :
    (2 * l.value) ∣ (qVFamilyK T b).order ↔
      l.value ∣ qVFamilyKRamificationIdx T b ∧
        2 ∣ (qVFamilyK T b).order := by
  constructor
  · intro h
    exact ⟨twoL_dvd_order_K_requires_ramification (l := l) T b h,
      dvd_trans (show 2 ∣ 2 * l.value from ⟨l.value, by ring⟩) h⟩
  · rintro ⟨⟨k, hk⟩, h2⟩
    rw [qVFamilyK_order_factorization, hk]
    have h2' : 2 ∣ l.value * (k * (qVFamily T b).order) := by
      have h := h2
      rwa [qVFamilyK_order_factorization, hk, mul_assoc] at h
    have hodd : Odd l.value :=
      l.prime.odd_of_ne_two (by intro h2l; have := l.ge_five; omega)
    have hcop : Nat.Coprime 2 l.value := (Nat.coprime_two_left).mpr hodd
    have h2km : 2 ∣ k * (qVFamily T b).order := by
      exact hcop.dvd_of_dvd_mul_left (by simpa [mul_assoc] using h2')
    rcases h2km with ⟨t, ht⟩
    refine ⟨t, ?_⟩
    calc
      l.value * k * (qVFamily T b).order
          = l.value * (k * (qVFamily T b).order) := by ring
      _ = l.value * (2 * t) := by rw [ht]
      _ = 2 * l.value * t := by ring
end LeanFormal.IUT.XiFPaper.S1284KOrderControlActual
