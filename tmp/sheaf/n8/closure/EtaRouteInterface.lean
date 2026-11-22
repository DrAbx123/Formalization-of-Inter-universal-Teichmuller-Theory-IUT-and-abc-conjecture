import tmp.sheaf.n8.closure.C2Native
import tmp.sheaf.n8.closure.C9QPilotRegion
import LeanFormal.IUT.IUTII.Kummer.SourceLogShellCarrier

/-!
# Eta route interface (ETA-1)

Exact interface based on the production log-shell API and native q.

For the native log-shell datum D := C2Native.nativeLocalShell X:

- Rval := D.preLogShell
- Rss  := D.logShell
- EtaQ : Rval -> Rss is the actual scaling a |-> (p*_v)^{-1} * a
- EtaAnab : Rss -> Rval is the actual inverse scaling b |-> p*_v * b
- EtaComparison := LeftInverse EtaAnab EtaQ, RightInverse, and native q < 0.

The maps are derived from the production pStar and logShell equality; no free
Real or arbitrary map is introduced.  All interface fields are actual; no named
gap is needed.  Native q enters through qPilotSignedLog_neg.
-/

noncomputable section

namespace LeanFormal.IUT.N8Closure.EtaRouteInterface

open LeanFormal.IUT
open LeanFormal.IUT.N8Closure.NativeInput
open LeanFormal.IUT.N8Closure.C2Native
open LeanFormal.IUT.N8Closure.C9QPilotRegion

universe u

variable {l : PrimeGeFive} (X : N8NativeInput l)

/-- The actual native log-shell datum at the bad finite base place. -/
abbrev NativeShell (X : N8NativeInput l) :=
  nativeLocalShell X

/-- Rval: actual pre-log-shell (log-valuation side). -/
abbrev Rval (X : N8NativeInput l) : Set (NativeShell X).K :=
  (NativeShell X).preLogShell

/-- Rss: actual log-shell (subquotient side). -/
abbrev Rss (X : N8NativeInput l) : Set (NativeShell X).K :=
  (NativeShell X).logShell

/-- EtaQ: actual map Rval -> Rss, a |-> (p*_v)^{-1} a. -/
noncomputable def EtaQ (X : N8NativeInput l) : Rval X → Rss X :=
  fun a =>
    ⟨((NativeShell X).pStar : (NativeShell X).K)⁻¹ * a.1, by
      change ((NativeShell X).pStar : (NativeShell X).K)⁻¹ * a.1 ∈
        (NativeShell X).logShell
      rw [LeanFormal.IUT.SourceLogShellDatum.logShell_eq_invScaledPreLogShell]
      exact ⟨a.1, a.2, rfl⟩⟩

/-- EtaAnab: actual map Rss -> Rval, b |-> p*_v b. -/
noncomputable def EtaAnab (X : N8NativeInput l) : Rss X → Rval X :=
  fun b =>
    ⟨((NativeShell X).pStar : (NativeShell X).K) * b.1, by
      change ((NativeShell X).pStar : (NativeShell X).K) * b.1 ∈
        (NativeShell X).preLogShell
      exact b.2⟩

/-- EtaComparison: the actual maps are mutually inverse and the native q value
is negative. -/
def EtaComparison (X : N8NativeInput l) : Prop :=
  Function.LeftInverse (EtaAnab X) (EtaQ X) ∧
    Function.RightInverse (EtaAnab X) (EtaQ X) ∧
    qPilotSignedLog X < 0

/-- Actual left inverse of the Eta route maps. -/
theorem etaQ_leftInverse (X : N8NativeInput l) :
    Function.LeftInverse (EtaAnab X) (EtaQ X) := by
  intro a
  apply Subtype.ext
  change ((NativeShell X).pStar : (NativeShell X).K) * 
      (((NativeShell X).pStar : (NativeShell X).K)⁻¹ * a.1) = a.1
  rw [← mul_assoc,
    mul_inv_cancel₀ (LeanFormal.IUT.SourceLogShellDatum.pStar_ne_zero_cast (NativeShell X)),
    one_mul]

/-- Actual right inverse of the Eta route maps. -/
theorem etaQ_rightInverse (X : N8NativeInput l) :
    Function.RightInverse (EtaAnab X) (EtaQ X) := by
  intro b
  apply Subtype.ext
  change ((NativeShell X).pStar : (NativeShell X).K)⁻¹ *
      (((NativeShell X).pStar : (NativeShell X).K) * b.1) = b.1
  calc ((NativeShell X).pStar : (NativeShell X).K)⁻¹ *
        (((NativeShell X).pStar : (NativeShell X).K) * b.1)
      = ((((NativeShell X).pStar : (NativeShell X).K)⁻¹ *
          ((NativeShell X).pStar : (NativeShell X).K)) * b.1) :=
          (mul_assoc _ _ _).symm
    _ = (1 : (NativeShell X).K) * b.1 := by
          rw [inv_mul_cancel₀
            (LeanFormal.IUT.SourceLogShellDatum.pStar_ne_zero_cast (NativeShell X))]
    _ = b.1 := one_mul _

/-- EtaComparison is actual. -/
theorem etaComparison_actual (X : N8NativeInput l) : EtaComparison X :=
  ⟨etaQ_leftInverse X, etaQ_rightInverse X, qPilotSignedLog_neg X⟩

/-- Native q value used by the Eta route. -/
def EtaNativeQ (X : N8NativeInput l) : Real :=
  qPilotSignedLog X

/-- Native q is negative: the exact q-side input of EtaComparison. -/
theorem etaNativeQ_neg (X : N8NativeInput l) : EtaNativeQ X < 0 :=
  qPilotSignedLog_neg X

end LeanFormal.IUT.N8Closure.EtaRouteInterface
