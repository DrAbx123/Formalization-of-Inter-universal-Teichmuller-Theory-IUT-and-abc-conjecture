import tmp.sheaf.n8.closure.P6IndInvarianceAttempt

noncomputable section

namespace LeanFormal.IUT.N8Closure.P6IndCompatibilityAttempt

universe ua uv upi umon ui uG

open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.N8Closure.SourceInputBinding
open LeanFormal.IUT.N8Closure.SourceLogKummerRealization
open LeanFormal.IUT.N8Closure.SourcePilotRegion
open LeanFormal.IUT.N8Closure.IPLFamily
open LeanFormal.IUT.N8Closure.SourceAlgorithmCompatibility
open LeanFormal.IUT.N8Closure.C5Native
open LeanFormal.IUT.N8Closure.C5DonorProof
open LeanFormal.IUT.N8Closure.C5SHEIntegration
open LeanFormal.IUT.N8Closure.C5APTProof
open LeanFormal.IUT.N8Closure.P6SHEInd
open LeanFormal.IUT.N8Closure.P6SHEIndActualAttempt
open LeanFormal.IUT.N8Closure.P6IndInvarianceAttempt
open ABCBridge.N8.C4Actual

variable {l : PrimeGeFive} {V : Type uv}
variable (I : OriginalInput.{ua, uv, upi, umon, ui} l V)
variable {LAdd : Type uG} [AddGroup LAdd]
variable (C4 : SourceWitnessedOutputData (l := l) (V := V) I (Multiplicative LAdd))

/-! ## Eval/Choice compatibility law -/

/-- A natural action compatibility law relating an Ind action to the actual
`eval`/`Choice` structure: every action image of an evaluated choice is again
an evaluated choice.  This is a source law, not an arbitrary invariant set. -/
def EvalCompatibility
    (action : Multiplicative LAdd →* Equiv.Perm (I.ThetaPilotPoint C4.place.v)) : Prop :=
  ∀ (g : Multiplicative LAdd) (n : ThetaPilotCarrier l)
    (x : I.ThetaPilotPoint C4.place.v) (c : C4.Choice n x),
      ∃ c' : C4.Choice n x,
        action g (C4.eval n x c) = C4.eval n x c'

/-- The compatibility law implies invariance of the eval range `C4.U`. -/
theorem invariance_of_evalCompatibility
    (action : Multiplicative LAdd →* Equiv.Perm (I.ThetaPilotPoint C4.place.v))
    (h : EvalCompatibility (l := l) (V := V) I C4 action)
    (g : Multiplicative LAdd) (n : ThetaPilotCarrier l)
    (x : I.ThetaPilotPoint C4.place.v) :
    action g '' C4.U n x = C4.U n x := by
  ext y; constructor
  · rintro ⟨z, hz, rfl⟩
    rcases hz with ⟨c, rfl⟩
    rcases h g n x c with ⟨c', hc'⟩
    exact ⟨c', hc'.symm⟩
  · intro hy
    rcases hy with ⟨c, hc⟩
    rcases h g⁻¹ n x c with ⟨c', hc'⟩
    refine ⟨C4.eval n x c', ⟨c', rfl⟩, ?_⟩
    rw [← hc']
    rw [show action g⁻¹ = (action g)⁻¹ from map_inv action g]
    rw [← Equiv.Perm.mul_apply]
    rw [mul_inv_cancel]
    exact hc

/-- Conditional construction of the invariance slice from the compatibility law. -/
theorem P6IndInvarianceData_of_compat
    (h1 : EvalCompatibility (l := l) (V := V) I C4 C4.ind.ind1)
    (h2 : EvalCompatibility (l := l) (V := V) I C4 C4.ind.ind2) :
    Nonempty (P6IndInvarianceData (l := l) (V := V) I C4) :=
  ⟨{ ind1_invariance := fun g n x =>
        invariance_of_evalCompatibility (l := l) (V := V) I C4 C4.ind.ind1 h1 g n x,
      ind2_invariance := fun g n x =>
        invariance_of_evalCompatibility (l := l) (V := V) I C4 C4.ind.ind2 h2 g n x }⟩

end LeanFormal.IUT.N8Closure.P6IndCompatibilityAttempt
