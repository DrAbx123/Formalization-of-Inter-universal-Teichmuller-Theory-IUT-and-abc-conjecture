import tmp.sheaf.n8.closure.P6SHEInd
import tmp.sheaf.n8.closure.C5SHEIntegration

noncomputable section

namespace LeanFormal.IUT.N8Closure.P6SHEIndActualAttempt

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
open ABCBridge.N8.C4Actual

variable {l : PrimeGeFive} {V : Type uv}
variable (I : OriginalInput.{ua, uv, upi, umon, ui} l V)
variable {LAdd : Type uG} [AddGroup LAdd]
variable (C4 : SourceWitnessedOutputData (l := l) (V := V) I (Multiplicative LAdd))

/-! ## Actual Ind actions and Ind3 upper bound -/

structure P6IndActionsData
    (C4 : SourceWitnessedOutputData (l := l) (V := V) I (Multiplicative LAdd)) where
  ind1 : Multiplicative LAdd →* Equiv.Perm (I.ThetaPilotPoint C4.place.v)
  ind2 : Multiplicative LAdd →* Equiv.Perm (I.ThetaPilotPoint C4.place.v)
  ind3 : Nat → Set (I.ThetaPilotPoint C4.place.v) →
    Set (I.ThetaPilotPoint C4.place.v)
  ind3_upper_bound : ∀ (n : Nat) (S : Set (I.ThetaPilotPoint C4.place.v)),
    S ⊆ ind3 n S

noncomputable def p6IndActionsData : P6IndActionsData (l := l) (V := V) I C4 where
  ind1 := C4.ind.ind1
  ind2 := C4.ind.ind2
  ind3 := C4.ind.ind3_nonarch
  ind3_upper_bound := C4.ind.ind3_nonarch_inclusion

/-! ## Exact decomposition of P6IndData -/

theorem P6IndData_nonempty_iff :
    Nonempty (P6IndData (l := l) (V := V) I C4) ↔
      ∃ A : P6IndActionsData (l := l) (V := V) I C4,
        (∀ (g : Multiplicative LAdd) (n : ThetaPilotCarrier l)
          (x : I.ThetaPilotPoint C4.place.v),
            A.ind1 g '' C4.U n x = C4.U n x) ∧
          (∀ (g : Multiplicative LAdd) (n : ThetaPilotCarrier l)
            (x : I.ThetaPilotPoint C4.place.v),
              A.ind2 g '' C4.U n x = C4.U n x) := by
  constructor
  · rintro ⟨D⟩
    exact ⟨{ ind1 := D.ind1, ind2 := D.ind2, ind3 := D.ind3, ind3_upper_bound := D.ind3_upper_bound }, D.ind1_invariance, D.ind2_invariance⟩
  · rintro ⟨A, h1, h2⟩
    exact ⟨{ ind1 := A.ind1, ind2 := A.ind2, ind3 := A.ind3, ind1_invariance := h1, ind2_invariance := h2, ind3_upper_bound := A.ind3_upper_bound }⟩

/-- Conditional construction from actual actions plus the two invariance
responsibilities; this is not an inhabitant by itself. -/
theorem P6IndData_of_actual
    (A : P6IndActionsData (l := l) (V := V) I C4)
    (h1 : ∀ (g : Multiplicative LAdd) (n : ThetaPilotCarrier l)
      (x : I.ThetaPilotPoint C4.place.v), A.ind1 g '' C4.U n x = C4.U n x)
    (h2 : ∀ (g : Multiplicative LAdd) (n : ThetaPilotCarrier l)
      (x : I.ThetaPilotPoint C4.place.v), A.ind2 g '' C4.U n x = C4.U n x) :
    Nonempty (P6IndData (l := l) (V := V) I C4) :=
  ⟨{ ind1 := A.ind1, ind2 := A.ind2, ind3 := A.ind3, ind1_invariance := h1, ind2_invariance := h2, ind3_upper_bound := A.ind3_upper_bound }⟩

end LeanFormal.IUT.N8Closure.P6SHEIndActualAttempt
