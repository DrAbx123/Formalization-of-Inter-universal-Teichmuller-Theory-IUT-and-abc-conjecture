import tmp.sheaf.n8.closure.P6SHEIndActualAttempt

noncomputable section

namespace LeanFormal.IUT.N8Closure.P6IndInvarianceAttempt

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
open ABCBridge.N8.C4Actual

variable {l : PrimeGeFive} {V : Type uv}
variable (I : OriginalInput.{ua, uv, upi, umon, ui} l V)
variable {LAdd : Type uG} [AddGroup LAdd]
variable (C4 : SourceWitnessedOutputData (l := l) (V := V) I (Multiplicative LAdd))

/-! ## Exact invariance obligations

The C4 record supplies the actions `C4.ind.ind1`/`ind2` and the region `C4.U`
as independent fields: `ind` has no law relating its permutations to the
`eval`/`Choice` range defining `U`.  The following structure records exactly
the two invariance obligations, without adding a fake compatible action. -/

structure P6IndInvarianceData
    (C4 : SourceWitnessedOutputData (l := l) (V := V) I (Multiplicative LAdd)) where
  ind1_invariance : ∀ (g : Multiplicative LAdd) (n : ThetaPilotCarrier l)
    (x : I.ThetaPilotPoint C4.place.v),
      C4.ind.ind1 g '' C4.U n x = C4.U n x
  ind2_invariance : ∀ (g : Multiplicative LAdd) (n : ThetaPilotCarrier l)
    (x : I.ThetaPilotPoint C4.place.v),
      C4.ind.ind2 g '' C4.U n x = C4.U n x

/-- Exact decomposition: the invariance slice is inhabited iff the two
pointwise invariance statements hold. -/
theorem P6IndInvarianceData_nonempty_iff :
    Nonempty (P6IndInvarianceData (l := l) (V := V) I C4) ↔
      (∀ (g : Multiplicative LAdd) (n : ThetaPilotCarrier l)
        (x : I.ThetaPilotPoint C4.place.v),
          C4.ind.ind1 g '' C4.U n x = C4.U n x) ∧
        (∀ (g : Multiplicative LAdd) (n : ThetaPilotCarrier l)
          (x : I.ThetaPilotPoint C4.place.v),
            C4.ind.ind2 g '' C4.U n x = C4.U n x) := by
  constructor
  · rintro ⟨D⟩
    exact ⟨D.ind1_invariance, D.ind2_invariance⟩
  · rintro ⟨h1, h2⟩
    exact ⟨{ ind1_invariance := h1, ind2_invariance := h2 }⟩

/-- Conditional construction from the two pointwise invariance proofs. -/
theorem P6IndInvarianceData_of_actual
    (h1 : ∀ (g : Multiplicative LAdd) (n : ThetaPilotCarrier l)
      (x : I.ThetaPilotPoint C4.place.v),
        C4.ind.ind1 g '' C4.U n x = C4.U n x)
    (h2 : ∀ (g : Multiplicative LAdd) (n : ThetaPilotCarrier l)
      (x : I.ThetaPilotPoint C4.place.v),
        C4.ind.ind2 g '' C4.U n x = C4.U n x) :
    Nonempty (P6IndInvarianceData (l := l) (V := V) I C4) :=
  ⟨{ ind1_invariance := h1, ind2_invariance := h2 }⟩

/-! ## Named invariance gap

This is not derivable from the actual `C4.ind` actions alone: `IndActionData`
contains no evaluation/Choice compatibility field, and `U` is the range of
`eval` built from `place`/`pilot`, not from `ind`.  The named theorem records
the exact remaining construction obligation. -/

theorem p6IndInvarianceData_constructionGap :
    Nonempty (P6IndInvarianceData (l := l) (V := V) I C4) := by
  sorry

end LeanFormal.IUT.N8Closure.P6IndInvarianceAttempt
