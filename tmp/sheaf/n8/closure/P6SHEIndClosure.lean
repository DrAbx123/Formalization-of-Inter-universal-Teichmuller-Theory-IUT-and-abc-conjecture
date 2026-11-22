import tmp.sheaf.n8.closure.P6SHEInd

noncomputable section

namespace LeanFormal.IUT.N8Closure.P6SHEIndClosure

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
variable (C1 : SourceInputBinding I)
variable (C2 : SourceLogKummerData I C1)
variable (C3 : SourcePilotRegionData (l := l) (V := V) I)
variable {LAdd : Type uG} [AddGroup LAdd]
variable (C4 : SourceWitnessedOutputData (l := l) (V := V) I (Multiplicative LAdd))

/-! ## P6 source closure type layer

The closure type contains the actual SHE square and the Ind1/2/3 data as the
core, and keeps the APT/permitted missing data as explicit fields.  It is
inhabited exactly when the APT and permitted gaps are supplied. -/

structure P6SourceClosureCore
    (I : OriginalInput.{ua, uv, upi, umon, ui} l V)
    (C4 : SourceWitnessedOutputData (l := l) (V := V) I (Multiplicative LAdd)) where
  sheInd : P6SHEIndData I C4

structure P6SourceClosure
    (I : OriginalInput.{ua, uv, upi, umon, ui} l V)
    (C1 : SourceInputBinding I) (C2 : SourceLogKummerData I C1)
    (C3 : SourcePilotRegionData (l := l) (V := V) I)
    {LAdd : Type uG} [AddGroup LAdd]
    (C4 : SourceWitnessedOutputData (l := l) (V := V) I (Multiplicative LAdd)) where
  sheInd : P6SHEIndData I C4
  /-- Exact APT missing data; semantic field, not a free Prop. -/
  aptData : NativeAPTMissing (l := l) (V := V) I (LAdd := LAdd) C4
  /-- Exact permitted-family missing data; semantic field. -/
  permittedData : NativePermittedActual l

noncomputable def p6SourceClosureCore :
    P6SourceClosureCore I C4 where
  sheInd := p6SHEIndSlice (l := l) (V := V) I C4

theorem p6SourceClosureCore_nonempty :
    Nonempty (P6SourceClosureCore I C4) :=
  ⟨p6SourceClosureCore (l := l) (V := V) I C4⟩

/-! ## Responsibilities exposed from the type layer -/

theorem p6SourceClosure_ind1_invariance (D : P6SourceClosure I C1 C2 C3 C4)
    (g : Multiplicative LAdd) (n : ThetaPilotCarrier l)
    (x : I.ThetaPilotPoint C4.place.v) :
    D.sheInd.indData.ind1 g '' C4.U n x = C4.U n x :=
  D.sheInd.indData.ind1_invariance g n x

theorem p6SourceClosure_ind2_invariance (D : P6SourceClosure I C1 C2 C3 C4)
    (g : Multiplicative LAdd) (n : ThetaPilotCarrier l)
    (x : I.ThetaPilotPoint C4.place.v) :
    D.sheInd.indData.ind2 g '' C4.U n x = C4.U n x :=
  D.sheInd.indData.ind2_invariance g n x

theorem p6SourceClosure_ind3_upper_bound (D : P6SourceClosure I C1 C2 C3 C4)
    (n : Nat) (S : Set (I.ThetaPilotPoint C4.place.v)) :
    S ⊆ D.sheInd.indData.ind3 n S :=
  D.sheInd.indData.ind3_upper_bound n S

/-- Exact gap semantics: the full closure is inhabited exactly when the
P6 SHE/Ind core, the APT missing data, and the permitted missing data are all
supplied. -/
theorem p6SourceClosure_nonempty_iff :
    Nonempty (P6SourceClosure I C1 C2 C3 C4) ↔
      Nonempty (P6SHEIndData I C4) ∧
        Nonempty (NativeAPTMissing (l := l) (V := V) I (LAdd := LAdd) C4) ∧
          Nonempty (NativePermittedActual l) := by
  constructor
  · rintro ⟨D⟩
    exact ⟨⟨D.sheInd⟩, ⟨D.aptData⟩, ⟨D.permittedData⟩⟩
  · rintro ⟨⟨sheInd⟩, ⟨aptData⟩, ⟨permittedData⟩⟩
    exact ⟨{ sheInd := sheInd, aptData := aptData, permittedData := permittedData }⟩

end LeanFormal.IUT.N8Closure.P6SHEIndClosure
