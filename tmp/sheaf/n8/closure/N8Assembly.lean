import tmp.sheaf.n8.closure.TargetSignature
import tmp.sheaf.n8.closure.SourceInputBinding
import tmp.sheaf.n8.closure.SourceLogKummerRealization
import tmp.sheaf.n8.closure.SourcePilotRegion
import tmp.sheaf.n8.closure.SourceWitnessedOutput
import tmp.sheaf.n8.closure.SourceAlgorithmCompatibility
import tmp.sheaf.n8.closure.PaperNormalizedVolume
import tmp.sheaf.n8.closure.SourceHolomorphicHull
import tmp.sheaf.n8.closure.SourceDegreeComparison
import tmp.sheaf.n8.closure.SourcePilotApproximation

set_option checkBinderAnnotations false

/-!
# N8 C10 closure

Assembles the actual C1-C9 stage-2 data into N8FullOutput. The C0 output is
used only for the base field; the C1-C9 data and C6/C6Prod are explicit
parameters. No free ipl/she/apt/q_le_hull/possibleImage field and no
total-goal sorry is introduced.
-/

noncomputable section

namespace LeanFormal.IUT.N8Closure.Assembly

universe ua uv upi umon ui u v w uL uG uι uK

open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.N8Closure.TargetSignature
open LeanFormal.IUT.N8Closure.SourceInputBinding
open LeanFormal.IUT.N8Closure.SourceLogKummerRealization
open LeanFormal.IUT.N8Closure.SourcePilotRegion
open ABCBridge.N8.C4Actual
open LeanFormal.IUT.N8Closure.SourceAlgorithmCompatibility
open LeanFormal.IUT.N8C6.PaperNormalizedVolume
open ABCBridge.N8.C7Actual
open LeanFormal.IUT.N8Closure.C8
open LeanFormal.IUT.N8Closure.C9
open MeasureTheory
open LeanFormal.IUT.NumberFieldFinitePlace

variable {l : PrimeGeFive} {V : Type uv} {Label : Type u} {Choice : Type v}
  [AddGroup Label] [Preorder Choice]
  {LAdd : Type uG} [AddGroup LAdd] [Group (Multiplicative LAdd)]
  {K : Type uK} [Field K] [NumberField K] {p : Nat} [Fact p.Prime]
  {ι : Type uι} [Fintype ι] {W : ι → Type w}
  (places : (i : ι) → W i → FinitePlaceAtPrime K p)
  (tuple : (i : ι) → W i)
  [MeasurableSpace (ArithmeticTensorTupleBlock places tuple)]
  [BorelSpace (ArithmeticTensorTupleBlock places tuple)]
  (mu : Measure (ArithmeticTensorTupleBlock places tuple))
  [Measure.IsAddHaarMeasure mu]

/-- Full C10 output: base C0 output plus actual C1-C9 data and the C6/C6Prod
and C7 family consumed by C8/C9. -/
structure N8FullOutput
    (I : N8TargetInput l V Label Choice)
    (C1 : SourceInputBinding I.I)
    (C2 : SourceLogKummerData I.I C1)
    (C3 : SourcePilotRegionData I.I)
    (C4 : SourceWitnessedOutputData (l := l) (V := V) I.I (Multiplicative LAdd))
    (C5 : SourceAlgorithmCompatibilityData I.I C1 C2 C3 C4)
    (C6 : PaperNormalizedVolumeData places tuple mu)
    (C6Prod : C6ProductVolumeData (Y := I.I.ThetaPilotPoint C4.place.v))
    (C5Perm : C5PermittedFamilyData (l := l))
    (C7 : ∀ (n : ThetaPilotCarrier l) (x : I.I.ThetaPilotPoint C4.place.v),
      SourceHolomorphicHullData C4 C5Perm C6Prod n x)
    (Theta Q : Real) where
  /-- C0 base output. -/
  base : N8TargetOutput I
  /-- C1 actual source binding. -/
  fieldC1 : SourceInputBinding I.I
  /-- C2 actual local log-Kummer data. -/
  fieldC2 : SourceLogKummerData I.I fieldC1
  /-- C3 actual source pilot region. -/
  fieldC3 : SourcePilotRegionData I.I
  /-- C4 actual witnessed output. -/
  fieldC4 : SourceWitnessedOutputData (l := l) (V := V) I.I (Multiplicative LAdd)
  /-- C5 actual algorithm compatibility. -/
  fieldC5 : SourceAlgorithmCompatibilityData I.I fieldC1 fieldC2 fieldC3 fieldC4
  /-- C6 actual normalized volume data. -/
  fieldC6 : PaperNormalizedVolumeData places tuple mu
  /-- C6 product/volume handoff. -/
  fieldC6Prod : C6ProductVolumeData (Y := I.I.ThetaPilotPoint fieldC4.place.v)
  /-- C5 permitted family handoff consumed by C7. -/
  fieldC5Perm : C5PermittedFamilyData (l := l)
  /-- C7 common hull family. -/
  fieldC7 : ∀ (n : ThetaPilotCarrier l) (x : I.I.ThetaPilotPoint fieldC4.place.v),
    SourceHolomorphicHullData fieldC4 fieldC5Perm fieldC6Prod n x
  /-- C8 degree/log-volume comparison for every n,x. -/
  fieldC8 : ∀ (n : ThetaPilotCarrier l) (x : I.I.ThetaPilotPoint fieldC4.place.v),
    c8RelativeDetDegree (V := W) (places := places) (tuple := tuple) fieldC6 =
      c8HullLogVolume (V := W) (places := places) (tuple := tuple)
        (n := n) (x := x) fieldC6 fieldC6Prod (fieldC7 n x)
  /-- C9 boundedness and q-approximation for Theta/Q. -/
  fieldC9 :
    actual_values_bounded (D := fieldC4) (C5 := fieldC5Perm)
        (C6 := fieldC6) (C6Prod := fieldC6Prod) fieldC7 Theta ∧
      actual_q_approximated (D := fieldC4) (C5 := fieldC5Perm)
        (C6 := fieldC6) (C6Prod := fieldC6Prod) fieldC7 Q

/-- C10 closure theorem: explicit C1-C9/C6/C6Prod parameters produce an actual
N8FullOutput. The C0 output is used only for the base field; the C8/C9 fields
are actual theorem applications, not free conclusions. -/
theorem n8Assembly_closure
    (I : OriginalInput.{ua, uv, upi, umon, ui} l V)
    (C1 : SourceInputBinding I)
    (C2 : SourceLogKummerData I C1)
    (C3 : SourcePilotRegionData I)
    (C4 : SourceWitnessedOutputData (l := l) (V := V) I (Multiplicative LAdd))
    (C5 : SourceAlgorithmCompatibilityData I C1 C2 C3 C4)
    (C6 : PaperNormalizedVolumeData places tuple mu)
    (C6Prod : C6ProductVolumeData (Y := I.ThetaPilotPoint C4.place.v))
    (C5Perm : C5PermittedFamilyData (l := l))
    (C7 : ∀ (n : ThetaPilotCarrier l) (x : I.ThetaPilotPoint C4.place.v),
      SourceHolomorphicHullData C4 C5Perm C6Prod n x)
    (Theta Q : Real) :
    Nonempty (N8FullOutput (places := places) (tuple := tuple) (mu := mu)
      (l := l) (V := V) (Label := Label) (Choice := Choice) (LAdd := LAdd)
      ⟨I⟩ C1 C2 C3 C4 C5 C6 C6Prod C5Perm C7 Theta Q) := by
  let I0 : N8TargetInput l V Label Choice := ⟨I⟩
  let base : N8TargetOutput I0 :=
    Classical.choice (n8_targetOutput_nonempty (l := l) (V := V)
      (Label := Label) (Choice := Choice) I0)
  exact ⟨{
    base := base
    fieldC1 := C1
    fieldC2 := C2
    fieldC3 := C3
    fieldC4 := C4
    fieldC5 := C5
    fieldC6 := C6
    fieldC6Prod := C6Prod
    fieldC5Perm := C5Perm
    fieldC7 := C7
    fieldC8 := fun n x => sourceDegreeComparison (D := C4) (C5 := C5Perm)
      (C6Prod := C6Prod) (n := n) (x := x) C6
    fieldC9 := sourcePilotApproximation_stage2 (D := C4) (C5 := C5Perm)
      (C6 := C6) (C6Prod := C6Prod) (C7 := C7) Theta Q
  }⟩

end LeanFormal.IUT.N8Closure.Assembly
