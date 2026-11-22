import tmp.sheaf.n8.closure.TargetSignature
import tmp.sheaf.n8.closure.SourceWitnessedOutput
import tmp.sheaf.n8.closure.SourceAlgorithmCompatibility
import tmp.sheaf.n8.closure.SourceDegreeComparison
import tmp.sheaf.n8.closure.SourceHolomorphicHull
import tmp.sheaf.n8.closure.PaperNormalizedVolume

/-!
# N8 C9 stage 2: Values, boundedness and q-approximation

Uses the actual C0 `OriginalInput`/C4/C5/C7/C8 types.  `Values` is the range
of the actual C8 signed hull log-volume over the C4 output witnesses and the
actual C7 common hull data.  No local OriginalInput/C2/C3/C5/C8 structure is
defined here.  T4 handoff types (`C5PermittedFamilyData`, `C6ProductVolumeData`) are still the current `SourceHolomorphicHull` types; T4 has not replaced them with actual C5/C6 bridge types yet.

The only theorem-level named `sorry` is the source statement.
-/

set_option relaxedAutoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

open MeasureTheory BigOperators
open LeanFormal.IUT
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.LocalFieldProductHull
open ABCBridge.N8.C4Actual
open ABCBridge.N8.C7Actual
open LeanFormal.IUT.N8C6.PaperNormalizedVolume
open LeanFormal.IUT.N8Closure.C8

namespace LeanFormal.IUT.N8Closure.C9

universe ua uv upi umon ui uL uY uι uK u v w

variable {K : Type u} [Field K] [NumberField K] {p : ℕ} [Fact p.Prime]
  {iota : Type v} [Fintype iota] {V : iota → Type w}
  {places : (i : iota) → V i → FinitePlaceAtPrime K p}
  {tuple : (i : iota) → V i}
  [MeasurableSpace (ArithmeticTensorTupleBlock places tuple)]
  [BorelSpace (ArithmeticTensorTupleBlock places tuple)]
  {mu : Measure (ArithmeticTensorTupleBlock places tuple)}
  [Measure.IsAddHaarMeasure mu]

variable {l : PrimeGeFive} {V0 : Type uv} {Label : Type uL} [Group Label]
  {I : OriginalInput.{ua, uv, upi, umon, ui} l V0}
  {D : SourceWitnessedOutputData (l := l) (V := V0) I Label}
  {C5 : C5PermittedFamilyData (l := l)}
  {C6 : PaperNormalizedVolumeData places tuple mu}
  {C6Prod : C6ProductVolumeData (Y := I.ThetaPilotPoint D.place.v)}

variable (C7 : ∀ (n : ThetaPilotCarrier l) (x : I.ThetaPilotPoint D.place.v),
  SourceHolomorphicHullData D C5 C6Prod n x)

/-- Actual allowed output values: the range of the C8 signed hull log-volume
over the actual C4 output witness and the actual C7 common hull.  This is not
a free function, not `Set.Iic Theta`, and does not insert `Q`. -/
def Values (C6 : PaperNormalizedVolumeData places tuple mu)
    (C6Prod : C6ProductVolumeData (Y := I.ThetaPilotPoint D.place.v))
    (C7 : ∀ (n : ThetaPilotCarrier l) (x : I.ThetaPilotPoint D.place.v),
      SourceHolomorphicHullData D C5 C6Prod n x) : Set ℝ :=
  Set.range (fun p : Sigma (fun _ : ThetaPilotCarrier l =>
      I.ThetaPilotPoint D.place.v) =>
    c8HullLogVolume (n := p.1) (x := p.2) C6 C6Prod (C7 p.1 p.2))

/-- Every actual allowed output value is bounded by the theta value. -/
def actual_values_bounded (C6 : PaperNormalizedVolumeData places tuple mu)
    (C6Prod : C6ProductVolumeData (Y := I.ThetaPilotPoint D.place.v))
    (C7 : ∀ (n : ThetaPilotCarrier l) (x : I.ThetaPilotPoint D.place.v),
      SourceHolomorphicHullData D C5 C6Prod n x) (Theta : ℝ) : Prop :=
  ∀ y : ℝ, y ∈ Values C6 C6Prod C7 → y ≤ Theta

/-- The actual q-pilot value is approximated from below by actual allowed
output values. -/
def actual_q_approximated (C6 : PaperNormalizedVolumeData places tuple mu)
    (C6Prod : C6ProductVolumeData (Y := I.ThetaPilotPoint D.place.v))
    (C7 : ∀ (n : ThetaPilotCarrier l) (x : I.ThetaPilotPoint D.place.v),
      SourceHolomorphicHullData D C5 C6Prod n x) (Q : ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ y : ℝ, y ∈ Values C6 C6Prod C7 ∧ Q - ε ≤ y

/-- The single theorem-level named `sorry`: the actual bound and q-approximation
for the same C4/C5/C6/C7/C8 construction.  This is the C9 source statement,
not an `hq` input. -/
theorem sourcePilotApproximation_stage2
    (C6 : PaperNormalizedVolumeData places tuple mu)
    (C6Prod : C6ProductVolumeData (Y := I.ThetaPilotPoint D.place.v))
    (C7 : ∀ (n : ThetaPilotCarrier l) (x : I.ThetaPilotPoint D.place.v),
      SourceHolomorphicHullData D C5 C6Prod n x) (Theta Q : ℝ) :
    actual_values_bounded C6 C6Prod C7 Theta ∧ actual_q_approximated C6 C6Prod C7 Q := by
  sorry

/-- Complete consumer derivation: the two C9 statements imply `Q ≤ Theta`.
This uses no `hq` hypothesis. -/
theorem q_le_theta_of_sourcePilotApproximation
    (C6 : PaperNormalizedVolumeData places tuple mu)
    (C6Prod : C6ProductVolumeData (Y := I.ThetaPilotPoint D.place.v))
    (C7 : ∀ (n : ThetaPilotCarrier l) (x : I.ThetaPilotPoint D.place.v),
      SourceHolomorphicHullData D C5 C6Prod n x) (Theta Q : ℝ)
    (h : actual_values_bounded C6 C6Prod C7 Theta ∧ actual_q_approximated C6 C6Prod C7 Q) :
    Q ≤ Theta := by
  by_contra hnot
  have hlt : Theta < Q := lt_of_not_ge hnot
  have hpos : 0 < Q - Theta := sub_pos.mpr hlt
  obtain ⟨y, hyV, hyQ⟩ := h.2 ((Q - Theta) / 2) (half_pos hpos)
  have hyTheta : y ≤ Theta := h.1 y hyV
  have hmid : Q - (Q - Theta) / 2 ≤ Theta := le_trans hyQ hyTheta
  linarith

end LeanFormal.IUT.N8Closure.C9
