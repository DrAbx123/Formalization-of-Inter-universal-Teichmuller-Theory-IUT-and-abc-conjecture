import tmp.sheaf.n8.closure.C6NormalizedTensorHaar
import tmp.sheaf.n8.closure.PaperC6RegionConstructed2
import Mathlib.LinearAlgebra.PiTensorProduct.Basic

/-!
# C7 actual q-pilot region on the C6 tensor block

From the paper source `SourceInitialThetaData` choose a bad Fmod place `p0` and
lift it to an F place `pF`; `ClauseB.qParameter` gives the actual q in the
completion at `pF`.  On the one-factor C6 tensor block at `pF` we form the
actual q-scaled integral region and take its normalized C6 Haar mass/log-volume.
The exact missing equality with `log‖q‖` is recorded.
-/

noncomputable section
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.N8Closure.C7QPilotRegionActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.N8C6ActualIQ
open LeanFormal.IUT.N8Closure.C6NormalizedTensorHaar
open LeanFormal.IUT.LocalFieldIntegralUnits
open MeasureTheory
open scoped BigOperators ENNReal TensorProduct

variable {l : PrimeGeFive} (S : SourceInitialThetaData l)

/-- Actual bad Fmod place from Clause B. -/
noncomputable def p0 : NumberField.FinitePlace S.candidate.arithmetic.Fmod :=
  Classical.choose S.clauseB.bad_nonempty

theorem p0_mem : p0 S ∈ S.candidate.VbadMod :=
  Classical.choose_spec S.clauseB.bad_nonempty

/-- Actual lift of the bad Fmod place to an F place. -/
noncomputable def pF : NumberField.FinitePlace S.candidate.arithmetic.F :=
  Classical.choose (NumberFieldFinitePlace.comap_surjective (K := S.candidate.arithmetic.F) (p0 S))

theorem pF_comap : NumberFieldFinitePlace.comap (pF S) = p0 S :=
  Classical.choose_spec (NumberFieldFinitePlace.comap_surjective (K := S.candidate.arithmetic.F) (p0 S))

theorem pF_bad : NumberFieldFinitePlace.comap (pF S) ∈ S.candidate.VbadMod := by
  rw [pF_comap S]
  exact p0_mem S

/-- Actual q candidate from Clause B at the lifted bad place. -/
noncomputable def qCandidate : FinitePlaceQCandidate (pF S) :=
  S.clauseB.qParameter (pF S) (pF_bad S)

/-- Actual q element in the completion at the bad place. -/
noncomputable def q : Completion (pF S) := (qCandidate S).q

theorem q_ne_zero : q S ≠ 0 := (qCandidate S).q_ne_zero

/-- The chosen rational prime under `pF`. -/
noncomputable def pNat : ℕ := (completionRationalPrime (pF S)).val

instance factP : Fact (pNat S).Prime :=
  ⟨(completionRationalPrime (pF S)).property⟩

/-- Actual finite-place-at-prime datum at `pF`. -/
noncomputable def placeAtPrime : FinitePlaceAtPrime S.candidate.arithmetic.F (pNat S) :=
  ⟨pF S, rfl⟩

abbrev Idx : Type := Unit

noncomputable def places : (i : Idx) → Unit →
    FinitePlaceAtPrime S.candidate.arithmetic.F (pNat S) := fun _ _ => placeAtPrime S

noncomputable def tuple (S : SourceInitialThetaData l) : (i : Idx) → Unit :=
  fun _ => ()

abbrev Block : Type := ArithmeticTensorTupleBlock (places S) (tuple S)

noncomputable def e : Block S ≃ₗ[ℚ_[pNat S]]
    CommonPrimeCompletion (placeAtPrime S) :=
  PiTensorProduct.subsingletonEquiv (R := ℚ_[pNat S])
    (s := fun _ : Idx => CommonPrimeCompletion (placeAtPrime S)) ()

/-- Actual q-scaled integral region on the one-factor C6 tensor block. -/
noncomputable def qAtPrime : CommonPrimeCompletion (placeAtPrime S) :=
  q S

noncomputable def qPilotRegion : Set (Block S) :=
  Set.image (fun y : CommonPrimeCompletion (placeAtPrime S) => (e S).symm y)
    (Set.image (fun x : CommonPrimeCompletion (placeAtPrime S) => qAtPrime S * x)
      (Integers (CommonPrimeCompletion (placeAtPrime S)) : Set _))

/-- Actual normalized C6 tensor data at the chosen block. -/
noncomputable def normalizedData :
    @Measure (Block S) (rawData (places S) (tuple S)).measurableSpace := by
  let T := rawData (places S) (tuple S)
  letI := T.measurableSpace
  exact c6TensorNormalizedData (places S) (tuple S)

/-- Normalized q-pilot region mass. -/
noncomputable def qPilotMass : ENNReal := by
  let T := rawData (places S) (tuple S)
  letI := T.measurableSpace
  exact normalizedData S (qPilotRegion S)

/-- Normalized q-pilot log-volume readout. -/
noncomputable def QPaper : ℝ := Real.log (qPilotMass S).toReal

/-- Exact target: the normalized q-pilot log-volume is the log of the actual
q norm. -/
def QPaperEqLogNorm : Prop := QPaper S = Real.log ‖q S‖

end LeanFormal.IUT.N8Closure.C7QPilotRegionActual

end