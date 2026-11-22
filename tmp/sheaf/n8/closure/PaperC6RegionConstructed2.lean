import tmp.sheaf.n8.closure.C6TensorActual
import tmp.sheaf.n8.closure.C6ActualIQData
import LeanFormal.IUT.Foundations.LocalFields.FinitePadicTensorTopology
import LeanFormal.IUT.IUTI.InitialTheta.SourceInitialThetaData
import LeanFormal.IUT.ABCBridge.Geometry.FinitePlaceFullPrimePacket

/-!
# Paper C6 region constructed (actual tensor instance)

Actual paper C6 region input: choose a bad finite place from
`S.clauseB.bad_nonempty`, use its actual rational residue prime `p`, index by
the actual finite places above `p`, and build the actual tensor block C6 data
with the lead's `c6TensorActualData`.  The C6 region is the actual IQ image
set and Theta is the actual IQ hull log-volume.
-/

noncomputable section
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.N8Closure.PaperC6RegionConstructed2

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.NumberFieldFinitePlace
open MeasureTheory
open scoped BigOperators

variable {l : PrimeGeFive} (S : SourceInitialThetaData l)

/-- Actual chosen bad moduli finite place. -/
noncomputable def p0 : NumberField.FinitePlace S.candidate.arithmetic.Fmod :=
  Classical.choose S.clauseB.bad_nonempty

theorem p0_mem : p0 S ∈ S.candidate.VbadMod :=
  Classical.choose_spec S.clauseB.bad_nonempty

/-- Actual rational prime under the chosen bad place. -/
noncomputable def pNat : ℕ := (completionRationalPrime (p0 S)).val

instance factP : Fact (pNat S).Prime :=
  ⟨(completionRationalPrime (p0 S)).property⟩

/-- Actual finite places above the chosen bad residue prime. -/
abbrev Idx : Type := FinitePlaceAtPrime S.candidate.arithmetic.Fmod (pNat S)

instance idxFintype : Fintype (Idx S) := fintype_fullPrimePlaces

noncomputable def places : (i : Idx S) → Unit →
    FinitePlaceAtPrime S.candidate.arithmetic.Fmod (pNat S) := fun i _ => i

noncomputable def tuple : (i : Idx S) → Unit := fun _ => ()

abbrev Block (S : SourceInitialThetaData l) : Type :=
  LeanFormal.IUT.NumberFieldFinitePlace.ArithmeticTensorTupleBlock (places S) (tuple S)

/-- Paper C6 region input bundling the actual chosen bad place and the actual
tensor C6 data. -/
structure PaperC6RegionInput (S : SourceInitialThetaData l) where
  bad : NumberField.FinitePlace S.candidate.arithmetic.Fmod
  bad_mem : bad ∈ S.candidate.VbadMod
  tensor : C6TensorActualData (places S) (tuple S)

noncomputable def paperC6RegionInput : PaperC6RegionInput S where
  bad := p0 S
  bad_mem := p0_mem S
  tensor := c6TensorActualData (places S) (tuple S)

noncomputable def inputIqInterface (P : PaperC6RegionInput S) :
    IQHullLogVolumeInterface (Block S) := by
  letI := P.tensor.measurableSpace
  letI := P.tensor.borelSpace
  letI := P.tensor.addHaar
  exact P.tensor.data.iqInterface

/-- Actual C6 region: the IQ image set of the tensor data. -/
noncomputable def c6Region (P : PaperC6RegionInput S) : Set (Block S) :=
  (inputIqInterface S P).imageSet

/-- Actual C6 tensor hull. -/
noncomputable def c6HullSet (P : PaperC6RegionInput S) : Set (Block S) :=
  (inputIqInterface S P).hull

/-- Actual C6 tensor hull log-volume Theta. -/
noncomputable def c6Theta (P : PaperC6RegionInput S) : ENNReal :=
  (inputIqInterface S P).logVolume (c6HullSet S P)

/-- Actual C6 region log-volume. -/
noncomputable def c6RegionVolume (P : PaperC6RegionInput S) : ENNReal :=
  (inputIqInterface S P).logVolume (c6Region S P)

/-- Actual region log-volume <= Theta, from the exact C6 IQ hull containment. -/
theorem c6RegionVolume_le_c6Theta (P : PaperC6RegionInput S) :
    c6RegionVolume S P ≤ c6Theta S P := by
  unfold c6RegionVolume c6Theta c6Region c6HullSet
  exact (inputIqInterface S P).logVolume_mono (inputIqInterface S P).imageSet_subset_hull

theorem c6Theta_lt_top (P : PaperC6RegionInput S) : c6Theta S P < ⊤ := by
  unfold c6Theta c6HullSet
  exact IQHullLogVolumeInterface.hull_logVolume_lt_top (inputIqInterface S P)

theorem c6Theta_ne_top (P : PaperC6RegionInput S) : c6Theta S P ≠ ⊤ :=
  ne_of_lt (c6Theta_lt_top S P)

theorem c6RegionVolume_toReal_le_theta (P : PaperC6RegionInput S) :
    (c6RegionVolume S P).toReal ≤ (c6Theta S P).toReal :=
  ENNReal.toReal_mono (c6Theta_ne_top S P) (c6RegionVolume_le_c6Theta S P)

end LeanFormal.IUT.N8Closure.PaperC6RegionConstructed2
