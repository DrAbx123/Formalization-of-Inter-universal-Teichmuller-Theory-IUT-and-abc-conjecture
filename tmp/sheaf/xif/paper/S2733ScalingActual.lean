import tmp.sheaf.xif.paper.S2732ScaleShiftScalingAttempt
import tmp.sheaf.xif.paper.QVFamThetaImageActual
import tmp.sheaf.xif.paper.C3LogShellTensorPacketActual
import tmp.sheaf.xif.paper.S2737C3BlockCharActual
import LeanFormal.IUT.ABCBridge.Geometry.FinitePlaceIQHullInterface

noncomputable section
set_option synthInstance.maxHeartbeats 400000
namespace LeanFormal.IUT.XiFPaper.S2733ScalingActual

open scoped NNReal ENNReal

open MeasureTheory
open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.N8Closure.SourcePilotRegion
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.LocalFieldPadicTensor
open LeanFormal.IUT.XiFPaper.C3LogShellTensorPacketActual
open LeanFormal.IUT.XiFPaper.QVFamThetaImageActual
open LeanFormal.IUT.XiFPaper.S2732ScaleShiftScalingAttempt
open LeanFormal.IUT.XiFPaper.QPilotZeroLocusDivisorActual

variable {l : PrimeGeFive} {V : Type} {I : OriginalInput l V}
variable (C3 : SourcePilotRegionData (l := l) (V := V) I)
variable (T : SourceNativeInitialThetaData fiveLabel)
variable (b : Bad (nativePlaceSelection T))

local instance s2733BlockNormedAddCommGroup :
    NormedAddCommGroup (C3LogShellTensorBlock C3) := by
  letI : ∀ i, NormedAddCommGroup (C3LogShellFiber C3 i) := fun i => inferInstance
  letI : ∀ i, NormedSpace ℚ_[C3.p] (C3LogShellFiber C3 i) := fun i => inferInstance
  letI : ∀ i, FiniteDimensional ℚ_[C3.p] (C3LogShellFiber C3 i) := fun i => inferInstance
  infer_instance

local instance s2733BlockNormedSpace :
    NormedSpace ℚ_[C3.p] (C3LogShellTensorBlock C3) := by
  letI : ∀ i, NormedAddCommGroup (C3LogShellFiber C3 i) := fun i => inferInstance
  letI : ∀ i, NormedSpace ℚ_[C3.p] (C3LogShellFiber C3 i) := fun i => inferInstance
  letI : ∀ i, FiniteDimensional ℚ_[C3.p] (C3LogShellFiber C3 i) := fun i => inferInstance
  infer_instance

local instance s2733BlockFiniteDimensional :
    FiniteDimensional ℚ_[C3.p] (C3LogShellTensorBlock C3) := by
  letI : ∀ i, NormedAddCommGroup (C3LogShellFiber C3 i) := fun i => inferInstance
  letI : ∀ i, NormedSpace ℚ_[C3.p] (C3LogShellFiber C3 i) := fun i => inferInstance
  letI : ∀ i, FiniteDimensional ℚ_[C3.p] (C3LogShellFiber C3 i) := fun i => inferInstance
  infer_instance

local instance s2733BlockProperSpace :
    ProperSpace (C3LogShellTensorBlock C3) := by
  letI : ∀ i, NormedAddCommGroup (C3LogShellFiber C3 i) := fun i => inferInstance
  letI : ∀ i, NormedSpace ℚ_[C3.p] (C3LogShellFiber C3 i) := fun i => inferInstance
  letI : ∀ i, FiniteDimensional ℚ_[C3.p] (C3LogShellFiber C3 i) := fun i => inferInstance
  infer_instance

/-- Local Set action of p-adic units, avoiding missing global Set SMul. -/
local instance s2733UnitsSetSmul :
    SMul ℚ_[C3.p]ˣ (Set (C3LogShellTensorBlock C3)) :=
  ⟨fun u S => (fun x => ((u : ℚ_[C3.p]) • x)) '' S⟩

local instance s2733BlockMeasurableSpace :
    MeasurableSpace (C3LogShellTensorBlock C3) := borel _

local instance s2733BlockBorelSpace :
    BorelSpace (C3LogShellTensorBlock C3) := ⟨rfl⟩

local instance s2733BlockLocallyCompactSpace :
    LocallyCompactSpace (C3LogShellTensorBlock C3) := by
  infer_instance

/-- Candidate q-pilot exponent from qVFamily order. -/
noncomputable def qPilotLambdaFromOrder : ℚ_[C3.p] :=
  (C3.p : ℚ_[C3.p]) ^ (qVFamily T b).order

/-- Haar scaling under a p-adic unit, via distribHaarChar_mul. -/
theorem S2733_scalingHaar
    (u : ℚ_[C3.p]ˣ) (S : Set (C3LogShellTensorBlock C3)) :
    actualC3LogShellTensorHaar C3 (u • S)
      = (distribHaarChar (C3LogShellTensorBlock C3) u : ENNReal) *
          actualC3LogShellTensorHaar C3 S := by
  exact (distribHaarChar_mul
    (μ := actualC3LogShellTensorHaar C3) u S).symm

/-- Log-volume of a set under the tensor Haar. -/
noncomputable def c3LogVolume (S : Set (C3LogShellTensorBlock C3)) : ℝ :=
  Real.log ((actualC3LogShellTensorHaar C3 S).toReal)

/-- Log form of the Haar scaling law. -/
theorem S2733_scalingLog
    (u : ℚ_[C3.p]ˣ) (S : Set (C3LogShellTensorBlock C3))
    (hpos : actualC3LogShellTensorHaar C3 S ≠ 0)
    (hfinite : actualC3LogShellTensorHaar C3 S ≠ ⊤) :
    c3LogVolume C3 (u • S) =
      c3LogVolume C3 S +
        Real.log ((distribHaarChar (C3LogShellTensorBlock C3) u : ℝ)) := by
  unfold c3LogVolume
  rw [S2733_scalingHaar C3 u S, ENNReal.toReal_mul, ENNReal.coe_toReal]
  rw [Real.log_mul]
  · ring
  · exact_mod_cast (ne_of_gt
      (distribHaarChar_pos (A := C3LogShellTensorBlock C3) (g := u)))
  · exact ENNReal.toReal_ne_zero.mpr ⟨hpos, hfinite⟩


/-- Scaling law with the explicit tensor-block character formula. -/
theorem S2733_scalingHaar_norm
    (u : ℚ_[C3.p]ˣ) (S : Set (C3LogShellTensorBlock C3)) :
    actualC3LogShellTensorHaar C3 (u • S) =
      ((↑((‖(u : ℚ_[C3.p])‖₊) ^
        Module.finrank ℚ_[C3.p] (C3LogShellTensorBlock C3))) : ENNReal) *
        actualC3LogShellTensorHaar C3 S := by
  rw [S2733_scalingHaar, LeanFormal.IUT.XiFPaper.S2737C3BlockCharActual.c3LogShellTensorBlock_char]

/-- Log scaling law with the explicit tensor-block character formula. -/
theorem S2733_scalingLog_norm
    (u : ℚ_[C3.p]ˣ) (S : Set (C3LogShellTensorBlock C3))
    (hpos : actualC3LogShellTensorHaar C3 S ≠ 0)
    (hfinite : actualC3LogShellTensorHaar C3 S ≠ ⊤) :
    c3LogVolume C3 (u • S) =
      c3LogVolume C3 S +
        Real.log ((↑((‖(u : ℚ_[C3.p])‖₊) ^
          Module.finrank ℚ_[C3.p] (C3LogShellTensorBlock C3)) : ℝ)) := by
  rw [S2733_scalingLog C3 u S hpos hfinite,
    LeanFormal.IUT.XiFPaper.S2737C3BlockCharActual.c3LogShellTensorBlock_char]

#check S2733_scalingHaar_norm
#check S2733_scalingLog_norm




theorem c3LogVolume_smul_norm
    (u : ℚ_[C3.p]ˣ) (S : Set (C3LogShellTensorBlock C3))
    (hpos : actualC3LogShellTensorHaar C3 S ≠ 0)
    (hfinite : actualC3LogShellTensorHaar C3 S ≠ ⊤) :
    Real.log ((actualC3LogShellTensorHaar C3 (u • S)).toReal) =
      Real.log ((↑((‖(u : ℚ_[C3.p])‖₊) ^
        Module.finrank ℚ_[C3.p] (C3LogShellTensorBlock C3)) : ℝ)) +
      Real.log ((actualC3LogShellTensorHaar C3 S).toReal) := by
  have hbase : (0 : ℝ≥0) < ‖(u : ℚ_[C3.p])‖₊ := by
    rw [← NNReal.coe_lt_coe]
    push_cast
    exact norm_pos_iff.mpr (Units.ne_zero u)
  have hcpos : (0 : ℝ) < (↑((‖(u : ℚ_[C3.p])‖₊) ^
      Module.finrank ℚ_[C3.p] (C3LogShellTensorBlock C3)) : ℝ) := by
    exact_mod_cast pow_pos hbase _
  rw [S2733_scalingHaar_norm, ENNReal.toReal_mul, ENNReal.coe_toReal]
  rw [Real.log_mul (ne_of_gt hcpos)
    (ENNReal.toReal_ne_zero.mpr ⟨hpos, hfinite⟩)]

#check c3LogVolume_smul_norm

#check qPilotLambdaFromOrder
#check S2733_scalingHaar
#check (inferInstance : LocallyCompactSpace (C3LogShellTensorBlock C3))
end LeanFormal.IUT.XiFPaper.S2733ScalingActual
end
