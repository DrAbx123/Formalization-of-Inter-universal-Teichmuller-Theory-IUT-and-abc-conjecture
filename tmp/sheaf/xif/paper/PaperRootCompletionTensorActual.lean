import tmp.sheaf.xif.paper.PaperThetaRootObstructionActual
import LeanFormal.IUT.ABCBridge.Geometry.FinitePlaceSourceAlgebraicClosure
import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
import Mathlib.FieldTheory.IntermediateField.Adjoin.Algebra
import LeanFormal.IUT.Foundations.LocalFields.FinitePadicTensorTopology
import Mathlib.Analysis.Normed.Module.Basic

noncomputable section
open scoped BigOperators
open scoped IntermediateField
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 1000000

namespace LeanFormal.IUT.XiFPaper.PaperRootCompletionTensorActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.PaperThetaRootObstructionActual
open LeanFormal.IUT.N8Closure.C3Roots
open LeanFormal.IUT.LocalFieldPadicTensor

universe u

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable (b : Bad (nativePlaceSelection T))

/-- The normalized completion K. -/
abbrev rootBase : Type := sourceRootField T b

/-- The actual normed algebraic closure of the qVFamily place. -/
abbrev rootNormedAmbient : Type :=
  AlgebraicClosure (sourceRootField T b)

/-- Normed-field structure transported from the actual source algebraic closure. -/
noncomputable instance rootNormedAmbientNormedField :
    NontriviallyNormedField (rootNormedAmbient T b) :=
  inferInstanceAs (NontriviallyNormedField
    (SourceAlgebraicClosure (qVFamTensorPlace T b)))

/-- Normed algebra structure transported from the actual source algebraic closure. -/
noncomputable instance rootNormedAmbientNormedAlgebra :
    NormedAlgebra (rootBase T b) (rootNormedAmbient T b) :=
  inferInstanceAs (NormedAlgebra (NormalizedCompletion (qVFamTensorPlace T b))
    (SourceAlgebraicClosure (qVFamTensorPlace T b)))

/-- The actual root in the normed ambient. -/
noncomputable def rootNormedElement : rootNormedAmbient T b :=
  (sourceRoot T b : rootNormedAmbient T b)

/-- L = K(root) in the normed ambient. -/
noncomputable abbrev rootNormedExtension :
    IntermediateField (rootBase T b) (rootNormedAmbient T b) :=
  IntermediateField.adjoin (rootBase T b) {rootNormedElement T b}

/-- The root lies in L. -/
theorem rootNormedElement_mem : rootNormedElement T b ∈ rootNormedExtension T b := by
  change rootNormedElement T b ∈
    IntermediateField.adjoin (rootBase T b)
      ({rootNormedElement T b} : Set (rootNormedAmbient T b))
  exact (IntermediateField.subset_adjoin (rootBase T b)
    ({rootNormedElement T b} : Set (rootNormedAmbient T b)))
      (Set.mem_singleton _)

/-- The actual root equation in the ambient. -/
theorem rootNormedElement_pow :
    (rootNormedElement T b) ^ (2 * l.value) =
      (unitToAlgClosed (sourceRootQUnit T b) : rootNormedAmbient T b) := by
  simpa [rootNormedElement, rootNormedAmbient, rootBase] using sourceRoot_pow T b

/-- Root integrality from its explicit monic equation. -/
theorem rootNormedElement_isIntegral :
    IsIntegral (rootBase T b) (rootNormedElement T b) := by
  have hpow : IsIntegral (rootBase T b)
      ((rootNormedElement T b) ^ (2 * l.value)) := by
    rw [rootNormedElement_pow]
    exact isIntegral_algebraMap
  exact IsIntegral.of_pow (by
    have : 0 < 2 * l.value := Nat.mul_pos (by norm_num) l.prime.pos
    exact this) hpow

/-- L is finite-dimensional over K. -/
noncomputable instance rootNormedExtensionFiniteDimensional :
    FiniteDimensional (rootBase T b) (rootNormedExtension T b) := by
  exact IntermediateField.adjoin.finiteDimensional
    (K := rootBase T b) (x := rootNormedElement T b)
    (rootNormedElement_isIntegral T b)

/-- L is a nontrivially normed field. -/
noncomputable instance rootNormedExtensionNormedField :
    NontriviallyNormedField (rootNormedExtension T b) := inferInstance

/-- K is complete. -/
noncomputable instance rootBaseComplete : CompleteSpace (rootBase T b) := inferInstance

/-- L is complete: finite-dimensional over the complete normed field K. -/
theorem rootNormedExtensionComplete :
    CompleteSpace (rootNormedExtension T b) := by
  haveI : CompleteSpace (rootBase T b) := inferInstance
  haveI : NormedSpace (rootBase T b) (rootNormedExtension T b) := inferInstance
  exact FiniteDimensional.complete (rootBase T b) (rootNormedExtension T b)

/-- L has the measurable structure. -/
noncomputable instance rootNormedExtensionMeasurableSpace :
    MeasurableSpace (rootNormedExtension T b) :=
  borel (rootNormedExtension T b)

/-- L has the Borel structure. -/
noncomputable instance rootNormedExtensionBorelSpace :
    BorelSpace (rootNormedExtension T b) := ⟨rfl⟩


/-- The actual root unit in L. -/
noncomputable def rootNormedUnit : (rootNormedExtension T b)ˣ :=
  Units.mk0 ⟨rootNormedElement T b, rootNormedElement_mem T b⟩ (by
    intro h
    exact Units.ne_zero (sourceRoot T b) (congrArg Subtype.val h))

/-- The actual root log-volume. -/
noncomputable def rootNormedLogVolume : Real :=
  Real.log ‖(rootNormedUnit T b : rootNormedExtension T b)‖

/-- The root theta image value root^(j^2) in the ambient (integer power). -/
noncomputable def rootNormedThetaValue
    (j : SignedLabel l.value) : rootNormedAmbient T b :=
  (rootNormedElement T b) ^ (gaussExponent j.1)

/-- The root theta image value lies in L. -/
theorem rootNormedThetaValue_mem (j : SignedLabel l.value) :
    rootNormedThetaValue T b j ∈ rootNormedExtension T b := by
  change (rootNormedElement T b) ^ (gaussExponent j.1) ∈
    rootNormedExtension T b
  exact (rootNormedExtension T b).pow_mem (rootNormedElement_mem T b)
    (gaussExponent j.1)

/-- The root theta image in L. -/
noncomputable def rootNormedThetaValueInL (j : SignedLabel l.value) :
    rootNormedExtension T b :=
  ⟨rootNormedThetaValue T b j, rootNormedThetaValue_mem T b j⟩

/-- The actual root theta image set in L. -/
noncomputable def rootNormedThetaImageSet : Set (rootNormedExtension T b) :=
  Set.range (rootNormedThetaValueInL T b)



/-- Qp normed-algebra structure on K. -/
noncomputable instance rootBaseNormedAlgebraQp :
    NormedAlgebra ℚ_[(qVFamTensorP T b)] (rootBase T b) :=
  inferInstanceAs (NormedAlgebra (PadicScalarField (qVFamTensorPlace T b))
    (NormalizedCompletion (qVFamTensorPlace T b)))

/-- Qp finite-dimensional structure on K. -/
noncomputable instance rootBaseFiniteDimensionalQp :
    FiniteDimensional ℚ_[(qVFamTensorP T b)] (rootBase T b) :=
  inferInstanceAs (FiniteDimensional (PadicScalarField (qVFamTensorPlace T b))
    (NormalizedCompletion (qVFamTensorPlace T b)))

/-- Qp normed-space structure on L (restricted scalars from K). -/
noncomputable instance rootNormedExtensionNormedSpaceQp :
    NormedSpace ℚ_[(qVFamTensorP T b)] (rootNormedExtension T b) :=
  NormedSpace.restrictScalars ℚ_[(qVFamTensorP T b)] (rootBase T b)
    (rootNormedExtension T b)

/-- Finite-dimensional Qp structure on L. -/
noncomputable instance rootNormedExtensionFiniteDimensionalQp :
    FiniteDimensional ℚ_[(qVFamTensorP T b)] (rootNormedExtension T b) := by
  haveI : FiniteDimensional ℚ_[(qVFamTensorP T b)] (rootBase T b) := inferInstance
  exact FiniteDimensional.trans ℚ_[(qVFamTensorP T b)] (rootBase T b)
    (rootNormedExtension T b)

/-- The actual finite p-adic tensor block over L. -/
abbrev rootTensorBlock (T : SourceNativeInitialThetaData.{0} l)
    (b : Bad (nativePlaceSelection T)) : Type :=
  FinitePadicTensor (p := qVFamTensorP T b) (fun _ : Unit => rootNormedExtension T b)

/-- The actual tensor unit in the root block. -/
noncomputable def rootTensorUnit (T : SourceNativeInitialThetaData.{0} l)
    (b : Bad (nativePlaceSelection T)) : rootTensorBlock T b :=
  finitePadicTensorTprod (p := qVFamTensorP T b)
    (fun _ : Unit => rootNormedExtension T b)
    (fun _ => (rootNormedUnit T b : rootNormedExtension T b))

/-- The actual root tensor log-volume: the actual root unit log-volume. -/
noncomputable def rootTensorLogVolume (T : SourceNativeInitialThetaData.{0} l)
    (b : Bad (nativePlaceSelection T)) : Real :=
  rootNormedLogVolume T b

/-- The actual root theta image in the root tensor block. -/
noncomputable def rootTensorThetaImage (T : SourceNativeInitialThetaData.{0} l)
    (b : Bad (nativePlaceSelection T)) (j : SignedLabel l.value) :
    rootTensorBlock T b :=
  finitePadicTensorTprod (p := qVFamTensorP T b)
    (fun _ : Unit => rootNormedExtension T b)
    (fun _ => (rootNormedThetaValueInL T b j : rootNormedExtension T b))

/-- Actual root completion tensor data. -/
structure RootCompletionTensorData
    (T : SourceNativeInitialThetaData.{0} l)
    (b : Bad (nativePlaceSelection T)) where
  unit : rootTensorBlock T b
  unit_eq : unit = rootTensorUnit T b
  logVolume : Real
  logVolume_eq : logVolume = rootTensorLogVolume T b
  thetaImage : SignedLabel l.value → rootTensorBlock T b
  thetaImage_eq : thetaImage = rootTensorThetaImage T b

/-- The actual root completion tensor data constructor. -/
noncomputable def rootCompletionTensorData
    (T : SourceNativeInitialThetaData.{0} l)
    (b : Bad (nativePlaceSelection T)) :
    RootCompletionTensorData T b where
  unit := rootTensorUnit T b
  unit_eq := rfl
  logVolume := rootTensorLogVolume T b
  logVolume_eq := rfl
  thetaImage := rootTensorThetaImage T b
  thetaImage_eq := rfl



end LeanFormal.IUT.XiFPaper.PaperRootCompletionTensorActual

end