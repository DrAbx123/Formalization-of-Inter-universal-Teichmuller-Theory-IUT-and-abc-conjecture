import tmp.sheaf.n8.closure.NativeC1PaperSource
import LeanFormal.IUT.IUTIII.Theorem311.SourceArithmeticHolomorphicLanding
import LeanFormal.IUT.Foundations.LocalFields.IntegralUnits
import LeanFormal.IUT.Foundations.NumberField.LocalQParameter
import Mathlib.NumberTheory.NumberField.Completion.InfinitePlace

noncomputable section
set_option maxHeartbeats 1000000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace LeanFormal.IUT.N8Closure.NativeOneColumnActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.N8Closure.NativeInput
open LeanFormal.IUT.N8Closure.NativeC1PaperSource
open LeanFormal.IUT.LocalFieldIntegralUnits
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.NumberFieldFinitePlace

universe u

variable {l : PrimeGeFive} (P : NativeC1PaperSource l)

abbrev K : Type := P.X.S.arithmetic.K

/-- Dependent local field: finite place gets the normalized completion, infinite place its completion. -/
noncomputable def localFieldOfPlace (place : NumberFieldPlace (K P)) : Type :=
  match place with
  | .finite p => NormalizedCompletion p
  | .infinite p => p.Completion

/-- Dependent local ring: integers of finite completion; the field itself at infinity. -/
noncomputable def localRingOfPlace (place : NumberFieldPlace (K P)) : Type :=
  match place with
  | .finite p => Integers (NormalizedCompletion p)
  | .infinite p => p.Completion

@[reducible] noncomputable def ringOfPlace (place : NumberFieldPlace (K P)) :
    CommRing (localRingOfPlace (P := P) place) := by
  cases place with
  | finite p =>
      dsimp [localRingOfPlace]
      infer_instance
  | infinite p =>
      dsimp [localRingOfPlace]
      infer_instance

@[reducible] noncomputable def fieldOfPlace (place : NumberFieldPlace (K P)) :
    Field (localFieldOfPlace (P := P) place) := by
  cases place with
  | finite p =>
      dsimp [localFieldOfPlace]
      infer_instance
  | infinite p =>
      dsimp [localFieldOfPlace]
      infer_instance

noncomputable def inclusionOfPlace (place : NumberFieldPlace (K P)) :
    letI : CommRing (localRingOfPlace (P := P) place) := ringOfPlace (P := P) place
    letI : Field (localFieldOfPlace (P := P) place) := fieldOfPlace (P := P) place
    localRingOfPlace (P := P) place →+* localFieldOfPlace (P := P) place := by
  cases place with
  | finite p =>
      dsimp [localRingOfPlace, localFieldOfPlace]
      exact (Integers (NormalizedCompletion p)).subtype
  | infinite p =>
      dsimp [localRingOfPlace, localFieldOfPlace]
      exact RingHom.id _

noncomputable def oneColumn :
    SourceOneColumnArithmeticHolomorphicStructure (NativePlaces P.X.S) where
  localRing := fun v => localRingOfPlace (P := P) v.1
  ringOf := fun v => ringOfPlace (P := P) v.1
  localField := fun v => localFieldOfPlace (P := P) v.1
  fieldOf := fun v => fieldOfPlace (P := P) v.1
  localizationInclusion := fun v => inclusionOfPlace (P := P) v.1

end LeanFormal.IUT.N8Closure.NativeOneColumnActual

end
