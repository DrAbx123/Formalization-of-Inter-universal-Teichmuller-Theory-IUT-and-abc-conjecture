import LeanFormal.IUT.IUTIII.Theorem311.SourceArithmeticHolomorphicLanding
import tmp.sheaf.n8.closure.NativeC1PaperSource
import LeanFormal.IUT.Foundations.LocalFields.IntegralUnits

noncomputable section
open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.N8Closure.NativeC1PaperSource
open LeanFormal.IUT.N8Closure.NativeInput
open LeanFormal.IUT.LocalFieldIntegralUnits

namespace LeanFormal.IUT.XiFPaper.S366OneColumnActual

variable {l : PrimeGeFive} (P : NativeC1PaperSource l)

@[reducible] noncomputable def oneColumnLocalField : NativePlaces P.X.S -> Type :=
  fun v =>
    match v.1 with
    | NumberFieldPlace.finite p => NumberFieldFinitePlace.Completion p
    | NumberFieldPlace.infinite p => p.Completion

@[reducible] noncomputable def oneColumnLocalRing : NativePlaces P.X.S -> Type :=
  fun v =>
    match v.1 with
    | NumberFieldPlace.finite p => Integers (NumberFieldFinitePlace.Completion p)
    | NumberFieldPlace.infinite p => p.Completion

instance (v : NativePlaces P.X.S) : CommRing (oneColumnLocalRing P v) := by
  unfold oneColumnLocalRing
  split <;> infer_instance

instance (v : NativePlaces P.X.S) : Field (oneColumnLocalField P v) := by
  unfold oneColumnLocalField
  split <;> infer_instance

noncomputable def sourceOneColumnActual :
    SourceOneColumnArithmeticHolomorphicStructure (NativePlaces P.X.S) where
  localRing := fun v =>
    match v.1 with
    | NumberFieldPlace.finite p => Integers (NumberFieldFinitePlace.Completion p)
    | NumberFieldPlace.infinite p => p.Completion
  ringOf := fun v => by split <;> infer_instance
  localField := fun v =>
    match v.1 with
    | NumberFieldPlace.finite p => NumberFieldFinitePlace.Completion p
    | NumberFieldPlace.infinite p => p.Completion
  fieldOf := fun v => by split <;> infer_instance
  localizationInclusion := fun v => by
    split
    · exact algebraMap (Integers (NumberFieldFinitePlace.Completion _))
        (NumberFieldFinitePlace.Completion _)
    · exact RingHom.id _
end LeanFormal.IUT.XiFPaper.S366OneColumnActual
end