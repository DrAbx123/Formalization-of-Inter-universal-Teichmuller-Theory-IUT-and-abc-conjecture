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

namespace LeanFormal.IUT.XiFPaper.S366OneColumnActualAdapted

variable {l : PrimeGeFive} (P : NativeC1PaperSource l)

noncomputable def oneColumnLocalField : NativePlaces P.X.S -> Type :=
  fun v =>
    match v.1 with
    | NumberFieldPlace.finite p => NumberFieldFinitePlace.Completion p
    | NumberFieldPlace.infinite p => p.Completion

noncomputable def oneColumnLocalRing : NativePlaces P.X.S -> Type :=
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

noncomputable def oneColumnInclusion (v : NativePlaces P.X.S) :
    oneColumnLocalRing P v →+* oneColumnLocalField P v := by
  cases h : v.1 with
  | finite p =>
      unfold oneColumnLocalRing oneColumnLocalField
      rw [h]
      exact algebraMap (Integers (NumberFieldFinitePlace.Completion p))
        (NumberFieldFinitePlace.Completion p)
  | infinite p =>
      unfold oneColumnLocalRing oneColumnLocalField
      rw [h]
      exact RingHom.id p.Completion

noncomputable def sourceOneColumnActual :
    SourceOneColumnArithmeticHolomorphicStructure (NativePlaces P.X.S) where
  localRing := oneColumnLocalRing P
  ringOf := fun v => inferInstance
  localField := oneColumnLocalField P
  fieldOf := fun v => inferInstance
  localizationInclusion := oneColumnInclusion P

end LeanFormal.IUT.XiFPaper.S366OneColumnActualAdapted
end