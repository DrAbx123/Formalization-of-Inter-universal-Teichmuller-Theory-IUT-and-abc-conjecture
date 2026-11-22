import LeanFormal.IUT.IUTII.Frobenioid.Example36SourceLogKummerIdentification
import LeanFormal.IUT.ABCBridge.Geometry.FinitePlaceCommonPrimeCompletion
import LeanFormal.IUT.Foundations.LocalFields.IntegralUnitLogarithmFunctoriality
import LeanFormal.IUT.Foundations.LocalFields.IntegralUnitGaloisDescent
import LeanFormal.IUT.Foundations.LocalFields.LogarithmSeriesTransport
import Mathlib.Tactic

set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1500000

/-!
# Actual Q_l source carrier map into the normalized completion

At a prime l (the concrete primes are >= 5) and an actual place of a number
field F over l.value, the source local field Q_l embeds isometrically into the
normalized completion F_v by the actual algebra map. This is the concrete
source-carrier map for the Q_l source log-shell; it is an embedding, not an
identification with the whole normalized completion.

The map is built only from actual production definitions:
* source field sourceLocalField l = Q_l;
* target CommonPrimeCompletion place = NormalizedCompletion place.val;
* algebraMap Q_l F_v;
* integralUnitMap and the actual logarithm transport.

No theta-link comparison is assumed here; that residual is recorded in
SourceQlThetaLinkBridge.lean.
-/

namespace ABCBridge.SourceQlCarrierMap

noncomputable section

open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.IUTII.Frobenioid.Example36
open LeanFormal.IUT.LocalFieldLogarithm
open LeanFormal.IUT.LocalFieldIntegralUnits
open scoped NumberField

variable {F : Type} [Field F] [NumberField F]
variable (l : LeanFormal.IUT.PrimeGeFive)
variable (place : FinitePlaceAtPrime F l.value)

local instance sourceQlCarrierPrimeFact : Fact (Nat.Prime l.value) :=
  l.factPrime

/-- Actual algebra-map embedding of the source Q_l into the normalized
completion at the chosen place. -/
noncomputable def sourceQlToTargetRingHom :
    sourceLocalField l →+* CommonPrimeCompletion place :=
  algebraMap (sourceLocalField l) (CommonPrimeCompletion place)

/-- The actual source embedding is an isometry for the normalized norms. -/
theorem sourceQlToTargetRingHom_isometry :
    Isometry (sourceQlToTargetRingHom l place) :=
  isometry_localField_algebraMap (K := sourceLocalField l)
    (L := CommonPrimeCompletion place)

/-- Actual integral-unit transport along the source embedding. -/
noncomputable def sourceQlUnitMap :
    (Integers (sourceLocalField l))ˣ →* (Integers (CommonPrimeCompletion place))ˣ :=
  integralUnitMap (sourceQlToTargetRingHom l place)
    (sourceQlToTargetRingHom_isometry l place)

theorem sourceQlUnitMap_val (u : (Integers (sourceLocalField l))ˣ) :
    ((sourceQlUnitMap l place u).val : CommonPrimeCompletion place) =
      sourceQlToTargetRingHom l place (u.val : sourceLocalField l) := rfl

/-- Principal units are carried into principal units. -/
theorem sourceQlUnitMap_mem_principalUnits
    (u : (Integers (sourceLocalField l))ˣ) (hu : u ∈ principalUnits) :
    sourceQlUnitMap l place u ∈ principalUnits :=
  integralUnitMap_mem_principalUnits (sourceQlToTargetRingHom l place)
    (sourceQlToTargetRingHom_isometry l place) u hu

/-- The actual principal-unit logarithm is compatible with the source
embedding: log(source unit) is the target log of the transported unit. -/
theorem sourceQl_principalUnitLog_compat
    (u : principalUnits (K := sourceLocalField l)) :
    sourceQlToTargetRingHom l place
        (principalUnitLog (K := sourceLocalField l) u) =
      principalUnitLog (K := CommonPrimeCompletion place)
        ⟨sourceQlUnitMap l place (u : (Integers (sourceLocalField l))ˣ),
          sourceQlUnitMap_mem_principalUnits l place
            (u : (Integers (sourceLocalField l))ˣ) u.property⟩ := by
  change sourceQlToTargetRingHom l place
      (log1p (((u : (Integers (sourceLocalField l))ˣ).val :
        sourceLocalField l) - 1)) =
    log1p (((sourceQlUnitMap l place
      (u : (Integers (sourceLocalField l))ˣ)).val :
        CommonPrimeCompletion place) - 1)
  have hval : ((sourceQlUnitMap l place
      (u : (Integers (sourceLocalField l))ˣ)).val :
        CommonPrimeCompletion place) =
      sourceQlToTargetRingHom l place
        (((u : (Integers (sourceLocalField l))ˣ).val : sourceLocalField l)) :=
    integralUnitMap_val (sourceQlToTargetRingHom l place)
      (sourceQlToTargetRingHom_isometry l place)
      (u : (Integers (sourceLocalField l))ˣ)
  rw [hval, ← map_one, ← map_sub]
  haveI : NormedField (sourceLocalField l) := inferInstance
  haveI : NormedAlgebra ℚ_[l.value] (sourceLocalField l) := inferInstance
  haveI : CharZero (sourceLocalField l) := inferInstance
  haveI : CompleteSpace (sourceLocalField l) := inferInstance
  haveI : NormedField (CommonPrimeCompletion place) :=
    LeanFormal.IUT.NumberFieldFinitePlace.commonPrimeCompletionNormedField place
  haveI : NormedAlgebra ℚ_[l.value] (CommonPrimeCompletion place) :=
    LeanFormal.IUT.NumberFieldFinitePlace.commonPrimeCompletionNormedAlgebra place
  haveI : CharZero (CommonPrimeCompletion place) :=
    LeanFormal.IUT.NumberFieldFinitePlace.commonPrimeCompletionCharZero place
  haveI : CompleteSpace (CommonPrimeCompletion place) :=
    LeanFormal.IUT.NumberFieldFinitePlace.commonPrimeCompletionComplete place
  exact log1p_map (p := l.value) (K := sourceLocalField l)
    (L := CommonPrimeCompletion place)
    (e := sourceQlToTargetRingHom l place)
    (he := sourceQlToTargetRingHom_isometry l place)
    (((u : (Integers (sourceLocalField l))ˣ).val : sourceLocalField l) - 1)
    ((mem_principalUnits_iff _).mp u.property)

/-- Actual map of the unscaled Q_l principal-unit log-shell into the
normalized-completion principal-unit log image. -/
noncomputable def sourceQlLogShellMap :
    sourceLogShell l →+ principalUnitLogImage (K := CommonPrimeCompletion place) l.value where
  toFun x :=
    ⟨sourceQlToTargetRingHom l place (x : sourceLocalField l), by
      rcases x.property with ⟨u, hu⟩
      refine ⟨⟨sourceQlUnitMap l place (u : (Integers (sourceLocalField l))ˣ),
        sourceQlUnitMap_mem_principalUnits l place
          (u : (Integers (sourceLocalField l))ˣ) u.property⟩, ?_⟩
      rw [← hu]
      simpa only using
        (sourceQl_principalUnitLog_compat l place u).symm⟩
  map_zero' := by
    ext
    change algebraMap (sourceLocalField l) (CommonPrimeCompletion place) 0 = 0
    exact map_zero _
  map_add' x y := by
    ext
    change algebraMap (sourceLocalField l) (CommonPrimeCompletion place)
        ((x : sourceLocalField l) + (y : sourceLocalField l)) =
      algebraMap (sourceLocalField l) (CommonPrimeCompletion place)
          (x : sourceLocalField l) +
        algebraMap (sourceLocalField l) (CommonPrimeCompletion place)
          (y : sourceLocalField l)
    exact map_add _ _ _

@[simp] theorem sourceQlLogShellMap_coe (x : sourceLogShell l) :
    (sourceQlLogShellMap l place x : CommonPrimeCompletion place) =
      sourceQlToTargetRingHom l place (x : sourceLocalField l) := rfl

theorem sourceQlToTargetRingHom_injective :
    Function.Injective (sourceQlToTargetRingHom l place) :=
  (sourceQlToTargetRingHom_isometry l place).injective

theorem sourceQlToTargetRingHom_norm (x : sourceLocalField l) :
    ‖sourceQlToTargetRingHom l place x‖ = ‖x‖ :=
  norm_map_of_isometry (sourceQlToTargetRingHom l place)
    (sourceQlToTargetRingHom_isometry l place) x

@[simp] theorem sourceQlUnitMap_one :
    sourceQlUnitMap l place 1 = 1 :=
  map_one (sourceQlUnitMap l place)

theorem sourceQlUnitMap_mul (u v : (Integers (sourceLocalField l))ˣ) :
    sourceQlUnitMap l place (u * v) =
      sourceQlUnitMap l place u * sourceQlUnitMap l place v :=
  map_mul (sourceQlUnitMap l place) u v

/-- On the actual log-Kummer generator, the log-shell map is the transported
target principal-unit logarithm. -/
theorem sourceQlLogShellMap_logKummerShell
    (u : sourcePrincipalUnits l) :
    sourceQlLogShellMap l place (sourceLogKummerShell l u) =
      ⟨principalUnitLog (K := CommonPrimeCompletion place)
        ⟨sourceQlUnitMap l place (u : (Integers (sourceLocalField l))ˣ),
          sourceQlUnitMap_mem_principalUnits l place
            (u : (Integers (sourceLocalField l))ˣ) u.property⟩,
        ⟨⟨sourceQlUnitMap l place (u : (Integers (sourceLocalField l))ˣ),
          sourceQlUnitMap_mem_principalUnits l place
            (u : (Integers (sourceLocalField l))ˣ) u.property⟩, rfl⟩⟩ := by
  apply Subtype.ext
  rw [sourceQlLogShellMap_coe]
  exact sourceQl_principalUnitLog_compat l place u

end

end ABCBridge.SourceQlCarrierMap
