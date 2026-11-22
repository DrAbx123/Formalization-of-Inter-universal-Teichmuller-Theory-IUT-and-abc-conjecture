import LeanFormal.IUT.Foundations.AlgebraicGeometry.LogShellQuotientConsumer
import LeanFormal.IUT.ABCBridge.Geometry.FinitePlaceCommonPrimeCompletion

set_option linter.unusedSectionVars false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1600000

noncomputable section

namespace LeanFormal.IUT.Foundations.LocalFields.LogShellQuotientGeneralPlace

universe u

open LeanFormal.IUT.LocalFieldIntegralUnits
open LeanFormal.IUT.LocalFieldLogarithm
open LeanFormal.IUT.Foundations.LocalFields.LogShellQuotientConsumer
open LeanFormal.IUT.NumberFieldFinitePlace

variable {F : Type u} [Field F] [NumberField F] {p : ℕ} [Fact p.Prime]

/-- Generalization of the actual integral log-shell integer quotient consumer to
an arbitrary finite place at a fixed rational prime `p`, using the production
common-prime completion and quotient/index arithmetic. -/
noncomputable def generalPlaceLogShellQuotientConsumer
    (place : FinitePlaceAtPrime F p) :
    LogShellIntegerQuotientConsumer (K := CommonPrimeCompletion place) :=
  logShellIntegerQuotientConsumer (K := CommonPrimeCompletion place) (p := p)

theorem generalPlaceLogShellQuotientConsumer_finite
    (place : FinitePlaceAtPrime F p) :
    Finite (generalPlaceLogShellQuotientConsumer place).quotient :=
  (generalPlaceLogShellQuotientConsumer place).finite

theorem generalPlaceLogShellQuotientConsumer_map_surjective
    (place : FinitePlaceAtPrime F p) :
    Function.Surjective (generalPlaceLogShellQuotientConsumer place).quotientMap :=
  (generalPlaceLogShellQuotientConsumer place).quotientMap_surjective

theorem generalPlaceLogShellQuotientConsumer_index_pos
    (place : FinitePlaceAtPrime F p) :
    0 < (generalPlaceLogShellQuotientConsumer place).index :=
  (generalPlaceLogShellQuotientConsumer place).index_pos

end LeanFormal.IUT.Foundations.LocalFields.LogShellQuotientGeneralPlace
end