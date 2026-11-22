import tmp.sheaf.xif.paper.S2040RootStackThetaPilotActual
import tmp.sheaf.xif.paper.S2032R6GeneratorActual
import LeanFormal.IUT.ABCBridge.Geometry.FinitePlaceSourceAlgebraicClosure

/-! # S2040 paper O^×/O^×μ carrier from the actual local model

Uses S1978's actual local O^× / O^×μ and S2032's actual O^◃ / q_v Q_p-model.
The S1487 source-strip unit carrier is not used (S1967 proves it is unit-trivial).
The Q_p model is not yet identified with the completion carrier at qVPlace; that
completion identification is recorded as exact missing data. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 8000000

namespace LeanFormal.IUT.XiFPaper.S2040PaperOUnitsMuAmbientActual

open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S1978LocalFieldOCarrierActual
open LeanFormal.IUT.XiFPaper.S2032R6GeneratorActual
open LeanFormal.IUT.XiFPaper.S1895OIdentificationsActual
open LeanFormal.IUT.XiFPaper.S2040RootStackThetaPilotActual
open LeanFormal.IUT.XiFPaper.S1951KummerEvaluationSquareActual
open LeanFormal.IUT.XiFPaper.S1968QVDeterminedQPilotActual
open LeanFormal.IUT.XiFPaper.S1979QPilotStripFromDivisorActual
open LeanFormal.IUT.XiFPaper.S1960QPilotAnchorActual
open LeanFormal.IUT.XiFPaper.S1487OQPilotScalarEqualityActual
open LeanFormal.IUT.XiFPaper.S1527OOrderEqualityActual
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.NumberFieldFinitePlace

local instance s2040FivePrime : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
open LeanFormal.IUT.XiFPaper.TwoLthRootKummerActual
open LeanFormal.IUT.LocalFieldIntegralUnits
open LeanFormal.IUT.LocalFieldLogarithm
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction

universe u

/-- Actual local O^×/O^×μ carrier at a rational prime, from S1978. -/
structure S2040LocalOUnitsCarrier (p : Nat) [Fact (Nat.Prime p)] where
  OUnits : Type := LocalOFieldUnits p
  OUnitsMu : Type := LocalOFieldUnitsMu p
  OUnits_nontrivial : Nontrivial OUnits
  OUnitsMu_nontrivial : Nontrivial OUnitsMu

/-- The actual local O^× is nontrivial. -/
theorem s2040LocalOUnits_nontrivial (p : Nat) [Fact (Nat.Prime p)] :
    Nontrivial (LocalOFieldUnits p) :=
  ⟨⟨localOFieldUnit p, 1, localOFieldUnit_ne_one p⟩⟩

/-- The actual local O^×μ quotient is nontrivial. -/
theorem s2040LocalOUnitsMu_nontrivial (p : Nat) [Fact (Nat.Prime p)] :
    Nontrivial (LocalOFieldUnitsMu p) :=
  ⟨⟨TimesMuQuotient.quotientMap (localOFieldUnit p), 1,
    LocalOFieldUnitsMu_nontrivial p⟩⟩

/-- The actual local carrier at p = 5. -/
noncomputable def s2040LocalOUnitsCarrierFive :
    S2040LocalOUnitsCarrier 5 where
  OUnits_nontrivial := s2040LocalOUnits_nontrivial 5
  OUnitsMu_nontrivial := s2040LocalOUnitsMu_nontrivial 5

/-- Actual local O^◃ element q_v and its realified value, from S2032. -/
structure S2040LocalQVRealification (D : S1895PaperInput)
    (b : (S1960QPilotAnchorActual.paperInput D).initial.badPlaces) where
  qv : LocalOFieldIntegral 5 := localOFieldQParameter D b
  qv_norm :
      ‖(localOFieldQParameter D b : AlgebraicClosure ℚ_[5])‖ = paperQV D b :=
    localOFieldQParameter_norm D b
  qv_norm_lt_one :
      ‖(localOFieldQParameter D b : AlgebraicClosure ℚ_[5])‖ < 1 :=
    localOFieldQParameter_norm_lt_one D b
  qv_realified :
    Multiplicative.toAdd (localOFieldNormLog 5 (localOFieldQParameter D b)) =
      qPilotGeneratorValue D b :=
    localOFieldNormLog_qParameter D b

/-- The actual local Q_p q_v realification data. -/
noncomputable def s2040LocalQVRealification (D : S1895PaperInput)
    (b : (S1960QPilotAnchorActual.paperInput D).initial.badPlaces) :
    S2040LocalQVRealification D b where
  qv := localOFieldQParameter D b

theorem s2040LocalQV_norm (D : S1895PaperInput)
    (b : (S1960QPilotAnchorActual.paperInput D).initial.badPlaces) :
    ‖(localOFieldQParameter D b : AlgebraicClosure ℚ_[5])‖ = paperQV D b :=
  (s2040LocalQVRealification D b).qv_norm

/-- Exact missing completion identification: the actual Q_p local carrier is not
yet identified with the units of the algebraic closure of the completion at
`qVPlace T b`.  No inhabitant is asserted. -/
structure S2040CompletionLocalIdentification
    (T : SourceNativeInitialThetaData.{0} l)
    (b : Bad (nativePlaceSelection T)) where
  p : Nat
  hprime : Fact (Nat.Prime p)
  /-- The actual completion **integral** units, not the all-units carrier. -/
  completionUnitEquiv :
    (Integers (SourceAlgebraicClosure (qVPlace (l := l) T b)))ˣ ≃*
      LocalOFieldUnits p
  /-- Genuine norm compatibility of the integral-unit identification. -/
  norm_compatible :
    ∀ u : (Integers (SourceAlgebraicClosure (qVPlace (l := l) T b)))ˣ,
      ‖((completionUnitEquiv u : LocalOFieldUnits p) : AlgebraicClosure ℚ_[p])‖ =
        ‖((u : Integers (SourceAlgebraicClosure (qVPlace (l := l) T b))) :
          SourceAlgebraicClosure (qVPlace (l := l) T b))‖

noncomputable def s2040PaperOUnitsMuAmbientOfCompletion
    (T : SourceNativeInitialThetaData.{0} l)
    (b : Bad (nativePlaceSelection T))
    (ci : S2040CompletionLocalIdentification T b) :
    S2040PaperOUnitsMuAmbient where
  OUnits := @LocalOFieldUnits ci.p ci.hprime
  OUnitsMu := @LocalOFieldUnitsMu ci.p ci.hprime
  ambientValues := @LocalOFieldIntegral ci.p ci.hprime
  quotient_compatible := by
    letI := ci.hprime
    exact Nonempty (Nontrivial (LocalOFieldUnitsMu ci.p))
  ambient_values_paper := by
    letI := ci.hprime
    exact Nonempty (LocalOFieldIntegral ci.p)
  OUnits_nontrivial := by
    letI := ci.hprime
    exact Nonempty (Nontrivial (LocalOFieldUnits ci.p))

#check S2040LocalOUnitsCarrier
#check s2040LocalOUnitsCarrierFive
#check S2040LocalQVRealification
#check S2040CompletionLocalIdentification
#check s2040PaperOUnitsMuAmbientOfCompletion

end LeanFormal.IUT.XiFPaper.S2040PaperOUnitsMuAmbientActual
end
