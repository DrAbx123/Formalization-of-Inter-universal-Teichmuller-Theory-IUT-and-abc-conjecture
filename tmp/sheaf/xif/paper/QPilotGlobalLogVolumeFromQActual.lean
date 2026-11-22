import tmp.sheaf.xif.paper.QPilotGlobalObjectActual
import tmp.sheaf.xif.paper.QPilotZeroLocusDivisorActual
import LeanFormal.IUT.IUTIII.Corollary312.ArithmeticQPilotBaseChange
import LeanFormal.IUT.ABCBridge.Geometry.FinitePlaceCompletionNormTransport

/-! # Actual q-pilot log-volume from the q_v family

The presentation-level q-pilot object of QPilotGlobalObjectActual used the
prime divisor at the base bad place with exponent one.  The actual q_v zero
locus has multiplicity equal to the q_v exponent times the relative residue
degree from the F-place to its base Fmod place.  With that multiplicity, the
effectiveDivisorDegree is exactly the negative sum of the actual q_v log
magnitudes

  - sum_b log ||q_v(b)|| = sum_b (- localLogMagnitude (qVFamily b)).

This file constructs the corrected actual q-pilot divisor/object and proves that
formula using the production norm formula
qNorm_eq_residueNormBase_zpow and residueNormBase_eq_lower_pow.

No inequality is asserted.  No line-bundle/global-ideal identification is
claimed.  No toy/axiom/sorry. -/

noncomputable section
open scoped BigOperators
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace LeanFormal.IUT.XiFPaper.QPilotGlobalLogVolumeFromQActual

open LeanFormal.IUT
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.N8Closure.NativeInput
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.ArithmeticQPilotLogVolume
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.IUTII.Frobenioid.Example36.SourceModelBackend
open LeanFormal.IUT.XiFPaper.GlobalFrobenioidPresentationActual
open LeanFormal.IUT.XiFPaper.QPilotGlobalObjectActual
open LeanFormal.IUT.XiFPaper.QPilotZeroLocusDivisorActual
open LeanFormal.IUT.ArithmeticQPilotBaseChange
open scoped BigOperators

variable {l : PrimeGeFive}
variable (X : N8NativeInput l)

/-- The actual multiplicity of the q_v zero-locus divisor: q_v exponent times
the relative residue degree of the actual F-place over its base Fmod place. -/
noncomputable def qVEffectiveMultiplicity
    (b : Bad (nativePlaceSelection X.S)) : Nat :=
  (qVFamily X.S b).order *
    localResidueDegree (k := X.S.arithmetic.Fmod) ((nativeBadLift X.S).lift b)

/-- The corrected q_v zero-locus effective divisor in the presentation's cone,
with the actual q_v multiplicity. -/
noncomputable def qVZeroLocusQEffectiveDivisor
    (b : Bad (nativePlaceSelection X.S)) :
    EffectiveDivisor (BaseField X) :=
  (Finsupp.single (NumberFieldFinitePlace.underlyingPrime b.1)
      (qVEffectiveMultiplicity X b), 0)

/-- The finite global q-pilot effective divisor from the actual q_v family. -/
noncomputable def qVZeroLocusQEffectiveGlobal
    [Fintype (Bad (nativePlaceSelection X.S))] :
    EffectiveDivisor (BaseField X) :=
  ∑ b : Bad (nativePlaceSelection X.S), qVZeroLocusQEffectiveDivisor X b

/-- The actual global q-pilot object with q_v multiplicities. -/
noncomputable def qPilotQGlobalObject
    [Fintype (Bad (nativePlaceSelection X.S))] :
    Iut.SourceModelFrobenioid.Object
      (presentationDivisorMonoid X) where
  base := bottomPoint
  divisorClass :=
    Algebra.GrothendieckAddGroup.of (qVZeroLocusQEffectiveGlobal X)

/-- The actual q_v log-volume: the arithmetic degree of the q_v effective
divisor. -/
noncomputable def qPilotQGlobalLogVolume
    [Fintype (Bad (nativePlaceSelection X.S))] : Real :=
  -effectiveDivisorDegree X (qVZeroLocusQEffectiveGlobal X)

/-- Additivity of the arithmetic degree for a finite family of effective
divisors. -/
theorem effectiveDivisorDegree_finset_sum
    {ι : Type u} (s : Finset ι)
    (D : ι → EffectiveDivisor (BaseField X)) :
    effectiveDivisorDegree X (s.sum D) =
      s.sum (fun i => effectiveDivisorDegree X (D i)) := by
  classical
  refine Finset.induction_on s ?_ ?_
  · simp [effectiveDivisorDegree]
  · intro a s ha ih
    rw [Finset.sum_insert ha, Finset.sum_insert ha,
      effectiveDivisorDegree_add, ih]

/-- The degree of one q_v zero-locus divisor with multiplicity. -/
theorem effectiveDivisorDegree_qVZeroLocusQEffectiveDivisor
    (b : Bad (nativePlaceSelection X.S)) :
    effectiveDivisorDegree X (qVZeroLocusQEffectiveDivisor X b) =
      (qVEffectiveMultiplicity X b : Real) *
        Real.log (residueNormBase b.1) := by
  unfold effectiveDivisorDegree qVZeroLocusQEffectiveDivisor
  simp [residueNormBase]

/-- The actual q_v local magnitude, in terms of the base residue norm and the
relative residue degree. -/
theorem qVFamily_localLogMagnitude_eq
    (b : Bad (nativePlaceSelection X.S)) :
    localLogMagnitude (qVFamily X.S b) =
      (qVEffectiveMultiplicity X b : Real) * Real.log (residueNormBase b.1) := by
  have hupper := localLogMagnitude_eq_order_mul_log
    (parameter := qVFamily X.S b)
  have hbase := residueNormBase_eq_lower_pow
    (k := X.S.arithmetic.Fmod) ((nativeBadLift X.S).lift b)
  have hcomap : comap (k := X.S.arithmetic.Fmod) ((nativeBadLift X.S).lift b) = b.1 :=
    (nativeBadLift X.S).lift_comap b
  rw [hupper, hbase, hcomap, Real.log_pow]
  unfold qVEffectiveMultiplicity
  push_cast
  ring

/-- Actual q-pilot log-volume formula: the global q-pilot log-volume equals
minus the sum of the actual q_v log magnitudes. -/
theorem qPilotQGlobalLogVolume_eq_neg_sum_qVLogMagnitude
    [Fintype (Bad (nativePlaceSelection X.S))] :
    qPilotQGlobalLogVolume X =
      -∑ b : Bad (nativePlaceSelection X.S),
        localLogMagnitude (qVFamily X.S b) := by
  unfold qPilotQGlobalLogVolume qVZeroLocusQEffectiveGlobal
  rw [effectiveDivisorDegree_finset_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro b _
  rw [effectiveDivisorDegree_qVZeroLocusQEffectiveDivisor,
    qVFamily_localLogMagnitude_eq]

/-- The corrected q-pilot object's divisor class is the Grothendieck class of
the q_v effective divisor, and its log-volume is the negative q_v log sum. -/
theorem qPilotQGlobalObject_logVolume_link
    [Fintype (Bad (nativePlaceSelection X.S))] :
    (qPilotQGlobalObject X).divisorClass =
        Algebra.GrothendieckAddGroup.of (qVZeroLocusQEffectiveGlobal X) ∧
      qPilotQGlobalLogVolume X =
        -∑ b : Bad (nativePlaceSelection X.S),
          localLogMagnitude (qVFamily X.S b) :=
  ⟨rfl, qPilotQGlobalLogVolume_eq_neg_sum_qVLogMagnitude X⟩

end LeanFormal.IUT.XiFPaper.QPilotGlobalLogVolumeFromQActual

end
