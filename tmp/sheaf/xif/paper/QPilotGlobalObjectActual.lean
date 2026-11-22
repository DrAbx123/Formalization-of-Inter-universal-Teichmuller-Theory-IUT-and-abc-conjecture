import tmp.sheaf.xif.paper.GlobalFrobenioidPresentationActual
import tmp.sheaf.xif.paper.QPilotGlobalDivisorOnCarrier
import LeanFormal.IUT.IUTII.Frobenioid.Example36SourceModelBackend
import Iut.Foundations.SourceModelFrobenioid

/-! # Actual global q-pilot object on the FrobenioidPresentation

The actual global model FrobenioidPresentation is
Example36.SourceModelBackend.numberFieldFrobenioidPresentation Fmod
(GlobalFrobenioidPresentationActual).  Its DivisorialMonoidOn is
globalDivisorMonoidOn Fmod with carrier EffectiveDivisor Fmod.

kummer's q_v family gives, for each bad base Fmod place b, the actual prime
divisor at the underlying HeightOneSpectrum.  This file maps that zero-locus
prime divisor into the actual EffectiveDivisor cone of the presentation, forms
the finite product over V_bad (conditional on Fintype Bad), and constructs the
actual global q-pilot object of SourceModelFrobenioid.Object with that effective
divisor class.

The arithmetic degree/log-volume data is the actual weighted effective-divisor
degree of this object.  No inequality is asserted; no line-bundle/global-ideal
identification is claimed.  No toy/axiom/sorry. -/

noncomputable section
open scoped BigOperators
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace LeanFormal.IUT.XiFPaper.QPilotGlobalObjectActual

open LeanFormal.IUT
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.N8Closure.NativeInput
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.XiFPaper.GlobalFrobenioidPresentationActual
open LeanFormal.IUT.XiFPaper.QPilotGlobalDivisorOnCarrier
open LeanFormal.IUT.IUTII.Frobenioid.Example36.SourceModelBackend
open LeanFormal.IUT.IUTII.Frobenioid.Example36

universe u

variable {l : PrimeGeFive}
variable (X : N8NativeInput l)

/-- The actual base Fmod number field. -/
abbrev BaseField : Type := X.S.arithmetic.Fmod

/-- The effective-divisor prime at a bad base place: the underlying height-one
spectrum generator with exponent one, and zero archimedean coordinate. -/
noncomputable def qVZeroLocusEffectiveDivisor
    (b : Bad (nativePlaceSelection X.S)) :
    EffectiveDivisor (BaseField X) :=
  (Finsupp.single
      (NumberFieldFinitePlace.underlyingPrime b.1) 1,
    0)

/-- The q_v zero-locus effective divisor is supported at the underlying finite
prime of b. -/
theorem qVZeroLocusEffectiveDivisor_fst
    (b : Bad (nativePlaceSelection X.S)) :
    (qVZeroLocusEffectiveDivisor X b).1 =
      Finsupp.single (NumberFieldFinitePlace.underlyingPrime b.1) 1 := rfl

/-- The q_v zero-locus effective divisor has zero archimedean coordinate. -/
theorem qVZeroLocusEffectiveDivisor_snd
    (b : Bad (nativePlaceSelection X.S)) :
    (qVZeroLocusEffectiveDivisor X b).2 = 0 := rfl

/-- The finite product of the zero-locus effective divisors over V_bad. -/
noncomputable def qVZeroLocusEffectiveGlobal
    [Fintype (Bad (nativePlaceSelection X.S))] :
    EffectiveDivisor (BaseField X) :=
  ∑ b : Bad (nativePlaceSelection X.S), qVZeroLocusEffectiveDivisor X b

/-- The global effective divisor is the finite sum over the bad places. -/
theorem qVZeroLocusEffectiveGlobal_eq_sum
    [Fintype (Bad (nativePlaceSelection X.S))] :
    qVZeroLocusEffectiveGlobal X =
      ∑ b : Bad (nativePlaceSelection X.S), qVZeroLocusEffectiveDivisor X b := rfl

/-- The actual DivisorialMonoidOn carried by the presentation. -/
abbrev presentationDivisorMonoid :
    Iut.DivisorialMonoidOn (BottomBase.{0}) BottomFSM :=
  globalEffectiveDivisorMonoidActual (K := BaseField X)

/-- The actual global q-pilot object in the model Frobenioid: the unique base
object with divisor class equal to the effective zero-locus divisor. -/
noncomputable def qPilotGlobalObject
    [Fintype (Bad (nativePlaceSelection X.S))] :
    Iut.SourceModelFrobenioid.Object
      (presentationDivisorMonoid X) where
  base := bottomPoint
  divisorClass :=
    Algebra.GrothendieckAddGroup.of (qVZeroLocusEffectiveGlobal X)

/-- The q-pilot object's base is the unique bottom base object. -/
theorem qPilotGlobalObject_base
    [Fintype (Bad (nativePlaceSelection X.S))] :
    (qPilotGlobalObject X).base = bottomPoint := rfl

/-- The q-pilot object's divisor class is the effective zero-locus divisor. -/
theorem qPilotGlobalObject_divisorClass
    [Fintype (Bad (nativePlaceSelection X.S))] :
    (qPilotGlobalObject X).divisorClass =
      Algebra.GrothendieckAddGroup.of (qVZeroLocusEffectiveGlobal X) := rfl

/-- Actual arithmetic degree on the effective divisor cone: finite-place
log-absolute-norm sum plus archimedean NNReal coordinates. -/
noncomputable def effectiveDivisorDegree
    (D : EffectiveDivisor (BaseField X)) : Real :=
  D.1.sum (fun v n =>
      (n : Real) * Real.log (Ideal.absNorm v.asIdeal : Real)) +
    ∑ w : NumberField.InfinitePlace (BaseField X), (D.2 w : Real)

/-- The actual q-pilot log-volume/degree value: the arithmetic degree of the
global zero-locus effective divisor. -/
noncomputable def qPilotGlobalLogVolume
    [Fintype (Bad (nativePlaceSelection X.S))] : Real :=
  effectiveDivisorDegree X (qVZeroLocusEffectiveGlobal X)

/-- The q-pilot log-volume is the arithmetic degree of its effective divisor. -/
theorem qPilotGlobalLogVolume_eq_degree
    [Fintype (Bad (nativePlaceSelection X.S))] :
    qPilotGlobalLogVolume X =
      effectiveDivisorDegree X (qVZeroLocusEffectiveGlobal X) := rfl

/-- Link the actual q-pilot effective divisor to kummer's zero-locus prime
divisor on the realified carrier: both are supported at the same base bad
place; the effective-divisor map records the nonnegative exponent-one lift. -/
theorem qPilotGlobalObject_divisor_link
    (b : Bad (nativePlaceSelection X.S)) :
    (qVZeroLocusEffectiveDivisor X b).1 =
      Finsupp.single (NumberFieldFinitePlace.underlyingPrime b.1) 1 := rfl

/-- Additivity of the arithmetic degree on the effective divisor cone. -/
theorem effectiveDivisorDegree_add
    (D E : EffectiveDivisor (BaseField X)) :
    effectiveDivisorDegree X (D + E) =
      effectiveDivisorDegree X D + effectiveDivisorDegree X E := by
  classical
  unfold effectiveDivisorDegree
  simp only [Prod.fst_add, Prod.snd_add, Pi.add_apply]
  rw [Finsupp.sum_add_index (fun v _ => by simp)
    (fun v _ a b => by push_cast; ring)]
  simp [Finset.sum_add_distrib]
  ring

/-- The degree of a single q_v zero-locus divisor is the log absolute norm of
the underlying height-one prime. -/
theorem effectiveDivisorDegree_qVZeroLocusEffectiveDivisor
    (b : Bad (nativePlaceSelection X.S)) :
    effectiveDivisorDegree X (qVZeroLocusEffectiveDivisor X b) =
      Real.log (Ideal.absNorm
        (NumberFieldFinitePlace.underlyingPrime b.1).asIdeal : Real) := by
  unfold effectiveDivisorDegree qVZeroLocusEffectiveDivisor
  simp

/-- Degree of a finite sum of q_v zero-locus divisors is the sum of the
individual degrees. -/
theorem effectiveDivisorDegree_sum_qVZeroLocus
    [Fintype (Bad (nativePlaceSelection X.S))] :
    effectiveDivisorDegree X
        (∑ b : Bad (nativePlaceSelection X.S),
          qVZeroLocusEffectiveDivisor X b) =
      ∑ b : Bad (nativePlaceSelection X.S),
        effectiveDivisorDegree X (qVZeroLocusEffectiveDivisor X b) := by
  classical
  refine Finset.induction_on
    (Finset.univ : Finset (Bad (nativePlaceSelection X.S))) ?_ ?_
  · simp [effectiveDivisorDegree]
  · intro a s ha ih
    rw [Finset.sum_insert ha, Finset.sum_insert ha,
      effectiveDivisorDegree_add, ih]

/-- Actual log-volume formula: the q-pilot global log-volume equals the sum
over the bad places of the log absolute norm of the underlying prime. -/
theorem qPilotGlobalLogVolume_eq_sum_log_absNorm
    [Fintype (Bad (nativePlaceSelection X.S))] :
    qPilotGlobalLogVolume X =
      ∑ b : Bad (nativePlaceSelection X.S),
        Real.log (Ideal.absNorm
          (NumberFieldFinitePlace.underlyingPrime b.1).asIdeal : Real) := by
  rw [qPilotGlobalLogVolume_eq_degree]
  unfold qVZeroLocusEffectiveGlobal
  rw [effectiveDivisorDegree_sum_qVZeroLocus]
  exact Finset.sum_congr rfl (fun b _ =>
    effectiveDivisorDegree_qVZeroLocusEffectiveDivisor X b)

/-- The q-pilot object's divisor class is the Grothendieck class of the same
effective divisor whose degree is the q-pilot global log-volume.  This links
qPilotGlobalObject_divisor_link to the actual log-volume formula. -/
theorem qPilotGlobalObject_logVolume_link
    [Fintype (Bad (nativePlaceSelection X.S))] :
    (qPilotGlobalObject X).divisorClass =
        Algebra.GrothendieckAddGroup.of (qVZeroLocusEffectiveGlobal X) ∧
      qPilotGlobalLogVolume X =
        effectiveDivisorDegree X (qVZeroLocusEffectiveGlobal X) :=
  ⟨qPilotGlobalObject_divisorClass X, qPilotGlobalLogVolume_eq_degree X⟩

/-! ## Boundary

Constructed actually:
* the q_v zero-locus effective divisor in the presentation's EffectiveDivisor
  cone;
* its finite V_bad product;
* the global q-pilot object of SourceModelFrobenioid.Object with that divisor
  class;
* the arithmetic degree/log-volume value of that effective divisor.

Not asserted:
* identification of this effective divisor with a global arithmetic line bundle
  or global ideal family;
* any source q descent beyond kummer's clause-B q_v family;
* any inequality/equality between this log-volume and -|log q|.

These remain separate object-level identifications. -/

end LeanFormal.IUT.XiFPaper.QPilotGlobalObjectActual

end