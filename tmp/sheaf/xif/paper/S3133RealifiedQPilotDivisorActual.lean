import tmp.sheaf.xif.paper.GlobalRealifiedFrobenioidActual
import tmp.sheaf.xif.paper.QPilotGlobalDivisorOnCarrier
import tmp.sheaf.xif.paper.QPilotGlobalLogVolumeFromQActual
import LeanFormal.IUT.IUTIII.Corollary312.ArithmeticQPilotBaseChange

/-!
# The q-pilot arithmetic divisor on the actual global realified Frobenioid

Source: IUT III, §3, p. 16 (iut3.txt lines 880-893): the q-pilot object is the
object of the [global realified] Frobenioid determined by the arithmetic divisor
given by the zero locus of the elements q_v, v in V_bad.  IUT III, Definition
3.8, (i), pp. 112-113: the q-pilot object is determined by the q_v.

This file constructs the q-pilot arithmetic divisor directly in the actual
realified global divisor monoid of C^boxplus_mod (GlobalRealifiedFrobenioidActual,
QPilotGlobalDivisorOnCarrier): the product over V_bad of the actual zero-locus
prime divisors, each taken to the actual q_v multiplicity

  mult_b = order(q_v(b)) * localResidueDegree(F-place over b),

and proves that its realified arithmetic degree is the weighted sum of the actual
q_v multiplicities.  The log-volume of this divisor is computed in
S3133RealifiedQPilotLogVolumeActual and identified there with the actual q-pilot
log-volume -|log q|.

No inequality is asserted.  No toy/True/PUnit/axiom/sorry.  WRITE-ONLY.
-/

noncomputable section
open scoped BigOperators
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT.XiFPaper.S3133RealifiedQPilotDivisorActual

open LeanFormal.IUT
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.N8Closure.NativeInput
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.ArithmeticQPilotBaseChange
open LeanFormal.IUT.XiFPaper.GlobalRealifiedFrobenioidActual
open LeanFormal.IUT.XiFPaper.QPilotGlobalDivisorOnCarrier
open LeanFormal.IUT.XiFPaper.QPilotGlobalObjectActual
open LeanFormal.IUT.XiFPaper.QPilotGlobalLogVolumeFromQActual
open LeanFormal.IUT.XiFPaper.QPilotZeroLocusDivisorActual
open LeanFormal.IUT.NumberFieldFinitePlace

universe u

variable {l : PrimeGeFive}
variable (X : N8NativeInput l)

/-- The actual q-pilot arithmetic divisor in the realified global divisor monoid
of C^boxplus_mod: the product over V_bad of the actual zero-locus prime divisors
with the actual q_v multiplicities. -/
noncomputable def qPilotRealifiedDivisor
    [Fintype (Bad (nativePlaceSelection X.S))] :
    GlobalDivisorMonoid (X := X) :=
  ∏ b : Bad (nativePlaceSelection X.S),
    (qVZeroLocusPrimeDivisor X b) ^ (qVEffectiveMultiplicity X b)

/-- Each q-pilot realified factor is the actual base-bad-place prime divisor. -/
theorem qPilotRealifiedDivisor_factor
    (b : Bad (nativePlaceSelection X.S)) :
    qVZeroLocusPrimeDivisor X b =
      globalPrimeDivisor (X := X) (NumberFieldPlace.finite b.1) := rfl

/-- The q-pilot realified divisor is the product of the actual base-prime
divisors with the actual q_v multiplicities. -/
theorem qPilotRealifiedDivisor_eq_prod_factor
    [Fintype (Bad (nativePlaceSelection X.S))] :
    qPilotRealifiedDivisor X =
      ∏ b : Bad (nativePlaceSelection X.S),
        (globalPrimeDivisor (X := X) (NumberFieldPlace.finite b.1)) ^
          (qVEffectiveMultiplicity X b) := rfl

/-- The arithmetic weight of the base bad place is the actual residue norm base. -/
theorem globalPrimeWeight_finite_eq
    (b : Bad (nativePlaceSelection X.S)) :
    globalPrimeWeight (X := X) (NumberFieldPlace.finite b.1) =
      Real.log (residueNormBase b.1) := by
  simp [globalPrimeWeight, residueNormBase]

/-- The realified degree of a power of an actual prime divisor: the exponent
times the arithmetic weight. -/
theorem globalDegree_primeDivisor_pow
    (v : GlobalPrimeIndex (X := X)) (n : Nat) :
    globalDegree (X := X) (globalPrimeDivisor (X := X) v ^ n) =
      Multiplicative.ofAdd
        ((n : Real) * globalPrimeWeight (X := X) v) := by
  rw [map_pow, globalDegree_primeDivisor]
  rw [← ofAdd_nsmul]
  congr 1
  rw [nsmul_eq_mul]

/-- The realified degree of the actual q-pilot divisor is the weighted sum of the
actual q_v multiplicities. -/
theorem globalDegree_qPilotRealifiedDivisor
    [Fintype (Bad (nativePlaceSelection X.S))] :
    globalDegree (X := X) (qPilotRealifiedDivisor X) =
      Multiplicative.ofAdd
        (∑ b : Bad (nativePlaceSelection X.S),
          (qVEffectiveMultiplicity X b : Real) *
            globalPrimeWeight (X := X) (NumberFieldPlace.finite b.1)) := by
  unfold qPilotRealifiedDivisor
  rw [map_prod]
  trans (∏ b : Bad (nativePlaceSelection X.S),
      Multiplicative.ofAdd
        ((qVEffectiveMultiplicity X b : Real) *
          globalPrimeWeight (X := X) (NumberFieldPlace.finite b.1)))
  · apply Finset.prod_congr rfl
    intro b _
    exact globalDegree_primeDivisor_pow X (NumberFieldPlace.finite b.1)
      (qVEffectiveMultiplicity X b)
  · exact (ofAdd_sum (Finset.univ : Finset (Bad (nativePlaceSelection X.S)))
      (fun b => (qVEffectiveMultiplicity X b : Real) *
        globalPrimeWeight (X := X) (NumberFieldPlace.finite b.1))).symm

end LeanFormal.IUT.XiFPaper.S3133RealifiedQPilotDivisorActual
