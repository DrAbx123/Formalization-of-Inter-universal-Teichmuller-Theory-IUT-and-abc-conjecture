import tmp.sheaf.n8.closure.NativeBadLiftActual
import LeanFormal.IUT.IUTIV.Estimates.ArithmeticDivisorDegree
import LeanFormal.IUT.IUTIII.Corollary312.ArithmeticQPilotLogVolume

/-!
# Global q_v family and zero-locus divisor input data

IUT III, Definition 3.8, (i): the q-pilot object is the object of the global
realified Frobenioid determined by generators up to torsion of the splitting
monoid, i.e. concretely by the collection of the q_v for v in V_bad.  IUT III
introduces it as the arithmetic divisor determined by the zero locus of the
q_v.  The log-volume is written -|log q|.

This file constructs the actual input data available from the native source:

* qVFamily: for every native bad moduli place b, the actual q candidate in
  the completion of the actual finite F-place over b, obtained from clause B's
  actual SourceTateComparisonWitness;
* qVZeroLocusLocalDivisor: at each b, the actual one-place arithmetic divisor
  with coefficient q.exponent at that actual finite place (the zero locus of
  the local parameter q_v);
* qVZeroLocusGlobalDivisor: the finite sum of the local divisors, conditional
  on the source finiteness of the native bad set (the known NativeSourceAssembly
  badFinite gap).

This is actual q_v/zero-locus divisor input data, not a global realified
Frobenioid object and not the C^boxplus_mod realization.  The latter require
the global arithmetic line bundle/Frobenioid assembly and are recorded as the
exact remaining object-level gap.  No inequality is asserted.  No toy/True/
PUnit/axiom/sorry.  WRITE-ONLY; no local compile; queued.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 1000000

namespace LeanFormal.IUT.XiFPaper.QPilotZeroLocusDivisorActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.IUTIV.Estimates
open LeanFormal.IUT.N8Closure

universe u

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)

/-- The actual q_v at a native bad moduli place: the parameter of the actual
clause-B Tate comparison witness at the actual finite F-place over b. -/
noncomputable def qVFamily
    (b : Bad (nativePlaceSelection T)) :
    FinitePlaceQCandidate ((nativeBadLift T).lift b) :=
  (Classical.choice
    (T.clauseB.q_comparison ((nativeBadLift T).lift b)
      (by
        rw [(nativeBadLift T).lift_comap b]
        exact b.2))).parameter

/-- The q_v family is exactly the clause-B comparison parameter. -/
theorem qVFamily_eq_comparisonParameter
    (b : Bad (nativePlaceSelection T)) :
    qVFamily T b =
      (Classical.choice
        (T.clauseB.q_comparison ((nativeBadLift T).lift b)
          (by
            rw [(nativeBadLift T).lift_comap b]
            exact b.2))).parameter := rfl

/-- The zero-locus local divisor of q_v at b: the actual one-place arithmetic
divisor supported at the actual finite place over b, with the q parameter's
zero exponent. -/
noncomputable def qVZeroLocusLocalDivisor
    (b : Bad (nativePlaceSelection T)) :
    IUTIVArithmeticDivisor T.arithmetic.F :=
  Finsupp.single
    (IUTIVPlace.finite ((nativeBadLift T).lift b).maximalIdeal)
    ((qVFamily T b).exponent : ℝ)

/-- The local zero-locus divisor has the expected single-place support. -/
theorem qVZeroLocusLocalDivisor_apply
    (b : Bad (nativePlaceSelection T)) :
    qVZeroLocusLocalDivisor T b =
      Finsupp.single
        (IUTIVPlace.finite ((nativeBadLift T).lift b).maximalIdeal)
        ((qVFamily T b).exponent : ℝ) := rfl

/-- The actual q_v family together with its zero-locus local divisor data.  This
is the literal V_bad-indexed input data for the q-pilot arithmetic divisor. -/
structure QVZeroLocusInput where
  qV : (b : Bad (nativePlaceSelection T)) →
    FinitePlaceQCandidate ((nativeBadLift T).lift b)
  qV_eq : qV = qVFamily T
  zeroLocus : (b : Bad (nativePlaceSelection T)) →
    IUTIVArithmeticDivisor T.arithmetic.F
  zeroLocus_eq : zeroLocus = qVZeroLocusLocalDivisor T

/-- The actual V_bad-indexed q_v / zero-locus input data. -/
noncomputable def qVZeroLocusInput : QVZeroLocusInput T where
  qV := qVFamily T
  qV_eq := rfl
  zeroLocus := qVZeroLocusLocalDivisor T
  zeroLocus_eq := rfl

/-- The input's q_v family is the actual clause-B q family. -/
theorem qVZeroLocusInput_qV
    (b : Bad (nativePlaceSelection T)) :
    (qVZeroLocusInput T).qV b = qVFamily T b := rfl

/-- The input's local divisor is the actual local zero-locus divisor. -/
theorem qVZeroLocusInput_zeroLocus
    (b : Bad (nativePlaceSelection T)) :
    (qVZeroLocusInput T).zeroLocus b = qVZeroLocusLocalDivisor T b := rfl

/-- The global zero-locus arithmetic divisor: the finite sum of the local
q_v zero-locus divisors, conditional on the source finiteness of the native
bad set.  This is the actual arithmetic-divisor input for the global q-pilot
object; the global Frobenioid/line-bundle realization remains separate. -/
noncomputable def qVZeroLocusGlobalDivisor
    [Fintype (Bad (nativePlaceSelection T))] :
    IUTIVArithmeticDivisor T.arithmetic.F :=
  ∑ b : Bad (nativePlaceSelection T), qVZeroLocusLocalDivisor T b

/-- The global divisor is the finite sum of the local q_v zero-locus divisors. -/
theorem qVZeroLocusGlobalDivisor_eq_sum
    [Fintype (Bad (nativePlaceSelection T))] :
    qVZeroLocusGlobalDivisor T =
      ∑ b : Bad (nativePlaceSelection T), qVZeroLocusLocalDivisor T b := rfl

end LeanFormal.IUT.XiFPaper.QPilotZeroLocusDivisorActual
