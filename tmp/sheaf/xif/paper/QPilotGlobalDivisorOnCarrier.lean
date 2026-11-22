import tmp.sheaf.xif.paper.GlobalRealifiedFrobenioidActual
import tmp.sheaf.xif.paper.QPilotZeroLocusDivisorActual
import tmp.sheaf.n8.closure.NativeBadLiftActual
import LeanFormal.IUT.IUTI.InitialTheta.SourcePlacePartitionReduction

/-!
# q_v zero-locus divisor on the global realified Frobenioid carrier

This file uses the actual C^boxplus_mod carrier layer constructed by qside in
GlobalRealifiedFrobenioidActual:

  GlobalPrimeIndex, GlobalDivisorGroup, GlobalDivisorMonoid,
  globalPrimeDivisor, globalDegree, globalRealifiedFrobenioidCarrier.

For the native V_bad family it constructs the literal q_v zero-locus input on
that carrier:

* the actual q_v is the clause-B q candidate at the actual F-place over b
  (QPilotZeroLocusDivisorActual.qVFamily);
* the zero-locus prime divisor is the actual prime divisor at the base Fmod
  place b (the q-local-parameter zero locus in C^boxplus_mod);
* qVZeroLocusCarrierFamily is the resulting V_bad-indexed family in the global
  realified divisor monoid;
* qVZeroLocusCarrierGlobal is its finite product, conditional on the source
  finiteness of the native bad set.

This is the q_v/zero-locus divisor input on the actual carrier.  It does not
identify this divisor with an arithmetic line bundle, a global ideal, or a full
FrobenioidPresentation; those remain exact object-level gaps.  No inequality is
asserted.  No toy/True/PUnit/axiom/sorry.  WRITE-ONLY; no local compile; queued.
-/

noncomputable section
open scoped BigOperators
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT.XiFPaper.QPilotGlobalDivisorOnCarrier

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.N8Closure.NativeInput
open LeanFormal.IUT.XiFPaper.GlobalRealifiedFrobenioidActual
open LeanFormal.IUT.XiFPaper.QPilotZeroLocusDivisorActual
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.NumberFieldFinitePlace

universe u

variable {l : PrimeGeFive}
variable (X : N8NativeInput l)

/-- The base Fmod place of a native bad moduli place, as an actual global prime
of C^boxplus_mod. -/
noncomputable def qVCarrierBasePrime
    (b : Bad (nativePlaceSelection X.S)) :
    GlobalPrimeIndex (X := X) :=
  NumberFieldPlace.finite b.1

/-- The q_v local parameter zero locus in the global realified divisor monoid:
the actual prime divisor at the base bad place. -/
noncomputable def qVZeroLocusPrimeDivisor
    (b : Bad (nativePlaceSelection X.S)) :
    GlobalDivisorMonoid (X := X) :=
  globalPrimeDivisor (X := X) (qVCarrierBasePrime X b)

/-- The actual q_v family together with its zero-locus prime divisor on the
C^boxplus_mod carrier. -/
structure QVCarrierInput where
  qV : (b : Bad (nativePlaceSelection X.S)) →
    FinitePlaceQCandidate ((nativeBadLift X.S).lift b)
  qV_eq : qV = qVFamily X.S
  zeroLocus : (b : Bad (nativePlaceSelection X.S)) →
    GlobalDivisorMonoid (X := X)
  zeroLocus_eq : zeroLocus = qVZeroLocusPrimeDivisor X

/-- The actual V_bad-indexed q_v / zero-locus input on the global carrier. -/
noncomputable def qVCarrierInput : QVCarrierInput X where
  qV := qVFamily X.S
  qV_eq := rfl
  zeroLocus := qVZeroLocusPrimeDivisor X
  zeroLocus_eq := rfl

/-- The input q_v at b is the actual clause-B q candidate at the actual lift. -/
theorem qVCarrierInput_qV
    (b : Bad (nativePlaceSelection X.S)) :
    (qVCarrierInput X).qV b = qVFamily X.S b := rfl

/-- The input zero-locus divisor at b is the actual prime divisor at the base
bad place. -/
theorem qVCarrierInput_zeroLocus
    (b : Bad (nativePlaceSelection X.S)) :
    (qVCarrierInput X).zeroLocus b =
      globalPrimeDivisor (X := X) (qVCarrierBasePrime X b) := rfl

/-- The V_bad-indexed zero-locus family in the global realified divisor monoid. -/
noncomputable def qVZeroLocusCarrierFamily :
    (b : Bad (nativePlaceSelection X.S)) →
      GlobalDivisorMonoid (X := X) :=
  qVZeroLocusPrimeDivisor X

/-- The finite product of the zero-locus prime divisors, conditional on the
source finiteness of the native bad set. -/
noncomputable def qVZeroLocusCarrierGlobal
    [Fintype (Bad (nativePlaceSelection X.S))] :
    GlobalDivisorMonoid (X := X) :=
  ∏ b : Bad (nativePlaceSelection X.S), qVZeroLocusPrimeDivisor X b

/-- The global zero-locus divisor is the finite product of the local prime
divisors. -/
theorem qVZeroLocusCarrierGlobal_eq_product
    [Fintype (Bad (nativePlaceSelection X.S))] :
    qVZeroLocusCarrierGlobal X =
      ∏ b : Bad (nativePlaceSelection X.S),
        qVZeroLocusPrimeDivisor X b := rfl

/-- The base prime map is the actual finite place of the bad moduli place. -/
theorem qVCarrierBasePrime_eq
    (b : Bad (nativePlaceSelection X.S)) :
    qVCarrierBasePrime X b = NumberFieldPlace.finite b.1 := rfl

end LeanFormal.IUT.XiFPaper.QPilotGlobalDivisorOnCarrier
