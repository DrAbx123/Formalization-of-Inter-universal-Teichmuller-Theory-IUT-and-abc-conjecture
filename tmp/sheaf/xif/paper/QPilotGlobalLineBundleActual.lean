import tmp.sheaf.xif.paper.GlobalRealifiedFrobenioidActual
import tmp.sheaf.xif.paper.QPilotGlobalDivisorOnCarrier
import tmp.sheaf.xif.paper.ArithmeticLineBundleActual

/-!
# Global q-pilot arithmetic line bundle / global ideal on C^boxplus_mod

IUT III, Definition 3.8, (i): the q-pilot object is determined by the q_v for
v in V_bad; IUT III, §3 (p. 17) writes it as the arithmetic divisor determined
by the zero locus of the q_v, with log-volume -|log q|.

This file constructs, on qside's actual carrier GlobalRealifiedFrobenioidActual:

* qPilotGlobalIdeal: the global ideal of O_Fmod obtained as the product of the
  prime ideals at the actual base Fmod places of the native V_bad family;
* qPilotGlobalLineBundle: its actual fractional-ideal line bundle in Fmod;
* QPilotGlobalLineBundleRealization: the actual q_v family, zero-locus divisor
  family, global divisor, global ideal and global line bundle, with the
  definitional line-bundle/ideal equality.

The q_v family is the actual clause-B q candidate at the actual F-place over
each bad moduli place; the zero-locus prime divisor is at the base Fmod place.
This is the literal zero-locus arithmetic line bundle construction.  It does
not construct the (1,0) q-pilot F^boxplus-triangleright-x-mu prime-strip, the
log-Kummer representation on 1,circ U_Q, or the full C^boxplus_mod q-pilot
realization; those are exact remaining object-level fields.

No inequality is asserted.  No toy/True/PUnit/axiom/sorry.  WRITE-ONLY; no
local compile; queued.
-/

noncomputable section
open scoped BigOperators
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT.XiFPaper.QPilotGlobalLineBundleActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.N8Closure.NativeInput
open LeanFormal.IUT.XiFPaper.GlobalRealifiedFrobenioidActual
open LeanFormal.IUT.XiFPaper.QPilotZeroLocusDivisorActual
open LeanFormal.IUT.XiFPaper.QPilotGlobalDivisorOnCarrier
open LeanFormal.IUT.XiFPaperArithmeticLineBundle

universe u

variable {l : PrimeGeFive}
variable (X : N8NativeInput l)

/-- The actual global q-pilot ideal: the product of the prime ideals at the
base Fmod places of the native V_bad family. -/
noncomputable def qPilotGlobalIdeal
    [Fintype (Bad (nativePlaceSelection X.S))] :
    Ideal (NumberField.RingOfIntegers X.S.arithmetic.Fmod) :=
  ∏ b : Bad (nativePlaceSelection X.S), b.1.maximalIdeal.asIdeal

/-- The actual global q-pilot arithmetic line bundle: the inverse of the
zero-locus fractional ideal, i.e. O(-D) for the zero-locus divisor D.  This is
the line bundle whose log-volume is -|log q|; no inequality is asserted. -/
noncomputable def qPilotGlobalLineBundle
    [Fintype (Bad (nativePlaceSelection X.S))] :
    FractionalIdeal
      (nonZeroDivisors (NumberField.RingOfIntegers X.S.arithmetic.Fmod))
      X.S.arithmetic.Fmod :=
  (qPilotGlobalIdeal X : FractionalIdeal
    (nonZeroDivisors (NumberField.RingOfIntegers X.S.arithmetic.Fmod))
    X.S.arithmetic.Fmod)⁻¹

/-- The global q-pilot line bundle is exactly the inverse of the zero-locus
fractional ideal. -/
theorem qPilotGlobalLineBundle_eq_inv_ideal
    [Fintype (Bad (nativePlaceSelection X.S))] :
    qPilotGlobalLineBundle X =
      (qPilotGlobalIdeal X : FractionalIdeal
        (nonZeroDivisors (NumberField.RingOfIntegers X.S.arithmetic.Fmod))
        X.S.arithmetic.Fmod)⁻¹ := rfl

/-- The actual global q-pilot line-bundle realization data built from the q_v
family and its zero-locus divisor. -/
structure QPilotGlobalLineBundleRealization
    [Fintype (Bad (nativePlaceSelection X.S))] where
  /-- The actual q_v family from clause B at the actual F-lifts. -/
  qV : (b : Bad (nativePlaceSelection X.S)) →
    FinitePlaceQCandidate ((nativeBadLift X.S).lift b)
  /-- The actual zero-locus prime divisor family on the global carrier. -/
  zeroLocus : (b : Bad (nativePlaceSelection X.S)) →
    GlobalDivisorMonoid (X := X)
  /-- The finite product of the zero-locus prime divisors. -/
  globalDivisor : GlobalDivisorMonoid (X := X)
  /-- The actual global ideal. -/
  ideal : Ideal (NumberField.RingOfIntegers X.S.arithmetic.Fmod)
  /-- The actual global fractional-ideal line bundle. -/
  lineBundle : FractionalIdeal
    (nonZeroDivisors (NumberField.RingOfIntegers X.S.arithmetic.Fmod))
    X.S.arithmetic.Fmod
  /-- The line bundle is O(-D), the inverse of the zero-locus fractional ideal. -/
  lineBundle_eq : lineBundle =
    (ideal : FractionalIdeal
      (nonZeroDivisors (NumberField.RingOfIntegers X.S.arithmetic.Fmod))
      X.S.arithmetic.Fmod)⁻¹

/-- The actual global q-pilot line-bundle realization from the native q_v family
and the zero-locus divisor on the C^boxplus_mod carrier. -/
noncomputable def qPilotGlobalLineBundleRealization
    [Fintype (Bad (nativePlaceSelection X.S))] :
    QPilotGlobalLineBundleRealization X where
  qV := qVFamily X.S
  zeroLocus := qVZeroLocusPrimeDivisor X
  globalDivisor := qVZeroLocusCarrierGlobal X
  ideal := qPilotGlobalIdeal X
  lineBundle := qPilotGlobalLineBundle X
  lineBundle_eq := rfl

/-- The realized global ideal is the product of the base bad prime ideals. -/
theorem qPilotGlobalLineBundleRealization_ideal
    [Fintype (Bad (nativePlaceSelection X.S))] :
    (qPilotGlobalLineBundleRealization X).ideal =
      ∏ b : Bad (nativePlaceSelection X.S), b.1.maximalIdeal.asIdeal := rfl

/-- The realized global line bundle is the qPilotGlobalLineBundle. -/
theorem qPilotGlobalLineBundleRealization_lineBundle
    [Fintype (Bad (nativePlaceSelection X.S))] :
    (qPilotGlobalLineBundleRealization X).lineBundle =
      qPilotGlobalLineBundle X := rfl

/-- The realized q_v family is the actual clause-B q family. -/
theorem qPilotGlobalLineBundleRealization_qV
    [Fintype (Bad (nativePlaceSelection X.S))]
    (b : Bad (nativePlaceSelection X.S)) :
    (qPilotGlobalLineBundleRealization X).qV b = qVFamily X.S b := rfl

/-- The realized zero-locus divisor is the actual prime divisor at the base bad
place. -/
theorem qPilotGlobalLineBundleRealization_zeroLocus
    [Fintype (Bad (nativePlaceSelection X.S))]
    (b : Bad (nativePlaceSelection X.S)) :
    (qPilotGlobalLineBundleRealization X).zeroLocus b =
      globalPrimeDivisor (X := X) (qVCarrierBasePrime X b) := rfl

end LeanFormal.IUT.XiFPaper.QPilotGlobalLineBundleActual
