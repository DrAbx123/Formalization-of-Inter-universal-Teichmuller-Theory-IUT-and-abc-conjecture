import tmp.sheaf.n8.closure.NativeSourceReductionActual
import LeanFormal.IUT.IUTI.InitialTheta.SourcePlacePartitionReduction

/-!
# Actual V_bad-indexed base q candidate family

IUT I, Definition 3.1(b)-(c); IUT III, Definition 3.8, (i), pp. 112-113.

The source place selection carries, for every bad moduli place b, the section
lift sectionFiniteLift P b.1 (a finite place of K with comap equal to b.1) and
the actual valuation-theoretic q candidate

  badPlaceQCandidate P b :
    FinitePlaceQCandidate (sectionFiniteLift P b.1)

constructed by Classical.choice from the actual finitePlaceQCandidate_nonempty
theorem.  This is independent of the clause-B F-place q_v family and is not
asserted to equal it.

This file constructs the actual V_bad-indexed base q candidate family, its q
laws, its base-place comap relation, and the actual relation to the real
proxy badPlaceQProxy.  No equality to qVFamily is asserted.  No inequality is
asserted beyond the q-candidate valuation fields already carried by the source
object.  No toy/True/PUnit/axiom/sorry.  WRITE-ONLY; no local compile; queued.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 1000000

namespace LeanFormal.IUT.XiFPaper.BaseQFamilyActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace

universe u

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)

/-- The native bad-place selection used for the base q family. -/
abbrev NativeBaseSelection : SourcePlaceSelection T.arithmetic :=
  nativePlaceSelection T

/-- The actual section lift of a native bad moduli place b to a finite place of
K, with comap exactly b.1. -/
noncomputable def nativeBaseSectionPlace
    (b : Bad (NativeBaseSelection T)) :
    NumberField.FinitePlace T.arithmetic.K :=
  sectionFiniteLift (NativeBaseSelection T) b.1

/-- The actual V_bad-indexed base q candidate family: the source DVR q
candidate at the section lift of each bad moduli place. -/
noncomputable def nativeBaseQFamily
    (b : Bad (NativeBaseSelection T)) :
    FinitePlaceQCandidate (nativeBaseSectionPlace T b) :=
  badPlaceQCandidate (NativeBaseSelection T) b

/-- The base q family is exactly the source badPlaceQCandidate. -/
theorem nativeBaseQFamily_eq_badPlaceQCandidate
    (b : Bad (NativeBaseSelection T)) :
    nativeBaseQFamily T b =
      badPlaceQCandidate (NativeBaseSelection T) b := rfl

/-- The base section place contracts to the bad moduli place b. -/
theorem nativeBaseSectionPlace_comap
    (b : Bad (NativeBaseSelection T)) :
    NumberFieldFinitePlace.comap (nativeBaseSectionPlace T b) = b.1 :=
  sectionFiniteLift_comap (NativeBaseSelection T) b.1

/-- The base q candidate is nonzero. -/
theorem nativeBaseQFamily_q_ne_zero
    (b : Bad (NativeBaseSelection T)) :
    (nativeBaseQFamily T b).q ≠ 0 :=
  (nativeBaseQFamily T b).q_ne_zero

/-- The base q candidate is contracting. -/
theorem nativeBaseQFamily_valuation_lt_one
    (b : Bad (NativeBaseSelection T)) :
    (Valued.v (nativeBaseQFamily T b).q : WithZero (Multiplicative Int)) < 1 :=
  (nativeBaseQFamily T b).valuation_lt_one

/-- The base q candidate has positive order. -/
theorem nativeBaseQFamily_order_pos
    (b : Bad (NativeBaseSelection T)) :
    0 < (nativeBaseQFamily T b).order :=
  (nativeBaseQFamily T b).order_pos

/-- The real proxy is the actual residue-characteristic power of the base q
order. -/
theorem nativeBaseQFamily_proxy_eq
    (b : Bad (NativeBaseSelection T)) :
    badPlaceQProxy (NativeBaseSelection T) b =
      ((NumberFieldFinitePlace.residueCharacteristic b.1 : Nat) : Real)⁻¹ ^
        (nativeBaseQFamily T b).order := rfl

/-- The actual base q family is indexed by the native V_bad and lives at the
actual section lifts of the base bad places. -/
abbrev nativeBaseQFamilyIndex : Type :=
  (b : Bad (NativeBaseSelection T)) →
    FinitePlaceQCandidate (nativeBaseSectionPlace T b)

/-- The constructed family has the required index type. -/
def nativeBaseQFamilyIndexed : nativeBaseQFamilyIndex T :=
  nativeBaseQFamily T

/-- The indexed family evaluates to the actual base q candidate. -/
theorem nativeBaseQFamilyIndexed_apply
    (b : Bad (NativeBaseSelection T)) :
    nativeBaseQFamilyIndexed T b = nativeBaseQFamily T b := rfl

end LeanFormal.IUT.XiFPaper.BaseQFamilyActual
