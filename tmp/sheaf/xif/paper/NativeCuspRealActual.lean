import tmp.sheaf.xif.paper.NativeD7CuspActual
import tmp.sheaf.n8.closure.NativeSourceSectionsCuspActual

/-!
# Native cusp real epsilon/cuspScale: object construction status

The native cusp object is actual and geometric:

  nativeEpsilonGeometric T
    : Iut.OrbicurveBoundaryCusp (nativeCompletion T).sourceSignQuotientData.cK.

NativeCuspClauseHypotheses instead requires real data:

  epsilon : Real, 0 < epsilon, epsilon != 0,
  cuspScale : Real, 0 < cuspScale, epsilon * cuspScale != 0,
  epsilon_compatibility : Prop with proof,
  native_epsilon_realization : Prop.

No map from OrbicurveBoundaryCusp to Real and no real cuspScale attached to the
native tuple exists in the tree. Therefore no NativeCuspClauseHypotheses is
constructed unconditionally. The exact missing real-coordinate data is isolated
below; a conditional constructor from that explicit data is provided.

No arbitrary real, compatibility proposition, toy data, forbidden placeholder,
or unfilled proof is fabricated.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT.XiFPaper.NativeCuspRealActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.NativeSourceSectionsCuspActual
open LeanFormal.IUT.XiFPaper.NativeD7CuspActual

universe u

variable {l : PrimeGeFive} (T : SourceNativeInitialThetaData.{0} l)

/-- The actual native geometric cusp boundary object. -/
abbrev nativeCuspGeometric :
    Iut.OrbicurveBoundaryCusp (nativeCompletion T).sourceSignQuotientData.cK :=
  nativeEpsilonGeometric T

/-- Exact missing real-coordinate package for the native cusp. All its fields
are explicit data; the geometric-to-real realization is a proposition plus its
proof, not an assumed identity. -/
structure CuspRealizationData where
  epsilon : Real
  epsilon_positive : 0 < epsilon
  epsilon_nonzero : epsilon != 0
  cuspScale : Real
  cuspScale_positive : 0 < cuspScale
  epsilon_scale_relation : epsilon * cuspScale != 0
  epsilon_compatibility : Prop
  epsilon_compatibility_proved : epsilon_compatibility
  native_epsilon_realization : Prop
  native_epsilon_realization_proved : native_epsilon_realization

/-- Conditional construction of NativeCuspClauseHypotheses from the exact real
coordinate data. -/
def nativeCuspHypothesesOfRealization
    (R : CuspRealizationData) : NativeCuspClauseHypotheses where
  epsilon := R.epsilon
  epsilon_positive := R.epsilon_positive
  epsilon_nonzero :=
    bne_iff_ne.mp (show (R.epsilon != 0) = true from R.epsilon_nonzero)
  cuspScale := R.cuspScale
  cuspScale_positive := R.cuspScale_positive
  epsilon_scale_relation :=
    bne_iff_ne.mp (show (R.epsilon * R.cuspScale != 0) = true from R.epsilon_scale_relation)
  epsilon_compatibility := R.epsilon_compatibility
  epsilon_compatibility_proved := R.epsilon_compatibility_proved
  native_epsilon_realization := R.native_epsilon_realization

/-- Exact missing object: real epsilon/cuspScale data plus the native geometric
realization proof. -/
def MissingNativeCuspRealization : Prop :=
  Nonempty (CuspRealizationData)

/-- The geometric cusp has no real-coordinate construction in this file. -/
def nativeCuspGeometric_type :
    Iut.OrbicurveBoundaryCusp
      (nativeCompletion T).sourceSignQuotientData.cK :=
  nativeCuspGeometric T

/-- Conditional native cusp clause from the exact missing real data. -/
theorem nativeCuspClause_of_realization
    (R : CuspRealizationData) :
    Nonempty Theorem311Source.SourceCuspClause :=
  ⟨nativeCuspClauseOfHypotheses (nativeCuspHypothesesOfRealization R)⟩

end LeanFormal.IUT.XiFPaper.NativeCuspRealActual

end
