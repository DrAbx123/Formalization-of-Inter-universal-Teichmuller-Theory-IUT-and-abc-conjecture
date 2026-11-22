import tmp.sheaf.n8.closure.NativeSourceReductionActual
import tmp.sheaf.n8.closure.NativeBadLiftActual
import tmp.sheaf.n8.closure.NativeReductionFieldsActual
import LeanFormal.IUT.IUTI.InitialTheta.TateComparisonBoundary

/-!
# Attempt: split-multiplicative reduction from the Tate comparison

STATUS: audit/attempt only. No split proof is fabricated.

Inputs:
* NativeBadLiftActual supplies the actual lying-over lift nativeBadLift;
* NativeReductionFieldsActual supplies NativeSplitMultiplicativeAtLift and the
  exact bad-set finiteness equivalence;
* NativeSourceReductionActual supplies the conditional native reduction clause;
* SourceTateComparisonWitness from clauseB gives a TateCurveComparison at each
  lifted F-place.

What the Tate comparison actually contains:
* canonical Tate model is elliptic (canonicalIsElliptic);
* a variable change realizes the actual curve (realizesCurve/coordinateChange);
* Galois-equivariant point comparison (points).
It does NOT contain split multiplicative reduction, a minimal-model split
witness, or a theorem split-multiplicative-reduction follows from the Tate
uniformization data. The existing production lemmas
(PuncturedEllipticCurve.hasSplitMultiplicativeReductionAt_imp_multiplicative,
TateCurveArithmetic.MultiplicativeCertificate, and the concrete split curve
theorems) only go from split to multiplicative or prove split for a fixed
concrete curve. No general Tate comparison -> split theorem exists.

Exact missing source theorem:
  NativeSplitMultiplicativeAtLift T
    := forall b : Bad (nativePlaceSelection T),
         T.arithmetic.curve.HasSplitMultiplicativeReductionAt
           ((nativeBadLift T).lift b).

This file records that exact theorem and proves the only available conditional
assembly (split target + finite bad set => native reduction clause). It does not
assert the target, add an axiom, or fake a split certificate.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT.N8Closure
namespace NativeSplitFromTate

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.N8Closure.NativeReductionFieldsActual

variable {l : PrimeGeFive}

/-- The actual Tate comparison obtained from the clause B witness at the
actual lying-over F-place. This is the concrete data that the attempted
derivation would use. -/
noncomputable def nativeTateComparison
    (T : SourceNativeInitialThetaData.{0} l)
    (b : Bad (nativePlaceSelection T)) :
    TateCurveComparison T.arithmetic.curve
      ((nativeBadLift T).lift b)
      (nativeBadTateWitness T (nativeBadLift T) b).parameter :=
  (nativeBadTateWitness T (nativeBadLift T) b).comparison

/-- Exact missing theorem, named for the source ledger. It is definitionally
the split reduction target at the actual native lift. -/
def NativeSplitFromTateTheorem
    (T : SourceNativeInitialThetaData.{0} l) : Prop :=
  NativeSplitMultiplicativeAtLift T

/-- The Tate comparison supplies multiplicative reduction (via clause B), but
not split reduction. This theorem records only the multiplicative half that
does follow from the actual witness. -/
theorem nativeTateComparison_multiplicative
    (T : SourceNativeInitialThetaData.{0} l)
    (b : Bad (nativePlaceSelection T)) :
    T.arithmetic.curve.HasMultiplicativeReductionAt
      ((nativeBadLift T).lift b) :=
  T.clauseB.multiplicative_over_bad ((nativeBadLift T).lift b) (by
    rw [(nativeBadLift T).lift_comap b]
    exact b.2)

/-- No split conclusion is extracted from the Tate comparison in this file.
The target is exactly the missing theorem. -/
theorem nativeSplitFromTateTheorem_iff_target
    (T : SourceNativeInitialThetaData.{0} l) :
    NativeSplitFromTateTheorem T ↔ NativeSplitMultiplicativeAtLift T :=
  Iff.rfl

/-- Conditional assembly: if the missing split theorem and the bad-set
finiteness are supplied, the native reduction clause follows from the actual
Tate/clause data and the actual lift. -/
def nativeReductionClauseOfTateSplit
    (T : SourceNativeInitialThetaData.{0} l)
    [Fintype (Bad (nativePlaceSelection T))]
    (hsplit : NativeSplitFromTateTheorem T) :
    Theorem311Source.SourceReductionClause
      (Selected (nativePlaceSelection T))
      (Bad (nativePlaceSelection T)) :=
  nativeReductionClause T (nativeBadLift T) hsplit

/-- The exact primitive theorem still required, stated as a proposition. -/
theorem nativeSplitFromTate_required
    (T : SourceNativeInitialThetaData.{0} l) :
    NativeSplitFromTateTheorem T =
      (∀ b : Bad (nativePlaceSelection T),
        T.arithmetic.curve.HasSplitMultiplicativeReductionAt
          ((nativeBadLift T).lift b)) :=
  rfl

end NativeSplitFromTate
end LeanFormal.IUT.N8Closure
end
