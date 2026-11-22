import tmp.sheaf.n8.closure.NativeBadLiftActual
import tmp.sheaf.n8.closure.NativeReductionFieldsActual
import tmp.sheaf.xif.paper.ProcessionNormalizationWeightsActual

/-!
# Actual bad-place indexing and obstruction

This file constructs the actual indexing data available from the native source:

* nativeBadToFPlace T b : a finite place of the global field F above the bad
  moduli place b, obtained from the actual lying-over construction
  NativeBadLiftActual.nativeBadLift;
* the theorem that its comap to F_mod is exactly b.1;
* the actual normalized local weight at that F-place, from
  ProcessionNormalizationWeightsActual.localNormalizedWeight;
* the actual dependent place index carrying the comap proof.

The remaining non-actual step is also recorded exactly: the abstract
SourceDefinition31Data.badPlaces of an OriginalInput is not identified in the
tree with the native bad index Bad (nativePlaceSelection T). Such an
equivalence, plus compatibility of q-parameters, is the exact required data for
VbadPlaceIndexingObstruction. No such equivalence is fabricated.

No raw SignedLabel sum, no fake place, no inequality.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT.XiFPaper.VbadPlaceIndexingActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.ProcessionNormalizationWeightsActual

variable {l : PrimeGeFive} (T : SourceNativeInitialThetaData.{0} l)

/-- The actual finite F-place above the bad moduli place b, from the
lying-over construction. -/
noncomputable def nativeBadToFPlace
    (b : Bad (nativePlaceSelection T)) : NumberField.FinitePlace T.arithmetic.F :=
  (nativeBadLift T).lift b

/-- The actual comap equation: the F-place really lies above b. -/
theorem nativeBadToFPlace_comap
    (b : Bad (nativePlaceSelection T)) :
    NumberFieldFinitePlace.comap (k := T.arithmetic.Fmod)
        (nativeBadToFPlace T b) = b.1 :=
  (nativeBadLift T).lift_comap b

/-- The actual dependent indexing datum: an F-place together with its comap
proof to the bad moduli place. -/
noncomputable def nativeBadFPlaceIndex
    (b : Bad (nativePlaceSelection T)) :
    {w : NumberField.FinitePlace T.arithmetic.F //
      NumberFieldFinitePlace.comap (k := T.arithmetic.Fmod) w = b.1} :=
  ⟨nativeBadToFPlace T b, nativeBadToFPlace_comap T b⟩

/-- The actual bad moduli place, i.e. the F_mod place b.1. -/
def nativeBadFmodPlace
    (b : Bad (nativePlaceSelection T)) :
    NumberField.FinitePlace T.arithmetic.Fmod :=
  b.1

/-- The actual finite K-place above the bad moduli place b, from
lying-over.  The normalized local weight is a K-place weight
[K_w : (F_mod)_v]; it is not the F-place indexing datum below. -/
noncomputable def nativeBadToKPlace
    (b : Bad (nativePlaceSelection T)) : NumberField.FinitePlace T.arithmetic.K :=
  Classical.choose
    (NumberFieldFinitePlace.comap_surjective (K := T.arithmetic.K) b.1)

/-- The actual K-place comap equation. -/
theorem nativeBadToKPlace_comap
    (b : Bad (nativePlaceSelection T)) :
    NumberFieldFinitePlace.comap (k := T.arithmetic.Fmod)
        (nativeBadToKPlace T b) = b.1 :=
  Classical.choose_spec
    (NumberFieldFinitePlace.comap_surjective (K := T.arithmetic.K) b.1)

/-- The actual normalized local weight at the selected K-place over the bad
base place. -/
noncomputable def nativeBadLocalWeight
    (b : Bad (nativePlaceSelection T)) : Real :=
  localNormalizedWeight T.arithmetic (nativeBadToKPlace T b)

/-- The actual weight formula: inverse actual completion degree. -/
theorem nativeBadLocalWeight_eq_inv
    (b : Bad (nativePlaceSelection T)) :
    nativeBadLocalWeight T b =
      ((localCompletionDegree T.arithmetic (nativeBadToKPlace T b) : Nat) : Real)⁻¹ :=
  rfl

/-- Actual indexing plus actual local weight, assembled. -/
theorem nativeBadIndexing_actual
    (b : Bad (nativePlaceSelection T)) :
    NumberFieldFinitePlace.comap (k := T.arithmetic.Fmod)
        (nativeBadToFPlace T b) = b.1
      ∧ nativeBadLocalWeight T b =
          ((localCompletionDegree T.arithmetic
            (nativeBadToKPlace T b) : Nat) : Real)⁻¹ :=
  ⟨nativeBadToFPlace_comap T b, nativeBadLocalWeight_eq_inv T b⟩

/-- Exact required bridge: the abstract badPlaces of the OriginalInput source
contract must be identified with the native bad index, compatibly with the
selected moduli places. This is a proposition recording the missing
identification; it is not asserted. -/
def NativeBadIndexingBridge
    {V : Type} (I : OriginalInput.{0, 0, 0, 0, 0} l V)
    (T : SourceNativeInitialThetaData.{0} l) : Prop :=
  Nonempty (I.initial.badPlaces ≃ Bad (nativePlaceSelection T))

/-- The exact place-indexing obstruction for the abstract V_bad of the source
contract. -/
def VbadPlaceIndexingObstruction
    {V : Type} (I : OriginalInput.{0, 0, 0, 0, 0} l V)
    (T : SourceNativeInitialThetaData.{0} l) : Prop :=
  NativeBadIndexingBridge (l := l) I T

/-- The actual indexing/weight part is proved; the bridge to the abstract
badPlaces remains the precise missing identification. -/
theorem nativeBadIndexing_residual
    {V : Type} (I : OriginalInput.{0, 0, 0, 0, 0} l V) :
    (∀ b : Bad (nativePlaceSelection T),
      NumberFieldFinitePlace.comap (k := T.arithmetic.Fmod)
          (nativeBadToFPlace T b) = b.1)
      ∧ (VbadPlaceIndexingObstruction (l := l) I T ↔
          Nonempty (I.initial.badPlaces ≃ Bad (nativePlaceSelection T))) :=
  ⟨nativeBadToFPlace_comap T, Iff.rfl⟩

end LeanFormal.IUT.XiFPaper.VbadPlaceIndexingActual

end
