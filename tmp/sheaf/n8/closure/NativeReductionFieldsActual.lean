import tmp.sheaf.n8.closure.NativeSourceReductionActual
import tmp.sheaf.n8.closure.NativeBadLiftActual
import tmp.sheaf.n8.closure.NativeBadFintypeSourceAttempt
import tmp.sheaf.n8.closure.NativeSplitMultiplicativeAttempt

/-!
# Native reduction primitive fields: bottom-up outcome

This file asks whether the two remaining primitive fields of
NativeSourceReductionActual can be derived from the native source data and
clauses A/B.

Result:
* the lying-over NativeBadLift IS derived from the actual source via
  NativeBadLiftActual.comap_surjective; it is not a missing field any more.
* Fintype (Bad (nativePlaceSelection T)) is NOT derivable from the native
  tuple/clauses. The exact missing source theorem is
  T.tuple.source.V_mod_bad.Finite. We prove the exact equivalence:
    Nonempty (Fintype (Bad ...)) <-> T.tuple.source.V_mod_bad.Finite.
  No Fintype is fabricated.
* split-multiplicative reduction at nativeBadLift is NOT derivable from
  clauses A/B or the Tate comparison witness: clause A gives stable reduction,
  clause B gives multiplicative reduction and a Tate q-parameter, but neither
  gives split multiplicative reduction. The exact missing source theorem is
  NativeSplitMultiplicativeAtLift T. No split proof is fabricated.

The conditional native reduction clause therefore has exactly two primitive
source hypotheses: the bad-set finiteness and split-multiplicative reduction.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT.N8Closure
namespace NativeReductionFieldsActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.Theorem311Source

variable {l : PrimeGeFive}

/-- Exact source finiteness proposition for the native bad moduli set. -/
def NativeBadSetFinite
    (T : SourceNativeInitialThetaData.{0} l) : Prop :=
  T.tuple.source.V_mod_bad.Finite

/-- Exact equivalence: the bad Fintype exists precisely when the native bad
set is finite. This is the bottom-up reduction of the Fintype primitive to the
actual source finiteness statement. -/
theorem nativeBadFintype_iff_sourceFinite
    (T : SourceNativeInitialThetaData.{0} l) :
    Nonempty (Fintype (Bad (nativePlaceSelection T))) ↔
      NativeBadSetFinite T := by
  constructor
  · rintro ⟨badFintype⟩
    letI := badFintype
    have hf : Set.Finite
        (Set.range (fun b : Bad (nativePlaceSelection T) => b.1)) :=
      Set.finite_range _
    have hrange : Set.range
        (fun b : Bad (nativePlaceSelection T) => b.1) =
        T.tuple.source.V_mod_bad := by
      ext p
      constructor
      · rintro ⟨b, rfl⟩
        exact b.2
      · intro hp
        exact ⟨⟨p, hp⟩, rfl⟩
    unfold NativeBadSetFinite
    rw [← hrange]
    exact hf
  · intro hfinite
    haveI : Finite (Bad (nativePlaceSelection T)) :=
      hfinite.to_subtype
    exact ⟨Fintype.ofFinite _⟩

/-- Exact missing source theorem for split-multiplicative reduction at the
actual lying-over place. Clause A/B and the Tate comparison do not currently
supply it. -/
def NativeSplitMultiplicativeAtLift
    (T : SourceNativeInitialThetaData.{0} l) : Prop :=
  ∀ b : Bad (nativePlaceSelection T),
    T.arithmetic.curve.HasSplitMultiplicativeReductionAt
      ((nativeBadLift T).lift b)

/-- The actual lying-over lift is derived, not hypothesized. -/
theorem nativeBadLift_comap
    (T : SourceNativeInitialThetaData.{0} l)
    (b : Bad (nativePlaceSelection T)) :
    NumberFieldFinitePlace.comap (k := T.arithmetic.Fmod)
        ((nativeBadLift T).lift b) = b.1 :=
  (nativeBadLift T).lift_comap b

/-- From the two exact primitive source fields, assemble the native reduction
clause. This is the bottom-up conditional constructor; it adds no interface and
no fake data. -/
def nativeReductionClauseOfPrimitives
    (T : SourceNativeInitialThetaData.{0} l)
    [Fintype (Bad (nativePlaceSelection T))]
    (hsplit : NativeSplitMultiplicativeAtLift T) :
    Theorem311Source.SourceReductionClause
      (Selected (nativePlaceSelection T))
      (Bad (nativePlaceSelection T)) :=
  nativeReductionClause T (nativeBadLift T) hsplit

/-- The same constructor with the finiteness hypothesis supplied as the exact
source theorem. -/
theorem nativeBadSetFintype
    (T : SourceNativeInitialThetaData.{0} l)
    (hfinite : NativeBadSetFinite T) :
    Nonempty (Fintype (Bad (nativePlaceSelection T))) :=
  (nativeBadFintype_iff_sourceFinite T).mpr hfinite

/-- Exact primitive-field ledger: Fintype is equivalent to source finiteness;
split reduction is the nativeSplitMultiplicativeAtLift proposition. -/
theorem nativeReductionPrimitiveFields
    (T : SourceNativeInitialThetaData.{0} l) :
    (Nonempty (Fintype (Bad (nativePlaceSelection T))) ↔
      NativeBadSetFinite T) ∧
    (NativeSplitMultiplicativeAtLift T ↔
      (∀ b : Bad (nativePlaceSelection T),
        T.arithmetic.curve.HasSplitMultiplicativeReductionAt
          ((nativeBadLift T).lift b))) :=
  ⟨nativeBadFintype_iff_sourceFinite T, Iff.rfl⟩

end NativeReductionFieldsActual
end LeanFormal.IUT.N8Closure
end
