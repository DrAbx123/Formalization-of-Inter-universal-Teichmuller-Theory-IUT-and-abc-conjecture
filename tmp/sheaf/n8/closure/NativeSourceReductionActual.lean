import LeanFormal.IUT.IUTI.InitialTheta.SourceDefinition31Boundary
import LeanFormal.IUT.IUTI.HodgeTheater.SourceDefinition31NativeContractBridgeReduction
import LeanFormal.IUT.IUTI.InitialTheta.SourceDefinition31Quantifiers
import LeanFormal.IUT.IUTI.InitialTheta.SourcePlacePartitionReduction
import LeanFormal.IUT.IUTI.InitialTheta.SourcePlaceSelection
import LeanFormal.IUT.IUTIII.Corollary312.ArithmeticQPilotLogVolume

/-!
# Native SourcePlacePartition and SourceReductionClause

This file constructs the Definition 3.1(a)(b) place partition and reduction
clause from InitialThetaSource.SourceNativeInitialThetaData.

Selected places are the source places P.V of the native selection. Bad places
are the subtype of finite moduli places in tuple.source.V_mod_bad. Labels are
the source residue-characteristic labels from SourcePlacePartitionReduction.
Stable reduction comes from clause (a); multiplicative reduction and the
q-parameter witness come from clause (b).

Three source fields are absent from the native tuple and are explicit
hypotheses here:
1. Fintype (Bad P): finiteness of the bad moduli set;
2. NativeBadLift: a finite place of F above each bad moduli place, with
   comap equal to the moduli place;
3. hSplit: split multiplicative reduction at those F-places.

No Unit/Fin 1/arbitrary Fintype/True/PUnit/fake axiom is used.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT
namespace N8Closure

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.ArithmeticQPilotLogVolume

universe ua uv upi umon ui u

variable {l : PrimeGeFive}

/-- Canonical alias: the native place selection is exactly the
`LeanFormal.IUT` selection, definitionally (W4 unification). -/
abbrev nativePlaceSelection
    (T : SourceNativeInitialThetaData.{u} l) : SourcePlaceSelection T.arithmetic :=
  LeanFormal.IUT.nativePlaceSelection T

/-- The native place partition; extra input is exactly the finiteness of the
bad moduli set, which the native tuple does not store. -/
def nativePlacePartition
    (T : SourceNativeInitialThetaData.{u} l)
    [Fintype (Bad (nativePlaceSelection T))] :
    Theorem311Source.SourcePlacePartition
      (Selected (nativePlaceSelection T))
      (Bad (nativePlaceSelection T)) :=
  toSourcePlacePartition (nativePlaceSelection T)

/-- Explicit lying-over field absent from the native tuple: a finite place of F
above each bad moduli place. -/
structure NativeBadLift
    (A : InitialThetaArithmeticData.{u} l)
    (P : SourcePlaceSelection A) where
  lift : Bad P -> NumberField.FinitePlace A.F
  lift_comap : forall b : Bad P,
    NumberFieldFinitePlace.comap (k := A.Fmod) (lift b) = b.1

/-- The actual Clause (b) Tate comparison witness at a bad moduli place, using
the explicit lying-over place. -/
noncomputable def nativeBadTateWitness
    (T : SourceNativeInitialThetaData.{u} l)
    (L : NativeBadLift T.arithmetic (nativePlaceSelection T))
    (b : Bad (nativePlaceSelection T)) :
    SourceTateComparisonWitness T.arithmetic (L.lift b) :=
  Classical.choice
    (T.clauseB.q_comparison (L.lift b) (by
      rw [L.lift_comap b]
      exact b.2))

/-- The actual source q-parameter norm from the Clause (b) Tate comparison
witness, not the valuation proxy badPlaceQProxy. -/
noncomputable def nativeQParameter
    (T : SourceNativeInitialThetaData.{u} l)
    (L : NativeBadLift T.arithmetic (nativePlaceSelection T))
    (b : Bad (nativePlaceSelection T)) : Real :=
  ‖(nativeBadTateWitness T L b).parameter.q‖

theorem nativeQParameter_pos
    (T : SourceNativeInitialThetaData.{u} l)
    (L : NativeBadLift T.arithmetic (nativePlaceSelection T))
    (b : Bad (nativePlaceSelection T)) :
    0 < nativeQParameter T L b := by
  unfold nativeQParameter
  exact qNorm_pos (nativeBadTateWitness T L b).parameter

theorem nativeQParameter_lt_one
    (T : SourceNativeInitialThetaData.{u} l)
    (L : NativeBadLift T.arithmetic (nativePlaceSelection T))
    (b : Bad (nativePlaceSelection T)) :
    nativeQParameter T L b < 1 := by
  unfold nativeQParameter
  exact qNorm_lt_one (nativeBadTateWitness T L b).parameter

theorem nativeQParameter_ne_zero
    (T : SourceNativeInitialThetaData.{u} l)
    (L : NativeBadLift T.arithmetic (nativePlaceSelection T))
    (b : Bad (nativePlaceSelection T)) :
    nativeQParameter T L b ≠ 0 :=
  ne_of_gt (nativeQParameter_pos T L b)

theorem nativeQParameter_ne_one
    (T : SourceNativeInitialThetaData.{u} l)
    (L : NativeBadLift T.arithmetic (nativePlaceSelection T))
    (b : Bad (nativePlaceSelection T)) :
    nativeQParameter T L b ≠ 1 :=
  ne_of_lt (nativeQParameter_lt_one T L b)

theorem nativeQParameter_norm_lt_one
    (T : SourceNativeInitialThetaData.{u} l)
    (L : NativeBadLift T.arithmetic (nativePlaceSelection T))
    (b : Bad (nativePlaceSelection T)) :
    ‖nativeQParameter T L b‖ < 1 := by
  rw [Real.norm_of_nonneg (le_of_lt (nativeQParameter_pos T L b))]
  exact nativeQParameter_lt_one T L b

/-- The native reduction clause. Stable reduction is Clause (a); multiplicative
reduction and the q-witness are Clause (b); split multiplicative reduction is
the explicit source hypothesis absent from the native clauses. -/
def nativeReductionClause
    (T : SourceNativeInitialThetaData.{u} l)
    [Fintype (Bad (nativePlaceSelection T))]
    (L : NativeBadLift T.arithmetic (nativePlaceSelection T))
    (hSplit : forall b : Bad (nativePlaceSelection T),
      T.arithmetic.curve.HasSplitMultiplicativeReductionAt (L.lift b)) :
    Theorem311Source.SourceReductionClause
      (Selected (nativePlaceSelection T))
      (Bad (nativePlaceSelection T)) where
  partition := toSourcePlacePartition (nativePlaceSelection T)
  stableReduction := fun b =>
    T.arithmetic.curve.HasStableReductionAt (L.lift b)
  stableReduction_proved := fun b =>
    T.clauseA.stable_reduction_nonarchimedean (L.lift b)
  multiplicativeReduction := fun b =>
    T.arithmetic.curve.HasMultiplicativeReductionAt (L.lift b)
  multiplicativeReduction_proved := fun b =>
    T.clauseB.multiplicative_over_bad (L.lift b) (by
      rw [L.lift_comap b]
      exact b.2)
  splitMultiplicativeReduction := fun b =>
    T.arithmetic.curve.HasSplitMultiplicativeReductionAt (L.lift b)
  splitMultiplicativeReduction_proved := hSplit
  reductionCompatibility := fun b =>
    T.arithmetic.curve.hasSplitMultiplicativeReductionAt_imp_multiplicative
  qParameter := fun b => nativeQParameter T L b
  qParameter_nonzero := fun b => nativeQParameter_ne_zero T L b
  qParameter_contracting := fun b => nativeQParameter_norm_lt_one T L b
  qParameter_reduction_compatibility := fun b _ =>
    nativeQParameter_ne_one T L b

/-- The native source place partition. -/
def nativeSourcePlacePartition
    (T : SourceNativeInitialThetaData.{u} l)
    [Fintype (Bad (nativePlaceSelection T))] :
    Theorem311Source.SourcePlacePartition
      (Selected (nativePlaceSelection T))
      (Bad (nativePlaceSelection T)) :=
  nativePlacePartition T

/-- The native source reduction clause. -/
def nativeSourceReductionClause
    (T : SourceNativeInitialThetaData.{u} l)
    [Fintype (Bad (nativePlaceSelection T))]
    (L : NativeBadLift T.arithmetic (nativePlaceSelection T))
    (hSplit : forall b : Bad (nativePlaceSelection T),
      T.arithmetic.curve.HasSplitMultiplicativeReductionAt (L.lift b)) :
    Theorem311Source.SourceReductionClause
      (Selected (nativePlaceSelection T))
      (Bad (nativePlaceSelection T)) :=
  nativeReductionClause T L hSplit

end N8Closure
end LeanFormal.IUT
