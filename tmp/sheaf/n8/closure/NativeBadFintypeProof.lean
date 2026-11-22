import tmp.sheaf.n8.closure.NativeInput
import tmp.sheaf.n8.closure.NativeReductionFieldsActual
import LeanFormal.IUT.IUTI.InitialTheta.SourceDefinition31PlacePartition

/-!
# Deep attempt: finiteness of the native bad set

Goal: prove
  X.S.tuple.source.V_mod_bad.Finite
for X : N8NativeInput l.

Route found in production:
* InitialThetaSource.Definition31BadReductionFiniteness.exists_finite_goodReduction_off
  gives a finite set S of finite places of F outside which X.S.arithmetic.curve
  has good reduction.
* For every bad moduli place p, NumberFieldFinitePlace.comap_surjective gives a
  finite F-place w over p, and Clause B gives HasMultiplicativeReductionAt w.
* Hence w belongs to S, provided multiplicative reduction excludes good
  reduction at the same F-place.
* The map p |-> chosen w is injective because comap w = p, so the bad moduli
  set embeds into the finite set S and is finite.

The only missing production theorem is the local disjointness
  HasMultiplicativeReductionAt w -> not HasGoodReductionAt w.
Mathlib proves the corresponding statement for one minimal Weierstrass model
(WeierstrassCurve.HasMultiplicativeReduction.not_hasGoodReduction), but the
presentation-independent PuncturedEllipticCurve predicates are existentials
over possibly different minimal models; no production declaration currently
transfers Mathlib's disjointness to HasMultiplicativeReductionAt. This file
keeps exactly that theorem as an explicit hypothesis NativeLocalReductionDisjoint
and proves the finite-set consequence conditionally. No Fintype, split, or
local disjointness is fabricated.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT.N8Closure
namespace NativeBadFintypeProof

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.InitialThetaSource.Definition31BadReductionFiniteness
open LeanFormal.IUT.N8Closure.NativeInput
open LeanFormal.IUT.N8Closure.NativeReductionFieldsActual
open LeanFormal.IUT.NumberFieldFinitePlace

variable {l : PrimeGeFive}
universe u

/-- Exact missing local theorem: at a finite place of F, actual multiplicative
reduction excludes actual good reduction. -/
def NativeLocalReductionDisjoint : Prop :=
  forall (F : Type) [Field F] [NumberField F]
    (X : PuncturedEllipticCurve F) (p : NumberField.FinitePlace F),
      X.HasMultiplicativeReductionAt p -> ¬ X.HasGoodReductionAt p

/-- Direct Fintype form of the source finiteness. -/
theorem nativeBadFintype_of_sourceFinite
    (T : SourceNativeInitialThetaData.{u} l)
    (h : T.tuple.source.V_mod_bad.Finite) :
    Nonempty (Fintype (Bad (nativePlaceSelection T))) := by
  haveI : Finite (Bad (nativePlaceSelection T)) := h.to_subtype
  exact ⟨Fintype.ofFinite _⟩

/-- Deep conditional result: the native bad moduli set is finite from the
actual curve bad-reduction finiteness plus the exact local disjointness
theorem. -/
theorem nativeBadSetFinite_of_localDisjoint
    (X : N8NativeInput l)
    (hLocal : NativeLocalReductionDisjoint) :
    X.S.tuple.source.V_mod_bad.Finite := by
  let A := X.S.arithmetic
  let W := A.curve
  obtain ⟨S, hSfinite, hSgood⟩ :=
    Definition31BadReductionFiniteness.exists_finite_goodReduction_off W
  let lift : X.S.tuple.source.V_mod_bad -> NumberField.FinitePlace A.F :=
    fun p => Classical.choose
      (NumberFieldFinitePlace.comap_surjective (K := A.F) p.1)
  have lift_comap : forall p : X.S.tuple.source.V_mod_bad,
      NumberFieldFinitePlace.comap (k := A.Fmod) (lift p) = p.1 := by
    intro p
    exact Classical.choose_spec
      (NumberFieldFinitePlace.comap_surjective (K := A.F) p.1)
  have lift_mem_S : forall p : X.S.tuple.source.V_mod_bad, lift p ∈ S := by
    intro p
    have hp : NumberFieldFinitePlace.comap (k := A.Fmod) (lift p) ∈
        X.S.tuple.source.V_mod_bad := by
      rw [lift_comap p]
      exact p.2
    have hmult : W.HasMultiplicativeReductionAt (lift p) :=
      X.S.clauseB.multiplicative_over_bad (lift p) hp
    by_contra hnot
    exact hLocal A.F W (lift p) hmult (hSgood (lift p) hnot)
  let toS : X.S.tuple.source.V_mod_bad ->
      {w : NumberField.FinitePlace A.F // w ∈ S} :=
    fun p => ⟨lift p, lift_mem_S p⟩
  have hinj : Function.Injective toS := by
    intro p q hpq
    apply Subtype.ext
    have hv : lift p = lift q := congrArg Subtype.val hpq
    calc
      p.1 = NumberFieldFinitePlace.comap (k := A.Fmod) (lift p) :=
        (lift_comap p).symm
      _ = NumberFieldFinitePlace.comap (k := A.Fmod) (lift q) := by rw [hv]
      _ = q.1 := lift_comap q
  haveI : Finite {w : NumberField.FinitePlace A.F // w ∈ S} :=
    hSfinite.to_subtype
  haveI : Finite X.S.tuple.source.V_mod_bad :=
    Finite.of_injective toS hinj
  exact Set.finite_coe_iff.mp inferInstance

/-- The Fintype form of the same conditional result, using the exact
finite-subtype equivalence already proved in NativeReductionFieldsActual. -/
theorem nativeBadFintype_of_localDisjoint
    (X : N8NativeInput l)
    (hLocal : NativeLocalReductionDisjoint) :
    Nonempty (Fintype (Bad (nativePlaceSelection X.S))) :=
  nativeBadFintype_of_sourceFinite X.S
    (nativeBadSetFinite_of_localDisjoint X hLocal)

end NativeBadFintypeProof
end LeanFormal.IUT.N8Closure
end
