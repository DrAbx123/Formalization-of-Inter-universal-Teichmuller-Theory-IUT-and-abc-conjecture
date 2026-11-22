import tmp.sheaf.n8.closure.NativeBadFintypeProof
import tmp.sheaf.n8.closure.NativeLocalReductionDisjointAlt

/-! # Native bad-set finiteness for an arbitrary source datum

This replicates the finite-good-reduction argument directly for a
`SourceNativeInitialThetaData`, without a separate `N8NativeInput` wrapper. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT.N8Closure.NativeBadFintypeForTActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure.NativeBadFintypeProof
open LeanFormal.IUT.N8Closure.NativeLocalReductionDisjointAlt

universe u

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)

/-- The native bad moduli set is finite, from actual finite bad reduction and
the local disjointness theorem. -/
theorem nativeBadSetFinite :
    T.tuple.source.V_mod_bad.Finite := by
  let A := T.arithmetic
  let W := A.curve
  obtain ⟨S, hSfinite, hSgood⟩ :=
    Definition31BadReductionFiniteness.exists_finite_goodReduction_off W
  let lift : T.tuple.source.V_mod_bad -> NumberField.FinitePlace A.F :=
    fun p => Classical.choose
      (NumberFieldFinitePlace.comap_surjective (K := A.F) p.1)
  have lift_comap : forall p : T.tuple.source.V_mod_bad,
      NumberFieldFinitePlace.comap (k := A.Fmod) (lift p) = p.1 := by
    intro p
    exact Classical.choose_spec
      (NumberFieldFinitePlace.comap_surjective (K := A.F) p.1)
  have lift_mem_S : forall p : T.tuple.source.V_mod_bad, lift p ∈ S := by
    intro p
    have hp : NumberFieldFinitePlace.comap (k := A.Fmod) (lift p) ∈
        T.tuple.source.V_mod_bad := by
      rw [lift_comap p]
      exact p.2
    have hmult : W.HasMultiplicativeReductionAt (lift p) :=
      T.clauseB.multiplicative_over_bad (lift p) hp
    by_contra hnot
    exact nativeLocalReductionDisjoint_alt A.F W (lift p) hmult
      (hSgood (lift p) hnot)
  let toS : T.tuple.source.V_mod_bad ->
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
  haveI : Finite T.tuple.source.V_mod_bad :=
    Finite.of_injective toS hinj
  exact Set.finite_coe_iff.mp inferInstance

/-- Actual Fintype of the native bad places. -/
theorem nativeBadFintype_nonempty :
    Nonempty (Fintype (Bad (nativePlaceSelection T))) := by
  haveI : Finite (Bad (nativePlaceSelection T)) :=
    nativeBadSetFinite T |>.to_subtype
  exact ⟨Fintype.ofFinite _⟩

/-- The actual finite enumeration of the native bad places. -/
@[reducible] noncomputable def nativeBadFintype :
    Fintype (Bad (nativePlaceSelection T)) :=
  Classical.choice (nativeBadFintype_nonempty T)

end LeanFormal.IUT.N8Closure.NativeBadFintypeForTActual

end
