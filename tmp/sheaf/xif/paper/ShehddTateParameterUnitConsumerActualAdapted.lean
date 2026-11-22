import LeanFormal.IUT.Foundations.Geometry.TateUniformizationContract

/-!
# ShehddTateParameterUnitConsumerActualAdapted — Tate parameter unit / deck action consumer

STEP 0 prior-art (reuse only; A475 search: Tate uniformization contract found):
* Foundations/Geometry/TateUniformizationContract.lean (namespace NumberFieldFinitePlace):
  tateParameterUnit (q ↦ image in algebraic closure), tateParameterUnit_ne_one,
  tateParameterUnit_pow, tateParameterUnit_algEquiv_map,
  tateParameterDeckSubgroup_algEquiv_map;
  CurveIndexedTateUniformization (canonicalIsElliptic, coordinateChange,
  realizesCurve, pointUniformization) and coordinate_realization.

This file packages the unit-side Tate-uniformization facts as one consumer: the
parameter unit is nontrivial, its powers behave, and the deck/Galois action fixes it and
its zpowers subgroup.  No new assumptions, no sorry/axiom.
-/

noncomputable section

namespace LeanFormal.IUT.XiFPaper.ShehddTateParameterUnitConsumerActualAdapted

open LeanFormal.IUT
open LeanFormal.IUT.NumberFieldFinitePlace

universe u

/-- **PROVED consumer:** a nontrivial Tate parameter gives a nontrivial parameter unit
fixed by every Galois automorphism, with its zpowers subgroup fixed setwise. -/
theorem tateParameterUnit_deck_fixed_consumer {K : Type u} [Field K] [NumberField K]
    (place : NumberField.FinitePlace K) (q : Completion place) (hq0 : q ≠ 0)
    (hq1 : q ≠ 1)
    (sigma : AlgebraicClosure (Completion place) ≃ₐ[Completion place]
      AlgebraicClosure (Completion place)) :
    tateParameterUnit place q hq0 ≠ 1 ∧
      Units.map sigma.toRingEquiv.toMonoidHom (tateParameterUnit place q hq0) =
        tateParameterUnit place q hq0 ∧
          Subgroup.map (Units.map sigma.toRingEquiv.toMonoidHom)
              (Subgroup.zpowers (tateParameterUnit place q hq0)) =
            Subgroup.zpowers (tateParameterUnit place q hq0) :=
  ⟨tateParameterUnit_ne_one place q hq0 hq1,
    tateParameterUnit_algEquiv_map place q hq0 sigma,
    tateParameterDeckSubgroup_algEquiv_map place q hq0 sigma⟩

/-- **PROVED consumer:** powers of the Tate parameter pass to powers of its unit. -/
theorem tateParameterUnit_pow_consumer {K : Type u} [Field K] [NumberField K]
    (place : NumberField.FinitePlace K) (q : Completion place) (hq0 : q ≠ 0)
    (n : Nat) :
    tateParameterUnit place (q ^ n) (pow_ne_zero n hq0) =
      (tateParameterUnit place q hq0) ^ n :=
  tateParameterUnit_pow place q hq0 n

/-- Row record: reused Tate-uniformization unit laws vs the consumer interface. -/
def tateParameterUnitRows : List (String × String × String) :=
  [ ("parameter unit definition and nontriviality", "REUSED DEF/PROVED", "tateParameterUnit / tateParameterUnit_ne_one")
  , ("power compatibility", "REUSED PROVED", "tateParameterUnit_pow")
  , ("Galois/deck action fixes the unit and its zpowers subgroup", "REUSED PROVED", "tateParameterUnit_algEquiv_map / tateParameterDeckSubgroup_algEquiv_map")
  , ("consumer bundle", "COMPOSED PROVED", "tateParameterUnit_deck_fixed_consumer, tateParameterUnit_pow_consumer")
  , ("curve-indexed uniformization structure (ellipticity/coordinate change/point uniformization)", "REUSED DEF", "CurveIndexedTateUniformization (used by FreyTate consumer layer)") ]

theorem tateParameterUnitRows_length : tateParameterUnitRows.length = 5 := rfl

#check tateParameterUnit_deck_fixed_consumer
#check tateParameterUnit_pow_consumer
#check tateParameterUnitRows_length

end LeanFormal.IUT.XiFPaper.ShehddTateParameterUnitConsumerActualAdapted
end
