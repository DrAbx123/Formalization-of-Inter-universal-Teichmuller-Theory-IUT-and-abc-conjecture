/-
Copyright (c) 2026 LeanFormal contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanFormal contributors
-/
import tmp.sheaf.xif.paper.S2502FiniteLevelODiamondActual
import tmp.sheaf.xif.paper.S2501UniversalCoverSystemActual
import tmp.sheaf.xif.paper.S2500CategoricalOtriangleActual

/-! # S2503: finite-level O^◃ maps into the global O^◃ carrier

For an intermediate field `L` of `AlgebraicClosure ℚ_[p]`, the inclusion
`L → AlgebraicClosure ℚ_[p]` carries the integral closure of the `p`-adic
valuation ring in `L` into its integral closure in the algebraic closure.
This file constructs the induced actual ring homomorphism

`S2502IntegralClosure p L →+* LocalAlgebraicIntegerRing p`

and the induced monoid homomorphism on nonzero divisors

`S2502ODiamond p L →* S2500ODiamond p`.

Integrality is transported with `IsIntegral.map` (the `ℚ_[p]`-algebra map
`IntermediateField.val` with the scalar tower over `Z_p`); injectivity of
the field inclusion gives nonzero preservation.

The same argument applies to the actual field inclusions
`IntermediateField.inclusion h` for `M ≤ L`.  This yields actual transition
maps on the finite Galois index of `S2501`, hence an actual
`S2500ProSystem` whose objects are the finite-level O^◃ carriers, together
with actual maps from each finite-level carrier to the global carrier.

The O^▷ submonoid/pro-generator layer and the realified `rho_v` maps of
`S2500UniversalCoverRequired`/`S2500RhoVRequired` are **not** constructed
here; see the final section of this file for the exact missing data.  In
particular the trivial choice of pro-generator `1` would be a fake universal
cover and is deliberately not used. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 2000000

open LeanFormal.IUT
open LeanFormal.IUT.LocalIntegralMonoid
open LeanFormal.IUT.XiFPaper.S2500CategoricalOtriangleActual
open LeanFormal.IUT.XiFPaper.S2501UniversalCoverSystemActual
open LeanFormal.IUT.XiFPaper.S2502FiniteLevelODiamondActual
open scoped nonZeroDivisors

namespace LeanFormal.IUT.XiFPaper.S2503FiniteLevelToODiamondActual

variable (p : Nat) [Fact (Nat.Prime p)]

/-- The `p`-adic valuation ring `Z_p`, viewed as a subring of `Q_p`.  This is
the common base of the integral closures appearing in `S2502` and `S2500`. -/
noncomputable abbrev S2503BaseRing : Subring ℚ_[p] :=
  Valuation.integer (ValuativeRel.valuation ℚ_[p])

/-! ## Integrality along the field inclusions -/

/-- An element of the finite-level integral closure in `L`, seen as an element
of the algebraic closure, is integral over the base valuation ring. -/
theorem S2503_isIntegral_val
    (L : IntermediateField ℚ_[p] (AlgebraicClosure ℚ_[p]))
    {x : L.1} (hx : x ∈ S2502IntegralClosure p L) :
    IsIntegral (S2503BaseRing p) ((IntermediateField.val L) x) := by
  have hx' : IsIntegral (S2503BaseRing p) x := hx
  haveI : IsScalarTower (S2503BaseRing p) ℚ_[p] L.1 :=
    IsScalarTower.of_algebraMap_eq (R := S2503BaseRing p) (S := ℚ_[p])
      (A := L.1) fun _ => rfl
  haveI : IsScalarTower (S2503BaseRing p) ℚ_[p] (AlgebraicClosure ℚ_[p]) :=
    IsScalarTower.of_algebraMap_eq (R := S2503BaseRing p) (S := ℚ_[p])
      (A := AlgebraicClosure ℚ_[p]) fun _ => rfl
  exact IsIntegral.map (IntermediateField.val L) hx'

/-- An element of the finite-level integral closure in `M` stays integral
after the inclusion `M → L` of intermediate fields. -/
theorem S2503_isIntegral_inclusion
    {M L : IntermediateField ℚ_[p] (AlgebraicClosure ℚ_[p])} (h : M ≤ L)
    {x : M.1} (hx : x ∈ S2502IntegralClosure p M) :
    IsIntegral (S2503BaseRing p) ((IntermediateField.inclusion h) x) := by
  have hx' : IsIntegral (S2503BaseRing p) x := hx
  haveI : IsScalarTower (S2503BaseRing p) ℚ_[p] M.1 :=
    IsScalarTower.of_algebraMap_eq (R := S2503BaseRing p) (S := ℚ_[p])
      (A := M.1) fun _ => rfl
  haveI : IsScalarTower (S2503BaseRing p) ℚ_[p] L.1 :=
    IsScalarTower.of_algebraMap_eq (R := S2503BaseRing p) (S := ℚ_[p])
      (A := L.1) fun _ => rfl
  exact IsIntegral.map (IntermediateField.inclusion h) hx'

/-! ## The ring homomorphism to the global integral closure -/

/-- The actual ring homomorphism from the integral closure in `L` to the
integral closure in `AlgebraicClosure ℚ_[p]`, induced by the inclusion
`L → AlgebraicClosure ℚ_[p]`. -/
noncomputable def S2503IntegralClosureMap
    (L : IntermediateField ℚ_[p] (AlgebraicClosure ℚ_[p])) :
    S2502IntegralClosure p L →+* LocalAlgebraicIntegerRing p where
  toFun x :=
    ⟨(IntermediateField.val L) (x : L.1), S2503_isIntegral_val p L x.2⟩
  map_zero' := Subtype.ext (by
    simp only [Subring.coe_zero, map_zero, Subalgebra.coe_zero])
  map_one' := Subtype.ext (by
    simp only [Subring.coe_one, map_one, Subalgebra.coe_one])
  map_add' x y := Subtype.ext (by
    simp only [Subring.coe_add, map_add, Subalgebra.coe_add])
  map_mul' x y := Subtype.ext (by
    simp only [Subring.coe_mul, map_mul, Subalgebra.coe_mul])

@[simp]
theorem S2503IntegralClosureMap_coe
    (L : IntermediateField ℚ_[p] (AlgebraicClosure ℚ_[p]))
    (x : S2502IntegralClosure p L) :
    ((S2503IntegralClosureMap p L x : LocalAlgebraicIntegerRing p) :
        AlgebraicClosure ℚ_[p]) =
      (IntermediateField.val L) (x : L.1) :=
  rfl

theorem S2503IntegralClosureMap_injective
    (L : IntermediateField ℚ_[p] (AlgebraicClosure ℚ_[p])) :
    Function.Injective (S2503IntegralClosureMap p L) := by
  intro x y hxy
  have hval : (IntermediateField.val L) (x : L.1) =
      (IntermediateField.val L) (y : L.1) := by
    simpa only [S2503IntegralClosureMap_coe] using
      congrArg (fun z : LocalAlgebraicIntegerRing p =>
        (z : AlgebraicClosure ℚ_[p])) hxy
  exact Subtype.ext (Subtype.ext hval)

/-! ## The monoid homomorphism on nonzero divisors -/

/-- Nonzero preservation: an element of the finite-level O^◃ carrier maps to a
nonzero element of the global integral closure. -/
theorem S2503IntegralClosureMap_ne_zero
    (L : IntermediateField ℚ_[p] (AlgebraicClosure ℚ_[p]))
    (x : S2502ODiamond p L) :
    S2503IntegralClosureMap p L (x : S2502IntegralClosure p L) ≠ 0 :=
  map_ne_zero_of_mem_nonZeroDivisors (S2503IntegralClosureMap p L)
    (S2503IntegralClosureMap_injective p L) x.2

/-- The actual monoid homomorphism from the finite-level O^◃ carrier to the
global O^◃ carrier, induced by the inclusion of `L` into the closure. -/
noncomputable def S2503ODiamondMap
    (L : IntermediateField ℚ_[p] (AlgebraicClosure ℚ_[p])) :
    S2502ODiamond p L →* S2500ODiamond p where
  toFun x :=
    ⟨S2503IntegralClosureMap p L (x : S2502IntegralClosure p L),
      map_mem_nonZeroDivisors (S2503IntegralClosureMap p L)
        (S2503IntegralClosureMap_injective p L) x.2⟩
  map_one' := Subtype.ext (map_one (S2503IntegralClosureMap p L))
  map_mul' x y :=
    Subtype.ext (map_mul (S2503IntegralClosureMap p L)
      (x : S2502IntegralClosure p L) (y : S2502IntegralClosure p L))

@[simp]
theorem S2503ODiamondMap_coe
    (L : IntermediateField ℚ_[p] (AlgebraicClosure ℚ_[p]))
    (x : S2502ODiamond p L) :
    ((S2503ODiamondMap p L x : S2500ODiamond p) :
        LocalAlgebraicIntegerRing p) =
      S2503IntegralClosureMap p L (x : S2502IntegralClosure p L) :=
  rfl

/-! ## Finite-level transition maps -/

/-- The actual ring homomorphism between finite-level integral closures
induced by an inclusion `M ≤ L` of intermediate fields. -/
noncomputable def S2503FiniteLevelMap
    {M L : IntermediateField ℚ_[p] (AlgebraicClosure ℚ_[p])} (h : M ≤ L) :
    S2502IntegralClosure p M →+* S2502IntegralClosure p L where
  toFun x :=
    ⟨(IntermediateField.inclusion h) (x : M.1),
      S2503_isIntegral_inclusion p h x.2⟩
  map_zero' := Subtype.ext (by
    simp only [Subring.coe_zero, map_zero])
  map_one' := Subtype.ext (by
    simp only [Subring.coe_one, map_one])
  map_add' x y := Subtype.ext (by
    simp only [Subring.coe_add, map_add])
  map_mul' x y := Subtype.ext (by
    simp only [Subring.coe_mul, map_mul])

@[simp]
theorem S2503FiniteLevelMap_coe
    {M L : IntermediateField ℚ_[p] (AlgebraicClosure ℚ_[p])} (h : M ≤ L)
    (x : S2502IntegralClosure p M) :
    ((S2503FiniteLevelMap p h x : S2502IntegralClosure p L) : L.1) =
      (IntermediateField.inclusion h) (x : M.1) :=
  rfl

theorem S2503FiniteLevelMap_injective
    {M L : IntermediateField ℚ_[p] (AlgebraicClosure ℚ_[p])} (h : M ≤ L) :
    Function.Injective (S2503FiniteLevelMap p h) := by
  intro x y hxy
  have hval : (IntermediateField.inclusion h) (x : M.1) =
      (IntermediateField.inclusion h) (y : M.1) := by
    simpa only [S2503FiniteLevelMap_coe] using
      congrArg (fun z : S2502IntegralClosure p L => (z : L.1)) hxy
  exact Subtype.ext (IntermediateField.inclusion_injective h hval)

/-- The actual monoid homomorphism between finite-level O^◃ carriers induced
by an inclusion `M ≤ L` of intermediate fields. -/
noncomputable def S2503FiniteLevelDiamondMap
    {M L : IntermediateField ℚ_[p] (AlgebraicClosure ℚ_[p])} (h : M ≤ L) :
    S2502ODiamond p M →* S2502ODiamond p L where
  toFun x :=
    ⟨S2503FiniteLevelMap p h (x : S2502IntegralClosure p M),
      map_mem_nonZeroDivisors (S2503FiniteLevelMap p h)
        (S2503FiniteLevelMap_injective p h) x.2⟩
  map_one' := Subtype.ext (map_one (S2503FiniteLevelMap p h))
  map_mul' x y :=
    Subtype.ext (map_mul (S2503FiniteLevelMap p h)
      (x : S2502IntegralClosure p M) (y : S2502IntegralClosure p M))

/-! ## The actual finite-level transition system -/

/-- The actual transition system on the finite Galois intermediate fields of
`S2501`, whose objects are the finite-level O^◃ carriers `S2502ODiamond p L`
and whose transitions are the actual monoid homomorphisms induced by the
field inclusions. -/
noncomputable def S2503FiniteProSystem : S2500ProSystem where
  Index := S2501Index p
  le := S2501Le p
  le_refl := S2501Le_refl p
  le_trans := fun hLM hMN => S2501Le_trans p hLM hMN
  obj := fun L => S2502ODiamond p L.1
  transition := fun {L M} h x => S2503FiniteLevelDiamondMap p h x
  transition_refl := by
    intro L x
    apply Subtype.ext
    apply Subtype.ext
    apply Subtype.ext
    rfl

/-- The actual map from each finite-level O^◃ carrier to the global O^◃
carrier. -/
noncomputable def S2503FiniteToGlobal (L : S2501Index p) :
    S2502ODiamond p L.1 →* S2500ODiamond p :=
  S2503ODiamondMap p L.1

/-- The finite-level transitions are compatible with the maps to the global
carrier: the square with the inclusion of intermediate fields commutes. -/
theorem S2503FiniteToGlobal_compat
    {M L : IntermediateField ℚ_[p] (AlgebraicClosure ℚ_[p])} (h : M ≤ L)
    (x : S2502ODiamond p M) :
    S2503ODiamondMap p L (S2503FiniteLevelDiamondMap p h x) =
      S2503ODiamondMap p M x := by
  apply Subtype.ext
  apply Subtype.ext
  rfl

/-! ## Exact missing data

The constructions above are the actual O^◃ layer.  They do **not** produce an
inhabitant of `S2500UniversalCoverRequired`.  That structure additionally
requires

* `oTriangleSubmonoid : ∀ i, Set (proSystem.obj i)`,
* `oTriangleGenerator : ∀ i, proSystem.obj i`,
* `oTriangleGenerator_mem` and `generator_compat`,

i.e. the literal O^▷ submonoid and compatible pro-generators of the universal
covering pro-object.  No source-correct pro-generator is available in this
file; choosing the unit `1` at every level would satisfy the fields
vacuously and would be a fake universal cover, so it is deliberately omitted.

Likewise the realified `rho_v` maps of `S2500RhoVRequired` are not
constructed.  What remains is exactly this O^▷/pro-generator/rho_v data; the
O^◃ carrier level, its finite-level transition system, and its maps to the
global carrier are actual in this file. -/

#check S2503IntegralClosureMap
#check S2503IntegralClosureMap_injective
#check S2503IntegralClosureMap_ne_zero
#check S2503ODiamondMap
#check S2503FiniteLevelDiamondMap
#check S2503FiniteProSystem
#check S2503FiniteToGlobal
#check S2503FiniteToGlobal_compat
#check S2500UniversalCoverRequired

end LeanFormal.IUT.XiFPaper.S2503FiniteLevelToODiamondActual
end
