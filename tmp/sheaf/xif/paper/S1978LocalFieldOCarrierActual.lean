/-
Copyright (c) 2026 LeanFormal contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import tmp.sheaf.xif.paper.S1967OUnitsMuActual
import tmp.sheaf.xif.paper.IPLAPTDataActual
import LeanFormal.IUT.Foundations.LocalFields.IntegralUnits
import LeanFormal.IUT.Foundations.LocalFields.IntegralUnitLogarithmGalois
import LeanFormal.IUT.IUTII.Frobenioid.LocalIntegralFPrimeStrip
import LeanFormal.IUT.IUTII.Frobenioid.SourceKappaOrbitFactorizationProvider

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000

/-!
# S1978: the actual local-field O^× carrier on the S1895 paper input

Layer: **O** (original Theta-link / q-pilot), direct worker of S1967.

## The gap addressed

S1967 proves that the S1895 input is built on the S1487 shear strip, whose
value monoid is `SourceHaarActualValueMonoid` (the additive monoid of
nonpositive reals), so its unit group is trivial and the reduced `kappa^{x mu}`
representatives are identity completions in content.  It then constructs a
local-field model `LocalOUnits p = (AlgebraicClosure Q_p)^x` but does **not**
attach any local unit carrier to the S1895 place type.  This file supplies
that carrier.

## What is constructed here

1. **The actual local O^× carrier at every S1895 place.**  For a rational prime
   `p`, the carrier is

     `LocalOFieldUnits p := (Integers (AlgebraicClosure Q_p))^x`,

   the units of the actual integral closure of the p-adic valuation ring, i.e.
   the actual `O^×` of the local field.  This is not an abstract stand-in: the
   ring is Mathlib's `IntegralUnits.Integers` of the actual algebraic closure,
   and the unit group is its actual unit group.

2. **The actual local Galois action.**  `LocalOFieldUnitsAction p` is the
   action of `LocalAbsoluteGalois p` by `localGaloisUnitMap`, the actual
   automorphism action on integral units.  The quotient
   `LocalOFieldUnitsMu p = TimesMuQuotient (LocalOFieldUnits p)` carries the
   descended action.

3. **Genuine nontriviality.**  `1 + p` is an actual integral unit
   (`localOFieldUnit`).  It is not a root of unity: if `(1+p)^n = 1` in the
   algebraic closure, injectivity of the map from `Q` forces `(1+p)^n = 1` in
   `Q`, impossible because `1 < 1+p`.  Hence
   `localOFieldUnit_quotient_ne_one` and `LocalOFieldUnitsMu_nontrivial`: the
   actual `O^{x mu}` quotient is nontrivial at every prime.  This is the
   property that the S1487 carrier lacks.

4. **An actual F-prime-strip on the S1895 place type.**  `localOFieldStrip` is
   an `FPrimeStrip (FinitePrimePlace 2 7)` whose value monoid at `v` is the
   actual local O^× group at `v.1`, whose `Pi`/`G` are the actual local
   absolute Galois groups, whose action is the actual local Galois action, and
   whose degree is the actual norm-log degree.  The canonical
   `KappaOrbitUnitsActionDatum` on this strip has the actual O^× group as its
   module, and the canonical group-units equivalence
   `localOFieldStrip_unitsAction_groupUnitsEquiv` identifies its action with
   the actual action on `O^×`.

5. **Attachment to the S1895 boundary/strip slots and a paper object.**
   `localOFieldTheater`, `localOFieldBoundary` and
   `localOFieldBoundaryStrip` replace the S1487 value monoid by the actual
   local O^× strip in the very `OrigXiFPaperBoundaryStripFields` package used
   by `S1895PaperO`, keeping the S1895 input, its one-column carrier, its
   scalar and its route-normal-form data.  `localOFieldPaperO` is the
   corresponding `PaperQPilotObject` on the actual local strip; its strip
   anchors, (1,0) label, local F-times-mu slot, local log-Kummer slot, actual
   S1679 line-bundle slot and actual q-pilot scalar slot are all proved.  The
   two strip/Kummer slots are explicitly the local analogues, not the paper's
   identifications.

6. **No identification with the degenerate carrier.**  No `FPrimeStripEquiv`
   exists between `localOFieldStrip` and the S1487 shear core, and none between
   `localOFieldStrip` and `(S1895PaperO D).strip`.  Consequently the actual
   local O^× carrier cannot be identified with the degenerate S1895 value
   monoid; the only way to use it in the S1895 paper object is to rebase the
   input.

## The exact first missing

`S1978RebasedPaperInput D` is the exact missing object: an `OriginalInput` with
the same initial data as the S1895 input whose `(1,0)` F-prime-strip is
`localOFieldStrip`.  `S1978RebasedPaperO D` adds the corresponding
`PaperQPilotObject`.  The present S1527 input does not satisfy this
(`paperInput_core_ne_local`), and no equivalence to its strip exists
(`no_localOFieldStrip_equiv_paperO`), so this is not a cosmetic restatement.
The type is recorded, not inhabited: constructing the rebased S1527
Hodge-theater family/boundary and the paper's group-theoretic actor
`G |-> O^×(G)`, `G |-> O^×μ(G)` (IUT II, Example 1.8, (iii), (iv)) remains
the missing construction.

## Scope of the place model

The S1895 place type is `FinitePrimePlace 2 7`.  At a place `v`, the carrier
constructed here is the local model at the rational prime `v.1` (the
`Q_p`-model used by S1967's `LocalOUnits p` and by the local-integral
F-prime-strip), not the completion of the number field at the place
`QPlace v`.  It is the actual integral unit group of the actual algebraic
closure of `Q_p`, with the actual local Galois action; the completion-level
carrier of S1949 and the present `Q_p`-model are different actual carriers,
and no equivalence between them is asserted here.  The rebased-input missing
type of section 7 uses this `Q_p`-model strip.

No `sorry`, `axiom`, `True`/`PUnit` slot, empty type, arbitrary inhabitant or
`Nonempty` gate is used.  The missing object is recorded as a structure with no
inhabitant.
-/

namespace LeanFormal.IUT.XiFPaper.S1978LocalFieldOCarrierActual

open LeanFormal.IUT
open LeanFormal.IUT.LocalFieldIntegralUnits
open LeanFormal.IUT.LocalFieldLogarithm
open LeanFormal.IUT.XiFPaper.S1967OUnitsMuActual
open LeanFormal.IUT.XiFPaper.S1951KummerEvaluationSquareActual
open LeanFormal.IUT.XiFPaper.S1895OIdentificationsActual
open LeanFormal.IUT.XiFPaper.S1487OQPilotScalarEqualityActual
open LeanFormal.IUT.XiFPaper.OrigXiFPaperBoundaryStrip
open LeanFormal.IUT.XiFPaper.S1679CompleteODCarrierActual
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.IPLAPTDataActual
open LeanFormal.IUT.ArithmeticQPilotLogVolume

/-! ## 1. The actual local O^× carrier -/

/-- The actual integral unit group of the algebraic closure of `Q_p`: the
local-field `O^×` carrier. -/
noncomputable abbrev LocalOFieldUnits (p : Nat) [Fact (Nat.Prime p)] : Type :=
  (Integers (AlgebraicClosure ℚ_[p]))ˣ

/-- The local `O^×` carrier at a place of the S1895 one-column. -/
noncomputable abbrev LocalOFieldUnitsAt (v : PaperV) : Type :=
  @LocalOFieldUnits v.1 ⟨v.prime⟩

/-- The actual local Galois action on the integral unit group. -/
noncomputable def localOFieldUnitsMulAut (p : Nat) [Fact (Nat.Prime p)]
    (σ : LocalAbsoluteGalois p) : MulAut (LocalOFieldUnits p) where
  toFun := localGaloisUnitMap σ
  invFun := localGaloisUnitMap σ⁻¹
  left_inv u := by
    have h : localGaloisUnitMap (σ⁻¹ * σ) u = u := by
      rw [inv_mul_cancel]
      exact localGaloisUnitMap_one (K := AlgebraicClosure ℚ_[p]) (p := p) u
    rwa [localGaloisUnitMap_mul] at h
  right_inv u := by
    have h : localGaloisUnitMap (σ * σ⁻¹) u = u := by
      rw [mul_inv_cancel]
      exact localGaloisUnitMap_one (K := AlgebraicClosure ℚ_[p]) (p := p) u
    rwa [localGaloisUnitMap_mul] at h
  map_mul' u v := (localGaloisUnitMap σ).map_mul u v

/-- The actual action of the local absolute Galois group on `O^×`. -/
noncomputable def LocalOFieldUnitsAction (p : Nat) [Fact (Nat.Prime p)] :
    LocalAbsoluteGalois p →* MulAut (LocalOFieldUnits p) where
  toFun := localOFieldUnitsMulAut p
  map_one' := by
    apply MulEquiv.ext
    intro u
    exact localGaloisUnitMap_one (K := AlgebraicClosure ℚ_[p]) (p := p) u
  map_mul' σ τ := by
    apply MulEquiv.ext
    intro u
    exact localGaloisUnitMap_mul (K := AlgebraicClosure ℚ_[p]) (p := p) σ τ u

/-- The place-indexed actual action. -/
noncomputable abbrev LocalOFieldUnitsActionAt (v : PaperV) :
    @LocalAbsoluteGalois v.1 ⟨v.prime⟩ →* MulAut (LocalOFieldUnitsAt v) :=
  @LocalOFieldUnitsAction v.1 ⟨v.prime⟩

/-- The actual `O^×μ` quotient on the local carrier. -/
noncomputable abbrev LocalOFieldUnitsMu (p : Nat) [Fact (Nat.Prime p)] : Type :=
  TimesMuQuotient (LocalOFieldUnits p)

/-- The place-indexed `O^×μ` quotient. -/
noncomputable abbrev LocalOFieldUnitsMuAt (v : PaperV) : Type :=
  @LocalOFieldUnitsMu v.1 ⟨v.prime⟩

/-- The descended action on the actual local `O^×μ` quotient. -/
noncomputable def LocalOFieldUnitsMuAction (p : Nat) [Fact (Nat.Prime p)] :
    LocalAbsoluteGalois p →* MulAut (LocalOFieldUnitsMu p) :=
  TimesMuQuotient.action (LocalOFieldUnitsAction p)

/-- The place-indexed descended action. -/
noncomputable abbrev LocalOFieldUnitsMuActionAt (v : PaperV) :
    @LocalAbsoluteGalois v.1 ⟨v.prime⟩ →* MulAut (LocalOFieldUnitsMuAt v) :=
  @LocalOFieldUnitsMuAction v.1 ⟨v.prime⟩

@[simp] theorem LocalOFieldUnitsMuAction_quotientMap
    (p : Nat) [Fact (Nat.Prime p)] (g : LocalAbsoluteGalois p)
    (u : LocalOFieldUnits p) :
    LocalOFieldUnitsMuAction p g (TimesMuQuotient.quotientMap u) =
      TimesMuQuotient.quotientMap (LocalOFieldUnitsAction p g u) := rfl

/-! ## 2. The concrete non-torsion unit `1 + p` -/

/-- `1 + p` as an element of the algebraic closure. -/
def localOFieldOnePlusPClosed (p : Nat) [Fact (Nat.Prime p)] :
    AlgebraicClosure ℚ_[p] :=
  algebraMap ℚ_[p] (AlgebraicClosure ℚ_[p]) (1 + (p : ℚ_[p]))

/-- `1 + p` has p-adic norm one. -/
theorem localOFieldOnePlusPClosed_norm (p : Nat) [Fact (Nat.Prime p)] :
    ‖localOFieldOnePlusPClosed p‖ = 1 := by
  unfold localOFieldOnePlusPClosed
  rw [norm_algebraMap']
  have h : (1 + (p : ℚ_[p])) = ((p + 1 : ℕ) : ℚ_[p]) := by
    push_cast
    ring
  rw [h, Padic.norm_natCast_eq_one_iff]
  exact (Nat.coprime_self_add_right).mpr (Nat.coprime_one_right p)

/-- The actual integral unit `1 + p` of the local field. -/
def localOFieldUnit (p : Nat) [Fact (Nat.Prime p)] : LocalOFieldUnits p :=
  unitOfNormOne ⟨localOFieldOnePlusPClosed p,
    localOFieldOnePlusPClosed_norm p⟩

/-- The place-indexed version. -/
noncomputable abbrev localOFieldUnitAt (v : PaperV) : LocalOFieldUnitsAt v :=
  @localOFieldUnit v.1 ⟨v.prime⟩

/-- The underlying algebraic-closure value of `1 + p`. -/
theorem localOFieldUnit_coe (p : Nat) [Fact (Nat.Prime p)] :
    (((localOFieldUnit p : LocalOFieldUnits p) :
      Integers (AlgebraicClosure ℚ_[p])) : AlgebraicClosure ℚ_[p]) =
      localOFieldOnePlusPClosed p := rfl

/-- The unit `1 + p` is not the identity. -/
theorem localOFieldUnit_ne_one (p : Nat) [Fact (Nat.Prime p)] :
    localOFieldUnit p ≠ 1 := by
  intro h
  have hval : localOFieldOnePlusPClosed p = 1 := by
    have h' := congrArg (fun u : LocalOFieldUnits p =>
      (((u : Integers (AlgebraicClosure ℚ_[p])) : AlgebraicClosure ℚ_[p]))) h
    simpa [localOFieldUnit_coe] using h'
  unfold localOFieldOnePlusPClosed at hval
  have hq : (1 + (p : ℚ_[p])) = 1 :=
    (algebraMap ℚ_[p] (AlgebraicClosure ℚ_[p])).injective
      (by simpa using hval)
  have hp : (p : ℚ_[p]) = 0 := by
    have := congrArg (fun x : ℚ_[p] => x - 1) hq
    simpa using this
  have hp' : p = 0 := by exact_mod_cast hp
  exact (Fact.out : Nat.Prime p).ne_zero hp'

/-- `1 + p` is not a root of unity: otherwise its rational value would be one. -/
theorem localOFieldUnit_not_isOfFinOrder (p : Nat) [Fact (Nat.Prime p)] :
    ¬ IsOfFinOrder (localOFieldUnit p) := by
  rw [isOfFinOrder_iff_pow_eq_one]
  rintro ⟨n, hnpos, hpow⟩
  have hval : (localOFieldOnePlusPClosed p) ^ n = 1 := by
    have h := congrArg (fun u : LocalOFieldUnits p =>
      (((u : Integers (AlgebraicClosure ℚ_[p])) : AlgebraicClosure ℚ_[p])))
      hpow
    simpa [localOFieldUnit_coe] using h
  let q : ℚ := 1 + (p : ℚ)
  have hq : algebraMap ℚ (AlgebraicClosure ℚ_[p]) q =
      localOFieldOnePlusPClosed p := by
    unfold localOFieldOnePlusPClosed
    rw [show (1 + (p : ℚ_[p])) = algebraMap ℚ ℚ_[p] q by
      simp only [q, map_add, map_one, map_natCast]]
    rw [IsScalarTower.algebraMap_apply ℚ ℚ_[p] (AlgebraicClosure ℚ_[p])]
  have hpowq : (algebraMap ℚ (AlgebraicClosure ℚ_[p]) q) ^ n = 1 := by
    rw [hq]
    exact hval
  have hqpow : algebraMap ℚ (AlgebraicClosure ℚ_[p]) (q ^ n) = 1 := by
    rw [map_pow, hpowq]
  have hqeq : q ^ n = 1 :=
    (algebraMap ℚ (AlgebraicClosure ℚ_[p])).injective (by simpa using hqpow)
  have hqgt : (1 : ℚ) < q := by
    have hp : (1 : ℚ) < (p : ℚ) := by
      exact_mod_cast (Fact.out : Nat.Prime p).one_lt
    dsimp [q]
    linarith
  have hgt : (1 : ℚ) < q ^ n := one_lt_pow₀ hqgt hnpos.ne'
  linarith

/-- The quotient class of the non-torsion unit `1 + p` is nontrivial. -/
theorem localOFieldUnit_quotient_ne_one (p : Nat) [Fact (Nat.Prime p)] :
    TimesMuQuotient.quotientMap (localOFieldUnit p) ≠ 1 := by
  intro h
  apply localOFieldUnit_not_isOfFinOrder p
  have hmem : localOFieldUnit p ∈
      MonoidHom.ker (TimesMuQuotient.quotientMap
        (U := LocalOFieldUnits p)) :=
    MonoidHom.mem_ker.mpr h
  have htors : localOFieldUnit p ∈ CommGroup.torsion (LocalOFieldUnits p) := by
    simpa [TimesMuQuotient.quotientMap_ker] using hmem
  exact (CommGroup.mem_torsion _).mp htors

/-- **The actual local `O^×μ` quotient is nontrivial at every prime.** -/
theorem LocalOFieldUnitsMu_nontrivial (p : Nat) [Fact (Nat.Prime p)] :
    (TimesMuQuotient.quotientMap (localOFieldUnit p) :
      LocalOFieldUnitsMu p) ≠ 1 :=
  localOFieldUnit_quotient_ne_one p

/-- The place-indexed nontriviality statement. -/
theorem LocalOFieldUnitsMuAt_nontrivial (v : PaperV) :
    (TimesMuQuotient.quotientMap (@localOFieldUnit v.1 ⟨v.prime⟩) :
      LocalOFieldUnitsMuAt v) ≠ 1 :=
  @LocalOFieldUnitsMu_nontrivial v.1 ⟨v.prime⟩

/-! ## 3. The actual local `O^×` F-prime-strip over the S1895 places -/

/-- The canonical multiplicative equivalence between a group and its unit
group: every element of a group is a unit. -/
noncomputable def groupUnitsEquiv (G : Type*) [Group G] : G ≃* Gˣ where
  toFun g := ⟨g, g⁻¹, mul_inv_cancel g, inv_mul_cancel g⟩
  invFun u := u
  left_inv g := rfl
  right_inv u := by ext; rfl
  map_mul' g h := by ext; rfl

/-- The actual norm-log degree on the local integral units: every integral unit
has norm one, so the degree is the trivial multiplicative character. -/
noncomputable def localOFieldUnitsDegree (p : Nat) [Fact (Nat.Prime p)] :
    LocalOFieldUnits p →* Multiplicative ℝ :=
  (localUnitNormDegreeFor p).comp
    (Units.map (Integers (AlgebraicClosure ℚ_[p])).subtype.toMonoidHom)

/-- The place-indexed degree. -/
noncomputable abbrev LocalOFieldUnitsDegreeAt (v : PaperV) :
    LocalOFieldUnitsAt v →* Multiplicative ℝ :=
  @localOFieldUnitsDegree v.1 ⟨v.prime⟩

/-- **The actual local `O^×` F-prime-strip on the S1895 place type.**  At each
place `v` the value monoid is the actual local `O^×` group, the group is the
actual local absolute Galois group, the action is the actual Galois action, and
the degree is the actual norm-log degree. -/
noncomputable def localOFieldStrip : FPrimeStrip PaperV where
  Pi := fun v => @LocalAbsoluteGalois v.1 ⟨v.prime⟩
  groupPi := fun v => inferInstance
  G := fun v => @LocalAbsoluteGalois v.1 ⟨v.prime⟩
  groupG := fun v => inferInstance
  proj := fun v => MonoidHom.id _
  proj_surjective := fun v => Function.surjective_id
  Mon := fun v => LocalOFieldUnitsAt v
  commMonoidMon := fun v => inferInstance
  action := fun v => LocalOFieldUnitsActionAt v
  degree := fun v => LocalOFieldUnitsDegreeAt v

/-- The value monoid of the local strip is the actual `O^×` carrier. -/
theorem localOFieldStrip_Mon (v : PaperV) :
    localOFieldStrip.Mon v = LocalOFieldUnitsAt v := rfl

/-- The group of the local strip is the actual local absolute Galois group. -/
theorem localOFieldStrip_Pi (v : PaperV) :
    localOFieldStrip.Pi v = @LocalAbsoluteGalois v.1 ⟨v.prime⟩ := rfl

@[simp] theorem localOFieldStrip_proj (v : PaperV)
    (g : localOFieldStrip.Pi v) :
    localOFieldStrip.proj v g = g := rfl

/-- The strip action is the actual local Galois action. -/
theorem localOFieldStrip_action (v : PaperV)
    (g : localOFieldStrip.Pi v) (u : localOFieldStrip.Mon v) :
    localOFieldStrip.action v g u = LocalOFieldUnitsActionAt v g u := rfl

/-- The canonical group-units equivalence intertwines the actual action on
`O^×` with the strip's units action. -/
theorem localOFieldStrip_unitsAction_groupUnitsEquiv (v : PaperV)
    (g : localOFieldStrip.Pi v) (u : LocalOFieldUnitsAt v) :
    groupUnitsEquiv (LocalOFieldUnitsAt v) (LocalOFieldUnitsActionAt v g u) =
      localOFieldStrip.unitsAction v g
        (groupUnitsEquiv (LocalOFieldUnitsAt v) u) := by
  ext
  rfl

/-! ## 4. The local product Galois group and the canonical κ-orbit datum -/

/-- The actual product of the local Galois groups over the S1895 places. -/
abbrev LocalOFieldGaloisProduct : Type :=
  (v : PaperV) → @LocalAbsoluteGalois v.1 ⟨v.prime⟩

/-- The product is a group. -/
instance : Group LocalOFieldGaloisProduct := Pi.group

/-- The fallback topology, exactly as the existing source interface uses for
product groups; it is not the paper's profinite topology. -/
instance : TopologicalSpace LocalOFieldGaloisProduct := ⊥

/-- The evaluation factorization at one place. -/
noncomputable def localOFieldFactorization (v : PaperV) :
    LocalOFieldGaloisProduct →* localOFieldStrip.Pi v :=
  Pi.evalMonoidHom _ v

@[simp] theorem localOFieldFactorization_apply (v : PaperV)
    (g : LocalOFieldGaloisProduct) :
    localOFieldFactorization v g = g v := rfl

/-- The canonical κ-orbit datum of IUT II, Definition 4.9, on the actual local
`O^×` strip: source module the actual local `O^×` group, source action the
actual local Galois action, factor the evaluation at the place. -/
noncomputable def localOFieldKappaDatum :
    KappaOrbitUnitsActionDatum LocalOFieldGaloisProduct localOFieldStrip :=
  KappaOrbitUnitsActionDatum.canonicalDatumOfFactorization
    localOFieldFactorization

/-- The source module of the canonical datum is the units of the actual `O^×`
group, canonically the actual `O^×` group itself. -/
theorem localOFieldKappaDatum_sourceUnits (v : PaperV) :
    localOFieldKappaDatum.sourceUnits v = (LocalOFieldUnitsAt v)ˣ := rfl

/-- The source action of the canonical datum is the actual local Galois action,
transported to the unit group of `O^×`. -/
theorem localOFieldKappaDatum_sourceAction (v : PaperV) :
    localOFieldKappaDatum.sourceAction v =
      (localOFieldStrip.unitsAction v).comp
        (localOFieldFactorization v) := rfl

/-- The actual local `O^×` group is canonically the source module of the
datum. -/
noncomputable def localOFieldKappaSourceEquiv (v : PaperV) :
    LocalOFieldUnitsAt v ≃* localOFieldKappaDatum.sourceUnits v :=
  groupUnitsEquiv (LocalOFieldUnitsAt v)

/-- The canonical datum's source action is the actual local Galois action under
the canonical O^×-to-unit-group equivalence. -/
theorem localOFieldKappaDatum_sourceAction_equiv (v : PaperV)
    (g : LocalOFieldGaloisProduct) (u : LocalOFieldUnitsAt v) :
    localOFieldKappaSourceEquiv v (LocalOFieldUnitsActionAt v (g v) u) =
      localOFieldKappaDatum.sourceAction v g
        (localOFieldKappaSourceEquiv v u) := by
  change groupUnitsEquiv (LocalOFieldUnitsAt v)
      (LocalOFieldUnitsActionAt v (g v) u) =
    (localOFieldStrip.unitsAction v (localOFieldFactorization v g))
      (groupUnitsEquiv (LocalOFieldUnitsAt v) u)
  rw [← localOFieldStrip_unitsAction_groupUnitsEquiv]
  rfl

/-! ## 5. The local strip cannot be identified with the degenerate S1487 carrier -/

/-- No equivalence exists between the actual local `O^×` group and the units of
the nonpositive-real value monoid: the former contains the non-torsion unit
`1 + p`, the latter has a trivial unit group. -/
theorem no_localOFieldUnits_equiv_sourceHaarUnits
    (p : Nat) [Fact (Nat.Prime p)] :
    ¬ Nonempty (LocalOFieldUnits p ≃* (SourceHaarActualValueMonoid)ˣ) := by
  rintro ⟨e⟩
  haveI : Subsingleton ((SourceHaarActualValueMonoid)ˣ) :=
    sourceHaarActualValueMonoid_units_subsingleton
  have h1 : e (localOFieldUnit p) = 1 := Subsingleton.elim _ _
  exact localOFieldUnit_ne_one p (e.injective (by rw [h1, map_one]))

/-- No `FPrimeStripEquiv` exists between the actual local `O^×` strip and the
S1487 shear strip.  At the place 5 a strip equivalence would induce a monoid
equivalence between the actual local `O^×` groups and
`SourceHaarActualValueMonoid`, hence a unit-group equivalence, contradicting
the non-torsion unit `1 + 5`. -/
theorem no_localOFieldStrip_equiv_shear :
    ¬ Nonempty (FPrimeStripEquiv localOFieldStrip (S1487Strip 1 0)) := by
  letI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  rintro ⟨e⟩
  have hM : LocalOFieldUnits 5 ≃* SourceHaarActualValueMonoid := by
    change (localOFieldStrip.Mon s1895FivePlace) ≃*
      ((S1487Strip 1 0).Mon s1895FivePlace)
    exact e.isoMon s1895FivePlace
  have hU : Nonempty (LocalOFieldUnits 5 ≃*
      (SourceHaarActualValueMonoid)ˣ) :=
    ⟨(groupUnitsEquiv (LocalOFieldUnits 5)).trans (Units.mapEquiv hM)⟩
  exact no_localOFieldUnits_equiv_sourceHaarUnits 5 hU

/-- The S1895 paper object's strip is the S1487 shear core. -/
theorem paperO_strip_eq_shear (D : S1895PaperInput) :
    (S1895PaperO D).strip = S1487Strip 1 0 := rfl

/-- No `FPrimeStripEquiv` exists between the actual local `O^×` strip and the
strip of `S1895PaperO`. -/
theorem no_localOFieldStrip_equiv_paperO (D : S1895PaperInput) :
    ¬ Nonempty (FPrimeStripEquiv localOFieldStrip (S1895PaperO D).strip) := by
  rw [paperO_strip_eq_shear D]
  exact no_localOFieldStrip_equiv_shear

/-- The actual local `O^×` strip is not equal to the strip of `S1895PaperO`. -/
theorem paperO_strip_ne_local (D : S1895PaperInput) :
    (S1895PaperO D).strip ≠ localOFieldStrip := by
  intro h
  exact no_localOFieldStrip_equiv_paperO D
    ⟨h.symm ▸ FPrimeStripEquiv.refl (S1895PaperO D).strip⟩

/-- The S1895 input's `(1,0)` core is not the actual local `O^×` strip. -/
theorem paperInput_core_ne_local (D : S1895PaperInput) :
    (S1895PaperInput.I D).fPrimeStripAt 1 0 ≠ localOFieldStrip := by
  intro h
  have he : FPrimeStripEquiv localOFieldStrip
      ((S1895PaperInput.I D).fPrimeStripAt 1 0) :=
    h.symm ▸ FPrimeStripEquiv.refl
      ((S1895PaperInput.I D).fPrimeStripAt 1 0)
  exact no_localOFieldStrip_equiv_shear ⟨he⟩

/-! ## 6. Attachment to the S1895 boundary and strip slots -/

/-- The S1895 theater with its value monoid replaced by the actual local `O^×`
strip; arithmetic and theta data are unchanged. -/
noncomputable def localOFieldTheater (D : S1895PaperInput) :
    HodgeTheater D.l PaperV where
  arithmetic := (S1895PaperO D).boundary.theater.arithmetic
  primeStrip := localOFieldStrip
  thetaPacket := (S1895PaperO D).boundary.theater.thetaPacket

/-- The S1895 boundary with the local theater.  All non-strip fields are the
actual S1895 boundary's fields; the only change is `theater.primeStrip`. -/
noncomputable def localOFieldBoundary (D : S1895PaperInput) :
    SourceProcessionBoundary.Input
      (l := D.l) (V := PaperV)
      (Label := OrigXiFPaperLabel)
      (Choice := OrigXiFPaperChoice (S1895PaperInput.I D)) := by
  let old := (S1895PaperO D).boundary
  let T := localOFieldTheater D
  exact {
    theater := T
    history := HodgeTheaterHistory.singleton T
    carrier := old.carrier
    baseChoice := old.baseChoice
    baseChoice_eq := old.baseChoice_eq
    packetVolume := old.packetVolume
    packetVolume_eq_profile := old.packetVolume_eq_profile
    base_packetVolume_eq_theta := by
      simpa [T, localOFieldTheater] using old.base_packetVolume_eq_theta
    target_q := T.thetaPacket.q
    target_q_eq := rfl
    history_q_eq := rfl
    route_normal_form := old.route_normal_form
  }

/-- The boundary's source q-pilot strip is the actual local `O^×` strip. -/
theorem localOFieldBoundary_strip (D : S1895PaperInput) :
    sourceQPilotStrip (localOFieldBoundary D) = localOFieldStrip := rfl

/-- The local boundary package for the boundary/strip slots of a paper
object. -/
noncomputable def localOFieldBoundaryStrip (D : S1895PaperInput) :
    OrigXiFPaperBoundaryStripFields (l := D.l) (V := PaperV)
      (Label := OrigXiFPaperLabel)
      (Choice := OrigXiFPaperChoice (S1895PaperInput.I D)) where
  boundary := localOFieldBoundary D
  strip := localOFieldStrip
  strip_eq_source := rfl

/-- The strip anchor holds for the local boundary package. -/
theorem localOFieldBoundaryStrip_anchors (D : S1895PaperInput) :
    (localOFieldBoundaryStrip D).strip =
        sourceQPilotStrip (localOFieldBoundaryStrip D).boundary ∧
      (localOFieldBoundaryStrip D).boundary.target_q =
        (localOFieldBoundaryStrip D).boundary.theater.thetaPacket.q :=
  ⟨rfl, rfl⟩

/-- The S1895 one-column label survives the replacement; the one-column
carrier is unchanged. -/
noncomputable def localOFieldOneColumnLabel (D : S1895PaperInput) :
    S1895OneColumnLabel PaperV :=
  s1895OneColumnLabel PaperV (S1895PaperO D).oneColumn

theorem localOFieldOneColumnLabel_n (D : S1895PaperInput) :
    (localOFieldOneColumnLabel D).n = 1 := rfl

theorem localOFieldOneColumnLabel_m (D : S1895PaperInput) :
    (localOFieldOneColumnLabel D).m = 0 := rfl

theorem localOFieldOneColumnLabel_carrier (D : S1895PaperInput) :
    (localOFieldOneColumnLabel D).carrier = (S1895PaperO D).oneColumn := rfl


/-! ## 6b. A paper q-pilot object on the actual local O^× strip -/

/-- The paper-level F-times-mu identification *within* the local carrier: the
canonical times-mu strip of the local strip is fully poly-isomorphic to
itself.  This is the reduced local analogue of `S1895FTimesMuProp`; it does not
identify the local strip with the paper's q-pilot strip. -/
def localOFieldFTimesMuProp (D : S1895PaperInput) : Prop :=
  Nonempty (SourceFTimesMuPrimeStripFullPolyIsomorphism
    (SourceFTimesMuPrimeStrip.canonical localOFieldStrip)
    (SourceFTimesMuPrimeStrip.canonical localOFieldStrip))

/-- The local self-identification holds by the identity poly-isomorphism. -/
theorem localOFieldFTimesMuProp_holds (D : S1895PaperInput) :
    localOFieldFTimesMuProp D :=
  ⟨SourceFTimesMuPrimeStripFullPolyIsomorphism.id _⟩

/-- The local self log-Kummer proposition: the reduced local analogue of the
S1895 one-column correspondence, on the local O^× strip itself.  It is not
identified with the paper's one-column correspondence; that bridge is the
missing object of section 7. -/
def localOFieldSelfLogKummerProp (D : S1895PaperInput) : Prop :=
  Nonempty (SourceKummerArrow (SelfGroup localOFieldStrip)
    localOFieldStrip localOFieldStrip)

/-- The local self log-Kummer proposition holds by the actual self Kummer
arrow. -/
theorem localOFieldSelfLogKummerProp_holds (D : S1895PaperInput) :
    localOFieldSelfLogKummerProp D :=
  ⟨selfKummerArrow localOFieldStrip⟩

/-- The paper q-pilot object on the actual local O^× strip.  It uses the S1895
input, boundary data, one-column carrier, line bundle and q-pilot scalar.  The
two strip/Kummer identification slots are the local analogues above, not the
paper's identifications; the exact paper-level bridge is recorded as missing in
section 7. -/
noncomputable def localOFieldPaperO (D : S1895PaperInput) :
    PaperQPilotObject (l := D.l) (V := PaperV)
      (Label := OrigXiFPaperLabel)
      (Choice := OrigXiFPaperChoice (S1895PaperInput.I D))
      (S1895PaperInput.I D)
      (SelfGroup localOFieldStrip)
      localOFieldStrip where
  boundary := localOFieldBoundary D
  strip := localOFieldStrip
  strip_eq_source := rfl
  oneColumn := (S1895PaperO D).oneColumn
  lineBundle := (S1895PaperO D).lineBundle
  logKummer := selfKummerArrow localOFieldStrip
  qPilotLogVolume := (S1895PaperO D).qPilotLogVolume
  qPilotLogVolume_eq := (S1895PaperO D).qPilotLogVolume_eq
  paper_strip_identification := localOFieldFTimesMuProp D
  paper_lineBundle_identification := S1679PaperLineBundleIdentified D.l
  paper_logKummer_identification := localOFieldSelfLogKummerProp D
  paper_qPilot_log_identification :=
    S1895ScalarProp (S1895PaperInput.I D)
      (sourceQPilotSignedLog (S1895PaperInput.I D).initial)

/-- The local paper object's strip is the actual local O^× strip. -/
theorem localOFieldPaperO_strip (D : S1895PaperInput) :
    (localOFieldPaperO D).strip = localOFieldStrip := rfl

/-- The local paper object's strip is the source q-pilot strip of its own
boundary. -/
theorem localOFieldPaperO_strip_eq_source (D : S1895PaperInput) :
    (localOFieldPaperO D).strip =
      sourceQPilotStrip (localOFieldPaperO D).boundary := rfl

/-- Both strip anchors hold for the local paper object. -/
theorem localOFieldPaperO_strip_anchors (D : S1895PaperInput) :
    (localOFieldPaperO D).strip =
        sourceQPilotStrip (localOFieldPaperO D).boundary ∧
      (localOFieldPaperO D).boundary.target_q =
        (localOFieldPaperO D).boundary.theater.thetaPacket.q :=
  ⟨rfl, rfl⟩

/-- The local paper object's F-times-mu slot is the local self-identification
and holds. -/
theorem localOFieldPaperO_paper_strip (D : S1895PaperInput) :
    (localOFieldPaperO D).paper_strip_identification :=
  localOFieldFTimesMuProp_holds D

/-- The local paper object's line-bundle slot is the actual S1679
identification and holds. -/
theorem localOFieldPaperO_paper_lineBundle (D : S1895PaperInput) :
    (localOFieldPaperO D).paper_lineBundle_identification :=
  s1895PaperO_paper_lineBundle D

/-- The local paper object's log-Kummer slot is the local self-identification
and holds. -/
theorem localOFieldPaperO_paper_logKummer (D : S1895PaperInput) :
    (localOFieldPaperO D).paper_logKummer_identification :=
  localOFieldSelfLogKummerProp_holds D

/-- The local paper object's q-pilot scalar slot is the actual S1487/S1527
scalar identification and holds. -/
theorem localOFieldPaperO_paper_qPilot (D : S1895PaperInput) :
    (localOFieldPaperO D).paper_qPilot_log_identification :=
  s1895PaperO_paper_qPilot D

/-- The (1,0) label binding holds for the local paper object. -/
theorem localOFieldPaperO_label (D : S1895PaperInput) :
    (s1895OneColumnLabel PaperV (localOFieldPaperO D).oneColumn).n = 1 ∧
      (s1895OneColumnLabel PaperV (localOFieldPaperO D).oneColumn).m = 0 ∧
      (s1895OneColumnLabel PaperV (localOFieldPaperO D).oneColumn).carrier =
        (localOFieldPaperO D).oneColumn :=
  ⟨rfl, rfl, rfl⟩


/-! ## 7. The exact first missing: a rebased S1895 input -/

/-- The missing paper-level F-times-mu bridge from the local `O^×` strip to
the S1895 paper object's degenerate strip.  This type is *uninhabited*
(section 5); it is recorded to show that the replacement cannot be an
equivalence. -/
def S1978FirstMissingBridge (D : S1895PaperInput) : Type :=
  SourceFTimesMuPrimeStripFullPolyIsomorphism
    (SourceFTimesMuPrimeStrip.canonical localOFieldStrip)
    (SourceFTimesMuPrimeStrip.canonical (S1895PaperO D).strip)

/-- The bridge to the degenerate paper strip is impossible. -/
theorem S1978FirstMissingBridge_impossible (D : S1895PaperInput) :
    ¬ Nonempty (S1978FirstMissingBridge D) := by
  rintro ⟨φ⟩
  obtain ⟨ψ, _⟩ :=
    SourceFTimesMuPrimeStripFullPolyIsomorphism.representative_exists φ
  exact no_localOFieldStrip_equiv_paperO D ⟨ψ.toF⟩

/-- The exact missing object: an `OriginalInput` with the same initial data as
the S1895 input whose `(1,0)` F-prime-strip is the actual local `O^×` strip.
This is the input-level replacement of the degenerate value monoid.  No
inhabitant is asserted or constructed. -/
structure S1978RebasedPaperInput (D : S1895PaperInput) where
  /-- the rebased original input -/
  input : OriginalInput.{0, 0, 0, 0, 0} D.l PaperV
  /-- its initial theta data is the S1895 initial data -/
  same_initial : input.initial = (S1895PaperInput.I D).initial
  /-- its `(1,0)` core is the actual local `O^×` strip -/
  core_eq_local : input.fPrimeStripAt 1 0 = localOFieldStrip

/-- The exact missing paper object: a paper q-pilot object over the rebased
input, with the actual local `O^×` strip as its strip.  No inhabitant is
asserted or constructed. -/
structure S1978RebasedPaperO (D : S1895PaperInput) where
  /-- the rebased input -/
  rebased : S1978RebasedPaperInput D
  /-- the paper object over the rebased input -/
  object : PaperQPilotObject (l := D.l) (V := PaperV)
    (Label := OrigXiFPaperLabel)
    (Choice := OrigXiFPaperChoice rebased.input)
    rebased.input
    (SelfGroup localOFieldStrip)
    localOFieldStrip
  /-- its strip is the actual local `O^×` strip -/
  object_strip : object.strip = localOFieldStrip

/-- The exact first missing type. -/
abbrev S1978FirstMissing (D : S1895PaperInput) :=
  S1978RebasedPaperO D

/-! ## 8. Axiom probes -/

#print axioms LocalOFieldUnitsMu_nontrivial
#print axioms localOFieldUnit_not_isOfFinOrder
#print axioms localOFieldUnit_quotient_ne_one
#print axioms localOFieldStrip_unitsAction_groupUnitsEquiv
#print axioms localOFieldKappaDatum_sourceUnits
#print axioms localOFieldKappaDatum_sourceAction_equiv
#print axioms no_localOFieldUnits_equiv_sourceHaarUnits
#print axioms no_localOFieldStrip_equiv_shear
#print axioms no_localOFieldStrip_equiv_paperO
#print axioms paperO_strip_ne_local
#print axioms paperInput_core_ne_local
#print axioms localOFieldBoundary_strip
#print axioms localOFieldBoundaryStrip_anchors
#print axioms localOFieldFTimesMuProp_holds
#print axioms localOFieldBoundary
#print axioms localOFieldPaperO
#print axioms localOFieldPaperO_strip_anchors
#print axioms localOFieldPaperO_paper_strip
#print axioms localOFieldPaperO_paper_lineBundle
#print axioms localOFieldPaperO_paper_logKummer
#print axioms localOFieldPaperO_paper_qPilot
#print axioms localOFieldPaperO_label
#print axioms S1978FirstMissingBridge_impossible

end LeanFormal.IUT.XiFPaper.S1978LocalFieldOCarrierActual