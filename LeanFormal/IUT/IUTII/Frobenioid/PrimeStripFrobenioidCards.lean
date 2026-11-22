import LeanFormal.IUT.IUTII.Frobenioid.PrimeStripsFrobenioidLinks
import LeanFormal.IUT.IUTII.Frobenioid.LocalUnitKummerInjectivity
import LeanFormal.IUT.Foundations.NumberField.PlaceCompletionCarrier
import Iut.Foundations.Frobenioid
import Mathlib.RingTheory.Valuation.Integral
/-!
# Card reductions for the prime strips -> Frobenioid link layer

This module is the card-reduction companion of
`IUTII/Frobenioid/PrimeStripsFrobenioidLinks.lean` (the frozen link-layer
carrier, SHA 7899B185...F099891) for the obligation
`IUT-I-II.prime-strips-frobenioids` (`IUTII/Frobenioid/PrimeStrips.lean:5`).
It addresses the four cards left open by the link-layer pass:

* Card CAT (the categorical Frobenioids Cv / C⊢v / C⊩mod of IUT I, Examples
  3.3-3.5): reduced to a proved negative form.  On the group-valued
  prime-strip carriers no divisorial (sharp) additive monoid can be
  additively equivalent to them
  (`frobenioidLinkUnitStrip_no_divisorialAddMonoid`,
  `frobenioidLinkIntegralStrip_not_sharp`).  This is a REDUCED negative
  statement; it does not construct Cv, C⊢v, or C⊩mod.
* Card MOD (IUT III, Example 3.6, (iii); Proposition 3.7): necessary
  conditions (`MODDirectionCard.degree_mem_range`,
  `MODDirectionCard.realification_mem_range`), the degree-gap obstruction
  `not_MODDirectionCard_of_degree_gap` with the degree computation
  `inversePrimeUnit_degree` (degree = log p), and the finite-model negative
  `finitePlaceModel_not_MODDirectionCard`.  The arithmetic surjectivity of
  the norm degrees (norm image p^Q inside R) stays a recorded gap.
* Boundary item (1): the geometric kernels are trivial on the current
  carriers (`frobenioidLinkUnitStrip_geometric_eq_bot`); the etale-pi1
  content is not available (gap card).
* Boundary item (2): the unit kernel of a number-field place is constructed
  (`numberFieldFinitePlaceUnitKernel`); the V_K prime-strip/Galois transport
  interface stays a gap card.
* Boundary item (4): the arithmetic-Frobenius (log-shell compatibility) data
  is recorded as a text gap card.

## Source locations (original text under `papers/motizuki_corpus/text`)

* IUT I, Definition 5.2, (i)-(iv) (`Inter-universal Teichmuller Theory I.txt`
  lines 7702-7775): the prime-strip collections.
* IUT I, Example 3.2, (iii); Example 3.3, (i),(iii)-(iv) (txt line 4132ff):
  the local Frobenioids Cv and C⊢v.
* IUT I, Example 3.5, (i) (txt line 4569ff): the global realified Frobenioid
  C⊩mod and the restriction functors.
* IUT III, Example 3.6, (i)-(iii) (txt line 6181ff); Proposition 3.7:
  the MOD/mod Frobenioids and their natural isomorphism.
* [FrdI] section 0 (`The Geometry of Frobenioids I.txt` lines 464-465) and
  Definition 1.1, (i) (lines 810-815): the sharp/divisorial conditions.

## Consumers

* K2FrobenioidBoundary, k2FromFrobenioidCards
  (`IUTIII/Theorem311/SourceK1K2Construction.lean:350-385, 523`), the
  Theorem 3.11 source chain, and SourceHodgeTheaterBridge.
-/

open LeanFormal.IUT
open scoped NNReal nonZeroDivisors BigOperators

noncomputable section

namespace LeanFormal.IUT

/-! ## 1. The valued/norm bridge at p-adic places -/
theorem padicAlgCl_valuation_le_one_iff_norm_le_one (p : Nat) [Fact (Nat.Prime p)]
    (x : AlgebraicClosure ℚ_[p]) :
    (Valued.v x ≤ 1) ↔ (‖x‖ ≤ 1) := by
  rw [PadicAlgCl.valuation_def]
  exact NNReal.coe_le_one.symm

/-! ## 2. Card CAT: the sharpness obstruction (reduced negative form) -/

theorem not_sharp_of_addGroup {G : Type} [AddGroup G] {g : G} (hg : g ≠ 0) :
    ¬ (∀ a : G, IsAddUnit a → a = 0) :=
  fun h => hg (h g ⟨⟨g, -g, add_neg_cancel g, neg_add_cancel g⟩, rfl⟩)

theorem not_sharp_of_nontrivial_unit {M : Type} [Monoid M] (u : Mˣ) (hu : u ≠ 1) :
    ¬ (∀ a : Additive M, IsAddUnit a → a = 0) := by
  intro h
  have huM : (u : M) ≠ 1 := fun h1 => hu (Units.ext h1)
  have hval : Additive.ofMul (u : M) + Additive.ofMul ((u⁻¹ : Mˣ) : M) = 0 := by
    have h1 : (u : M) * ((u⁻¹ : Mˣ) : M) = 1 := by
      rw [← Units.val_mul]
      simp [mul_inv_cancel]
    rw [← ofMul_mul, h1, ofMul_one]
  have hval' : Additive.ofMul ((u⁻¹ : Mˣ) : M) + Additive.ofMul (u : M) = 0 := by
    have h1 : ((u⁻¹ : Mˣ) : M) * (u : M) = 1 := by
      rw [← Units.val_mul]
      simp [inv_mul_cancel]
    rw [← ofMul_mul, h1, ofMul_one]
  have hw : IsAddUnit (Additive.ofMul (u : M)) :=
    ⟨⟨Additive.ofMul (u : M), Additive.ofMul ((u⁻¹ : Mˣ) : M), hval, hval'⟩, rfl⟩
  exact huM (ofMul_eq_zero.mp (h (Additive.ofMul (u : M)) hw))

theorem no_divisorialAddMonoid_of_addEquiv {G : Type} [AddGroup G] {g : G}
    (hg : g ≠ 0) :
    ¬ ∃ M : Iut.DivisorialAddMonoid, Nonempty (M.carrier ≃+ G) := by
  rintro ⟨M, ⟨e⟩⟩
  have hcomm : ∀ a b : G, a + b = b + a := by
    intro a b
    have hab : a + b = e (e.symm a + e.symm b) := by
      simp only [map_add, e.apply_symm_apply]
    have hba : b + a = e (e.symm b + e.symm a) := by
      simp only [map_add, e.apply_symm_apply]
    rw [hab, hba, add_comm (e.symm a) (e.symm b)]
  have eq_e_zero : ∀ g' : G, g' = e 0 := by
    intro g'
    have h1 : e.symm g' + e.symm (e (0 : M.carrier) - g') = 0 := by
      apply e.injective
      simp only [map_add, e.apply_symm_apply]
      rw [sub_eq_add_neg, ← add_assoc, hcomm g' (e (0 : M.carrier)), add_assoc, add_neg_cancel, add_zero]
    have h2 : e.symm (e (0 : M.carrier) - g') + e.symm g' = 0 := by
      apply e.injective
      simp only [map_add, e.apply_symm_apply]
      rw [sub_eq_add_neg, add_assoc, neg_add_cancel, add_zero]
    have hu : IsAddUnit (e.symm g') :=
      ⟨⟨e.symm g', e.symm (e (0 : M.carrier) - g'), h1, h2⟩, rfl⟩
    have hsharp : e.symm g' = 0 := M.sharp (e.symm g') hu
    calc g' = e (e.symm g') := (e.apply_symm_apply g').symm
      _ = e 0 := by rw [hsharp]
  exact hg (by rw [eq_e_zero g, ← eq_e_zero 0])

-- concrete witness: the prime p as a unit of the algebraic closure
theorem padicAlgClPrimeUnit_ne_zero (p : Nat) [Fact (Nat.Prime p)] :
    ((p : ℚ_[p]) : AlgebraicClosure ℚ_[p]) ≠ 0 := by
  rw [← norm_ne_zero_iff, PadicAlgCl.norm_extends, Padic.norm_p]
  exact inv_ne_zero (by exact_mod_cast (Fact.out : Nat.Prime p).ne_zero)

noncomputable def padicAlgClPrimeUnit (p : Nat) [Fact (Nat.Prime p)] :
    (AlgebraicClosure ℚ_[p])ˣ :=
  Units.mk0 ((p : ℚ_[p]) : AlgebraicClosure ℚ_[p]) (padicAlgClPrimeUnit_ne_zero p)

theorem padicAlgClPrimeUnit_ne_one (p : Nat) [Fact (Nat.Prime p)] :
    padicAlgClPrimeUnit p ≠ 1 := by
  intro h
  rw [padicAlgClPrimeUnit] at h
  have h1 : ((p : ℚ_[p]) : AlgebraicClosure ℚ_[p]) = 1 := by
    simpa using congrArg (fun w : (AlgebraicClosure ℚ_[p])ˣ =>
      (w : AlgebraicClosure ℚ_[p])) h
  have h2 := congrArg (fun x : AlgebraicClosure ℚ_[p] => ‖x‖) h1
  rw [PadicAlgCl.norm_extends, Padic.norm_p, norm_one] at h2
  have h3 : (p : ℝ) = 1 := inv_eq_one.mp h2
  exact (Fact.out : Nat.Prime p).ne_one (by exact_mod_cast h3)

theorem frobenioidLinkUnitStrip_not_sharp (v : RationalPrimePlace) :
    ¬ (∀ a : Additive (frobenioidLinkUnitStrip.Mon v), IsAddUnit a → a = 0) := by
  letI : Fact (Nat.Prime v.1) := Fact.mk v.2
  change ¬ (∀ a : Additive ((AlgebraicClosure ℚ_[v.1])ˣ), IsAddUnit a → a = 0)
  refine not_sharp_of_addGroup (g := Additive.ofMul (padicAlgClPrimeUnit v.1)) ?_
  intro hcon
  exact padicAlgClPrimeUnit_ne_one v.1 (ofMul_eq_zero.mp hcon)

theorem frobenioidLinkUnitStrip_no_divisorialAddMonoid (v : RationalPrimePlace) :
    ¬ ∃ M : Iut.DivisorialAddMonoid,
        Nonempty (M.carrier ≃+ Additive (frobenioidLinkUnitStrip.Mon v)) := by
  letI : Fact (Nat.Prime v.1) := Fact.mk v.2
  change ¬ ∃ M : Iut.DivisorialAddMonoid,
        Nonempty (M.carrier ≃+ Additive ((AlgebraicClosure ℚ_[v.1])ˣ))
  refine no_divisorialAddMonoid_of_addEquiv
    (g := Additive.ofMul (padicAlgClPrimeUnit v.1)) ?_
  intro hcon
  exact padicAlgClPrimeUnit_ne_one v.1 (ofMul_eq_zero.mp hcon)

-- the integral carrier: (-1) is a nontrivial unit
theorem frobenioidLinkIntegralStrip_not_sharp (v : RationalPrimePlace) :
    ¬ (∀ a : Additive (frobenioidLinkIntegralStrip.Mon v), IsAddUnit a → a = 0) := by
  letI : Fact (Nat.Prime v.1) := Fact.mk v.2
  change ¬ (∀ a : Additive (LocalIntegralMonoid v.1), IsAddUnit a → a = 0)
  let z : LocalIntegralMonoid v.1 :=
    ⟨(-1 : LocalAlgebraicIntegerRing v.1),
      mem_nonZeroDivisors_of_ne_zero (by
        intro hzero
        have h1 : (-1 : AlgebraicClosure ℚ_[v.1]) = 0 :=
          congrArg (fun w : LocalAlgebraicIntegerRing v.1 =>
            (w : AlgebraicClosure ℚ_[v.1])) hzero
        exact neg_ne_zero.mpr one_ne_zero h1)⟩
  have hzz : z * z = 1 := by
    apply Subtype.ext
    apply Subtype.ext
    change ((-1 : AlgebraicClosure ℚ_[v.1]) * (-1 : AlgebraicClosure ℚ_[v.1])) = 1
    ring
  have hz1 : z ≠ 1 := by
    intro heq
    have h1 : (-1 : LocalAlgebraicIntegerRing v.1) = 1 :=
      congrArg (fun w : LocalIntegralMonoid v.1 =>
        (w : LocalAlgebraicIntegerRing v.1)) heq
    have h2 : (-1 : AlgebraicClosure ℚ_[v.1]) = 1 :=
      congrArg (fun w : LocalAlgebraicIntegerRing v.1 =>
        (w : AlgebraicClosure ℚ_[v.1])) h1
    exact Ring.neg_one_ne_one_of_char_ne_two (by rw [ringChar.eq_zero]; norm_num) h2
  exact not_sharp_of_nontrivial_unit ⟨z, z, hzz, hzz⟩ (by
    intro hu
    exact hz1 (by simpa using congrArg (fun w : (LocalIntegralMonoid v.1)ˣ =>
      (w : LocalIntegralMonoid v.1)) hu))

/-! ## 3. Integral elements of the local ring have norm at most 1 -/
theorem localAlgebraicInteger_norm_le_one (p : Nat) [Fact (Nat.Prime p)]
    (x : LocalAlgebraicIntegerRing p) :
    ‖(x : AlgebraicClosure ℚ_[p])‖ ≤ 1 := by
  let R := Valuation.integer (ValuativeRel.valuation ℚ_[p])
  let T : Subring (AlgebraicClosure ℚ_[p]) :=
    (Valued.v : Valuation (AlgebraicClosure ℚ_[p]) NNReal).integer
  have hxint : IsIntegral R (x : AlgebraicClosure ℚ_[p]) := x.2
  have hbase : ∀ r : R,
      (algebraMap ℚ_[p] (AlgebraicClosure ℚ_[p])) (r : ℚ_[p]) ∈ T := by
    intro r
    have hmul : Padic.mulValuation (p := p) (r : ℚ_[p]) ≤ 1 :=
      (Valuation.vle_one_iff (Padic.mulValuation (p := p))).mp
        ((Valuation.vle_one_iff (ValuativeRel.valuation ℚ_[p])).mpr r.2)
    have hnorm : ‖(r : ℚ_[p])‖ ≤ 1 :=
      (LocalIntegralUnitKummerInjectivity.padicMulValuation_le_one_iff_norm_le_one p _).mp hmul
    have hnormA : ‖(((r : ℚ_[p]) : AlgebraicClosure ℚ_[p]))‖ ≤ 1 := by
      rw [PadicAlgCl.norm_extends]
      exact hnorm
    change Valued.v (((r : ℚ_[p]) : AlgebraicClosure ℚ_[p])) ≤ 1
    rw [PadicAlgCl.valuation_def]
    exact NNReal.coe_le_one.mp hnormA
  let phi : R →+* T :=
    RingHom.codRestrict ((algebraMap ℚ_[p] (AlgebraicClosure ℚ_[p])).comp
      (Subring.subtype R)) T hbase
  letI : Algebra R T := RingHom.toAlgebra phi
  haveI : IsScalarTower R T (AlgebraicClosure ℚ_[p]) :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  have hxT : IsIntegral T (x : AlgebraicClosure ℚ_[p]) := hxint.tower_top
  have hv : Valued.v (x : AlgebraicClosure ℚ_[p]) ≤ 1 :=
    ((Valuation.integer.integers
      (Valued.v : Valuation (AlgebraicClosure ℚ_[p]) NNReal)).isIntegral_iff_v_le_one).mp hxT
  rw [PadicAlgCl.valuation_def] at hv
  exact NNReal.coe_le_one.mpr hv

/-! ## 4. The inverse prime unit and its degree log p -/
noncomputable def inversePrimeUnit (v : RationalPrimePlace) :
    frobenioidLinkUnitStrip.Mon v := by
  letI : Fact (Nat.Prime v.1) := Fact.mk v.2
  change (AlgebraicClosure ℚ_[v.1])ˣ
  exact (padicAlgClPrimeUnit v.1)⁻¹

theorem inversePrimeUnit_degree (v : RationalPrimePlace) :
    (frobenioidLinkUnitStrip.degree v (inversePrimeUnit v)).toAdd
      = Real.log (v.1 : ℝ) := by
  letI : Fact (Nat.Prime v.1) := Fact.mk v.2
  rw [inversePrimeUnit]
  change Real.log ‖(((padicAlgClPrimeUnit v.1)⁻¹ : (AlgebraicClosure ℚ_[v.1])ˣ) :
    AlgebraicClosure ℚ_[v.1])‖ = Real.log (v.1 : ℝ)
  congr 1
  rw [padicAlgClPrimeUnit, Units.val_inv_eq_inv_val, Units.val_mk0,
    norm_inv, PadicAlgCl.norm_extends, Padic.norm_p, inv_inv]

/-! ## 5. Card MOD: degree-gap obstruction and the finite-model negative -/
theorem not_MODDirectionCard_of_degree_gap
    {X Y : Type} [CommMonoid X] [CommMonoid Y]
    (localKernel : FrobenioidValueKernel X) (globalKernel : FrobenioidValueKernel Y)
    (hLocal : ∀ x, (localKernel.degree x).toAdd ≤ 0)
    (hGlobal : ∃ y, 0 < (globalKernel.degree y).toAdd) :
    ¬ MODDirectionCard localKernel globalKernel := by
  rintro ⟨MODMap, hdegree, _⟩
  obtain ⟨y, hy⟩ := hGlobal
  have h := congrArg Multiplicative.toAdd (hdegree y)
  rw [← h] at hy
  exact not_le_of_gt hy (hLocal (MODMap y))

noncomputable def inversePrimeUnitFamily (s : Finset RationalPrimePlace)
    (v0 : {v : RationalPrimePlace // v ∈ s}) : FinitePlaceValueFamily s :=
  Pi.mulSingle v0 (inversePrimeUnit v0.1)

theorem inversePrimeUnitFamily_totalDegreeFun (s : Finset RationalPrimePlace)
    (v0 : {v : RationalPrimePlace // v ∈ s}) :
    (finitePlaceTotalDegreeFun s (inversePrimeUnitFamily s v0)).toAdd
      = Real.log (v0.1.1 : ℝ) := by
  rw [finitePlaceTotalDegreeFun, realToAdd_ofAdd]
  rw [Finset.sum_eq_single v0]
  · rw [inversePrimeUnitFamily, Pi.mulSingle_eq_same]
    exact inversePrimeUnit_degree v0.1
  · intro b _ hb
    rw [inversePrimeUnitFamily, Pi.mulSingle_eq_of_ne hb]
    simp
  · intro h
    exact absurd (Finset.mem_univ v0) h

theorem inversePrimeUnitFamily_totalDegree (s : Finset RationalPrimePlace)
    (v0 : {v : RationalPrimePlace // v ∈ s}) :
    (finitePlaceTotalDegree s (inversePrimeUnitFamily s v0)).toAdd
      = Real.log (v0.1.1 : ℝ) := by
  rw [show (finitePlaceTotalDegree s (inversePrimeUnitFamily s v0)).toAdd
      = (finitePlaceTotalDegreeFun s (inversePrimeUnitFamily s v0)).toAdd
      from rfl]
  exact inversePrimeUnitFamily_totalDegreeFun s v0

theorem finitePlaceModel_not_MODDirectionCard (s : Finset RationalPrimePlace)
    (v0 : {v : RationalPrimePlace // v ∈ s}) :
    ¬ MODDirectionCard (localIntegralPlaceFrobenioidValueKernel v0.1)
      (finitePlaceFrobenioidValueKernel s) := by
  refine not_MODDirectionCard_of_degree_gap _ _ ?_ ?_
  · intro x
    haveI : Fact (Nat.Prime v0.1.1) := Fact.mk v0.1.2
    have hnorm : ‖(LocalIntegralMonoid.toAlgebraicClosureUnits v0.1.1 x :
        AlgebraicClosure ℚ_[v0.1.1])‖ ≤ 1 := by
      simpa [LocalIntegralMonoid.toAlgebraicClosureUnits] using
        localAlgebraicInteger_norm_le_one v0.1.1 (x.1)
    have hlog : Real.log ‖(LocalIntegralMonoid.toAlgebraicClosureUnits v0.1.1 x :
        AlgebraicClosure ℚ_[v0.1.1])‖ ≤ 0 :=
      Real.log_nonpos (le_of_lt (norm_pos_unit (AlgebraicClosure ℚ_[v0.1.1]) _)) hnorm
    change Real.log ‖(LocalIntegralMonoid.toAlgebraicClosureUnits v0.1.1 x :
      AlgebraicClosure ℚ_[v0.1.1])‖ ≤ 0
    exact hlog
  · refine ⟨inversePrimeUnitFamily s v0, ?_⟩
    change 0 < (finitePlaceTotalDegree s (inversePrimeUnitFamily s v0)).toAdd
    rw [inversePrimeUnitFamily_totalDegree]
    exact Real.log_pos (by
      haveI : Fact (Nat.Prime v0.1.1) := Fact.mk v0.1.2
      exact_mod_cast (Fact.out : Nat.Prime v0.1.1).one_lt)

/-! ## 6. Boundary item (1): trivial geometric kernel (reduced form) -/
theorem frobenioidLinkUnitStrip_geometric_eq_bot (v : RationalPrimePlace) :
    frobenioidLinkUnitStrip.toDPrimeStrip.geometric v = ⊥ := by
  change (MonoidHom.id _).ker = ⊥
  exact MonoidHom.ker_id

theorem frobenioidLinkIntegralStrip_geometric_eq_bot (v : RationalPrimePlace) :
    frobenioidLinkIntegralStrip.toDPrimeStrip.geometric v = ⊥ := by
  change (MonoidHom.id _).ker = ⊥
  exact MonoidHom.ker_id

/-! ## 7. Boundary item (2): the number-field place unit kernel -/
def numberFieldFinitePlaceUnitKernel {K : Type} [Field K] [NumberField K]
    (place : NumberField.FinitePlace K) :
    FrobenioidValueKernel (NumberFieldFinitePlace.Completion place)ˣ :=
  {
    degree := unitNormLogDegree (NumberFieldFinitePlace.Completion place)
    realification := fun u => (unitNormLogDegree (NumberFieldFinitePlace.Completion place) u).toAdd
    realification_mul := by
      intro x y
      rw [map_mul, realToAdd_mul]
    degree_realification := by intro x; rfl
    unit := 1
    unit_realification := by simp
    effective := fun _ => True
    effective_proved := fun _ => trivial
    transport := id
    transport_degree := by intro x; rfl }

theorem numberFieldFinitePlaceUnitKernel_realification {K : Type} [NormedField K] (u : Kˣ) :
    (unitNormLogDegree K u).toAdd = Real.log ‖(u : K)‖ := rfl

/-! ## 8. Iterated transport compatibility of the link layer -/
theorem primeStripFrobenioidLinkLayer_modMap_iterate {X Y : Type} [CommMonoid X] [CommMonoid Y]
    (L : PrimeStripFrobenioidLinkLayer X Y) (x : X) (n : Nat) :
    L.modMap (Nat.iterate L.localFrobenioid.transport n x) =
      Nat.iterate L.globalFrobenioid.transport n (L.modMap x) := by
  induction n generalizing x with
  | zero => rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply', L.mod_transport, ih x]

theorem primeStripFrobenioidLinkLayer_MODMap_iterate {X Y : Type} [CommMonoid X] [CommMonoid Y]
    (L : PrimeStripFrobenioidLinkLayer X Y) (y : Y) (n : Nat) :
    L.MODMap (Nat.iterate L.globalFrobenioid.transport n y) =
      Nat.iterate L.localFrobenioid.transport n (L.MODMap y) := by
  induction n generalizing y with
  | zero => rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply', L.MOD_transport, ih y]

/-! ## 9. Necessary conditions for any MOD card -/
theorem MODDirectionCard.degree_mem_range {X Y : Type} [CommMonoid X] [CommMonoid Y]
    {localKernel : FrobenioidValueKernel X} {globalKernel : FrobenioidValueKernel Y}
    (h : MODDirectionCard localKernel globalKernel) (y : Y) :
    globalKernel.degree y ∈ Set.range localKernel.degree := by
  obtain ⟨MODMap, hdegree, _⟩ := h
  exact ⟨MODMap y, hdegree y⟩

theorem MODDirectionCard.realification_mem_range {X Y : Type} [CommMonoid X]
    [CommMonoid Y] {localKernel : FrobenioidValueKernel X}
    {globalKernel : FrobenioidValueKernel Y}
    (h : MODDirectionCard localKernel globalKernel) (y : Y) :
    globalKernel.realification y ∈ Set.range localKernel.realification := by
  obtain ⟨MODMap, hdegree, _⟩ := h
  refine ⟨MODMap y, ?_⟩
  rw [← localKernel.degree_realification, hdegree y]
  exact globalKernel.degree_realification y

end LeanFormal.IUT

end

namespace LeanFormal.IUT.Audit

/-- Card-reduction pass for `IUT-I-II.prime-strips-frobenioids`: the four
named cards (CAT, MOD, boundary (1), (2), (4)) reduced to proved statements
or recorded as precise gap cards, on top of the frozen link-layer carrier. -/
def primeStripFrobenioidCardReductions : Obligation :=
  { id := "IUT-II.prime-strips-frobenioid-card-reductions"
    source :=
      "IUT I, Definition 5.2, (i)-(iv); Example 3.2, (iii); Example 3.3, " ++
        "(i),(iii)-(iv); Example 3.5, (i); IUT III, Example 3.6, (i)-(iii); " ++
        "Proposition 3.7; [FrdI], section 0 and Definition 1.1, (i)"
    status := VerificationStatus.interface
    note :=
      "Card reductions on top of `IUT-II.prime-strips-frobenioid-link-layer`. " ++
        "Card CAT: proved negative (REDUCED) form -- no divisorial (sharp) " ++
        "additive monoid is additively equivalent to a nontrivial additive " ++
        "comm group, and the prime-strip value carriers are sharpness-" ++
        "nontrivial (`frobenioidLinkUnitStrip_no_divisorialAddMonoid`, " ++
        "`frobenioidLinkIntegralStrip_not_sharp`); the categorical " ++
        "Frobenioids Cv/C⊢v/C⊩mod remain unconstructed. Card MOD: proved " ++
        "necessary conditions (`MODDirectionCard.degree_mem_range`, " ++
        "`realification_mem_range`), the degree-gap obstruction " ++
        "`not_MODDirectionCard_of_degree_gap`, degree computations " ++
        "(`inversePrimeUnit_degree` = log p), and the finite-model negative " ++
        "`finitePlaceModel_not_MODDirectionCard`; the arithmetic " ++
        "surjectivity of the norm degrees remains a gap. Boundary (1): " ++
        "geometric kernel trivial (`frobenioidLinkUnitStrip_geometric_eq_bot`, " ++
        "`frobenioidLinkIntegralStrip_geometric_eq_bot`); etale-pi1 content " ++
        "open. Boundary (2): `numberFieldFinitePlaceUnitKernel` constructed; " ++
        "V_K prime-strip/Galois transport open. Boundary (4): arithmetic " ++
        "Frobenius data recorded as text card only. Consumers: " ++
        "K2FrobenioidBoundary, Theorem 3.11 source chain, " ++
        "SourceHodgeTheaterBridge."
    dependsOn :=
      [ "IUT-II.prime-strips-frobenioid-link-layer",
        "IUT-II.prime-strip-construction-kernel",
        "IUT-I-II.prime-strip-degree-kernel" ] }

end LeanFormal.IUT.Audit
