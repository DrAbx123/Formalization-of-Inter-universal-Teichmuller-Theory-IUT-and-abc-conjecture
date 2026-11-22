import LeanFormal.IUT.IUTII.Frobenioid.Example36TorsorTheory
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Tactic

/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/

/-!
# The n-fold contracted product of a G-torsor (III Example 3.6, tensor half)

This module constructs, for a commutative group G and a G-torsor T, the n-fold
contracted product T^⊗n (n ≥ 1) used by the degree-n torsor arrows of
Inter-universal Teichmüller Theory III, Example 3.6.

The construction is the following.  On the type Fin n → T.carrier of n-tuples of
points of T, put the relation

  x ~ y  ⟺  ∃ m : Fin n → G, (∀ i, y i = m i • x i) and ∏ i, m i = 1.

Because G is commutative, this is an equivalence relation: the product-one
condition is preserved by inversion and multiplication of multipliers.  The
carrier of T^⊗n is the quotient by this relation.  G acts on the quotient
through the first coordinate (in fact through any chosen coordinate i0 : Fin n):

  h • [x] = [update x i0 (h • x i0)].

The action is well defined because the relative coordinate
coordinate (x i) (y i) is unchanged when both entries are translated by the same
element of G.  We prove that this is a MulAction and that the resulting type is a
GTorsor (nonempty, free, transitive); freeness and transitivity reduce to the
product-one condition and to splitting a Finset product at the chosen
coordinate.

The main computation is the coordinate law for the tensor point

  tensorPoint x = [fun _ => x]

of a point x : T.carrier: for every base point t : T.carrier,

  coordinate (tensorPoint t) (tensorPoint x) = (coordinate t x) ^ n.

This is the torsor-theoretic form of the degree-n law "the tensor of n local
generators scales by the n-th power"; in the local log dictionary it becomes the
additive statement n · δ.  We also identify the n = 1 case with T through the
canonical equivariant equivalence, and record the precise first-coordinate action
formula for tensor points.

Scope: this file constructs the contracted product and its coordinate law only.
It does not construct local Hodge theaters, prime-strips, the global torsor
category, or any identification with objects of the source; those remain
separate tasks.
-/

noncomputable section

universe u

namespace LeanFormal.IUT.IUTII.Frobenioid
namespace Example36
namespace GTorsorTensor

open scoped BigOperators

variable {G : Type u} [CommGroup G]

/-! ## The multiplier relation and its quotient -/

/-- The multiplier relation on n-tuples of points of a G-torsor: two tuples are
related when they differ by a tuple of group elements whose product is 1. -/
def tensorRel (T : GTorsor G) (n : ℕ) (x y : Fin n → T.carrier) : Prop :=
  ∃ m : Fin n → G, (∀ i, y i = m i • x i) ∧ ∏ i, m i = 1

/-- The multiplier relation is reflexive. -/
theorem tensorRel_refl (T : GTorsor G) (n : ℕ) (x : Fin n → T.carrier) :
    tensorRel T n x x := by
  refine ⟨fun _ => 1, ?_, by simp⟩
  intro i
  simp

/-- The multiplier relation is symmetric: invert the multipliers. -/
theorem tensorRel_symm (T : GTorsor G) (n : ℕ) {x y : Fin n → T.carrier}
    (h : tensorRel T n x y) : tensorRel T n y x := by
  obtain ⟨m, hm, hprod⟩ := h
  refine ⟨fun i => (m i)⁻¹, ?_, ?_⟩
  · intro i
    have hxi : x i = (m i)⁻¹ • (m i • x i) := by
      simp
    rw [hm i]
    exact hxi
  · rw [Finset.prod_inv_distrib, hprod]
    simp

/-- The multiplier relation is transitive: multiply the multipliers. -/
theorem tensorRel_trans (T : GTorsor G) (n : ℕ) {x y z : Fin n → T.carrier}
    (hxy : tensorRel T n x y) (hyz : tensorRel T n y z) : tensorRel T n x z := by
  obtain ⟨m, hm, hmprod⟩ := hxy
  obtain ⟨m', hm', hm'prod⟩ := hyz
  refine ⟨fun i => m' i * m i, ?_, ?_⟩
  · intro i
    rw [hm' i, hm i, smul_smul]
  · rw [Finset.prod_mul_distrib, hm'prod, hmprod, one_mul]

/-- The multiplier relation as a setoid on n-tuples. -/
def tensorSetoid (T : GTorsor G) (n : ℕ) : Setoid (Fin n → T.carrier) where
  r := tensorRel T n
  iseqv :=
    ⟨tensorRel_refl T n,
      fun h => tensorRel_symm T n h,
      fun h₁ h₂ => tensorRel_trans T n h₁ h₂⟩

/-- The carrier of the n-fold contracted product T^⊗n: the quotient of the
n-tuples of points of T by the multiplier relation. -/
abbrev tensorCarrier (T : GTorsor G) (n : ℕ) : Type u :=
  Quotient (tensorSetoid T n)

/-- The tensor point of x : the class of the constant n-tuple at x. -/
def tensorPoint (T : GTorsor G) (n : ℕ) (x : T.carrier) : tensorCarrier T n :=
  Quotient.mk (tensorSetoid T n) (fun _ => x)

/-- The product of the relative coordinates of two n-tuples.  This is the
complete invariant of the multiplier relation. -/
def tensorCoordinateProduct (T : GTorsor G) (n : ℕ)
    (x y : Fin n → T.carrier) : G :=
  ∏ i, T.coordinate (x i) (y i)

/-- **Complete invariant.**  Two n-tuples are related by multipliers with product
one if and only if the product of their relative coordinates is one. -/
theorem tensorRel_iff_coordinateProduct_eq_one (T : GTorsor G) (n : ℕ)
    (x y : Fin n → T.carrier) :
    tensorRel T n x y ↔ tensorCoordinateProduct T n x y = 1 := by
  constructor
  · rintro ⟨m, hm, hprod⟩
    rw [tensorCoordinateProduct, ← hprod]
    apply Finset.prod_congr rfl
    intro i _
    exact T.coordinate_apply (x i) (hm i).symm
  · intro hprod
    refine ⟨fun i => T.coordinate (x i) (y i), ?_, ?_⟩
    · intro i
      exact (T.coordinate_spec (x i) (y i)).symm
    · exact hprod

/-! ## Elementary product and cancellation lemmas -/

/-- The elementary cancellation identity behind the product-one condition:
in a commutative group, (a * (a * b)⁻¹) * b = 1. -/
theorem mul_mul_inv_mul_eq_one (a b : G) : (a * (a * b)⁻¹) * b = 1 := by
  calc
    (a * (a * b)⁻¹) * b = (a * (b⁻¹ * a⁻¹)) * b := by rw [mul_inv_rev]
    _ = (a * a⁻¹) * (b * b⁻¹) := by ac_rfl
    _ = 1 := by simp

/-- Any two elements of Fin 1 are equal. -/
theorem fin_one_eq (i j : Fin 1) : i = j :=
  Fin.ext (by rw [Fin.val_eq_zero i, Fin.val_eq_zero j])

/-- A product over Fin 1 is the value at any (hence the unique) point. -/
theorem fin_one_prod {M : Type*} [CommMonoid M] (f : Fin 1 → M) (i : Fin 1) :
    ∏ j, f j = f i :=
  Finset.prod_eq_single_of_mem i (Finset.mem_univ i)
    (fun b _ hb => absurd (fin_one_eq b i) hb)

/-! ## The action through one coordinate -/

/-- Translating both entries of a relative coordinate by the same group element
does not change it. -/
theorem coordinate_smul_smul (T : GTorsor G) (g : G) (a b : T.carrier) :
    T.coordinate (g • a) (g • b) = T.coordinate a b := by
  rw [GTorsor.coordinate_smul, GTorsor.coordinate_basePoint_change]
  calc
    g * (T.coordinate a b * g⁻¹) = T.coordinate a b * (g * g⁻¹) := by ac_rfl
    _ = T.coordinate a b := by simp

/-- The product of relative coordinates is unchanged by translating both tuples
coordinatewise by the same group element. -/
theorem tensorCoordinateProduct_update (T : GTorsor G) (n : ℕ) (i0 : Fin n)
    (g : G) (x y : Fin n → T.carrier) :
    tensorCoordinateProduct T n (Function.update x i0 (g • x i0))
        (Function.update y i0 (g • y i0)) =
      tensorCoordinateProduct T n x y := by
  unfold tensorCoordinateProduct
  apply Finset.prod_congr rfl
  intro i _
  rcases eq_or_ne i i0 with rfl | hi
  · rw [Function.update_self, Function.update_self, coordinate_smul_smul]
  · rw [Function.update_of_ne hi, Function.update_of_ne hi]

/-- Splitting the relative-coordinate product at a chosen coordinate, when only
the left tuple is updated there. -/
theorem tensorCoordinateProduct_update_left (T : GTorsor G) (n : ℕ) (i0 : Fin n)
    (r : G) (x y : Fin n → T.carrier) :
    tensorCoordinateProduct T n (Function.update x i0 (r • x i0)) y =
      T.coordinate (r • x i0) (y i0) *
        ∏ i ∈ Finset.univ.erase i0, T.coordinate (x i) (y i) := by
  unfold tensorCoordinateProduct
  rw [← Finset.mul_prod_erase Finset.univ
    (fun i => T.coordinate (Function.update x i0 (r • x i0) i) (y i))
    (Finset.mem_univ i0)]
  have h1 : T.coordinate (Function.update x i0 (r • x i0) i0) (y i0) =
      T.coordinate (r • x i0) (y i0) := by
    rw [Function.update_self]
  have h2 : (∏ i ∈ Finset.univ.erase i0,
        T.coordinate (Function.update x i0 (r • x i0) i) (y i)) =
      ∏ i ∈ Finset.univ.erase i0, T.coordinate (x i) (y i) := by
    apply Finset.prod_congr rfl
    intro i hi
    rw [Function.update_of_ne (Finset.mem_erase.mp hi).1]
  rw [h1, h2]

/-- The action of G on the contracted product through the i0-th coordinate. -/
def tensorSMul (T : GTorsor G) (n : ℕ) (i0 : Fin n) (g : G) :
    tensorCarrier T n → tensorCarrier T n :=
  Quotient.map
    (fun x : Fin n → T.carrier => Function.update x i0 (g • x i0))
    (by
      intro x y hxy
      have hxy' : tensorRel T n x y := hxy
      change tensorRel T n (Function.update x i0 (g • x i0))
        (Function.update y i0 (g • y i0))
      rw [tensorRel_iff_coordinateProduct_eq_one] at hxy' ⊢
      rw [tensorCoordinateProduct_update T n i0 g x y]
      exact hxy')

/-- Computation rule for the action on representatives. -/
@[simp]
theorem tensorSMul_mk (T : GTorsor G) (n : ℕ) (i0 : Fin n) (g : G)
    (x : Fin n → T.carrier) :
    tensorSMul T n i0 g (Quotient.mk (tensorSetoid T n) x) =
      Quotient.mk (tensorSetoid T n) (Function.update x i0 (g • x i0)) := by
  rw [tensorSMul, Quotient.map_mk]

/-- The action of G on the contracted product is a multiplicative action. -/
@[reducible]
def tensorMulAction (T : GTorsor G) (n : ℕ) (i0 : Fin n) :
    MulAction G (tensorCarrier T n) where
  smul := tensorSMul T n i0
  one_smul := by
    intro q
    refine Quotient.inductionOn q ?_
    intro x
    change tensorSMul T n i0 1 (Quotient.mk (tensorSetoid T n) x) =
      Quotient.mk (tensorSetoid T n) x
    rw [tensorSMul_mk, one_smul, Function.update_eq_self]
  mul_smul := by
    intro g h q
    refine Quotient.inductionOn q ?_
    intro x
    change tensorSMul T n i0 (g * h) (Quotient.mk (tensorSetoid T n) x) =
      tensorSMul T n i0 g (tensorSMul T n i0 h (Quotient.mk (tensorSetoid T n) x))
    simp only [tensorSMul_mk]
    rw [Function.update_self, smul_smul, Function.update_idem]

/-! ## The contracted product as a torsor -/

/-- The n-fold contracted product of a G-torsor, with the residual G-action
through the i0-th coordinate.  It is a G-torsor: nonempty, free and transitive. -/
def tensorPowerAt (T : GTorsor G) (n : ℕ) (i0 : Fin n) : GTorsor G where
  carrier := tensorCarrier T n
  inst := tensorMulAction T n i0
  nonempty := ⟨tensorPoint T n (Classical.choice T.nonempty)⟩
  free := by
    intro g q hq
    revert hq
    refine Quotient.inductionOn q ?_
    intro x hx
    change tensorSMul T n i0 g (Quotient.mk (tensorSetoid T n) x) =
      Quotient.mk (tensorSetoid T n) x at hx
    rw [tensorSMul_mk] at hx
    have hrel : tensorRel T n (Function.update x i0 (g • x i0)) x :=
      Quotient.exact hx
    have hprod : tensorCoordinateProduct T n (Function.update x i0 (g • x i0)) x = 1 :=
      (tensorRel_iff_coordinateProduct_eq_one T n _ _).mp hrel
    unfold tensorCoordinateProduct at hprod
    rw [← Finset.mul_prod_erase Finset.univ
      (fun i => T.coordinate (Function.update x i0 (g • x i0) i) (x i))
      (Finset.mem_univ i0)] at hprod
    have h1 : T.coordinate (Function.update x i0 (g • x i0) i0) (x i0) = g⁻¹ := by
      rw [Function.update_self, GTorsor.coordinate_basePoint_change,
        GTorsor.coordinate_self, one_mul]
    have h2 : (∏ i ∈ Finset.univ.erase i0,
        T.coordinate (Function.update x i0 (g • x i0) i) (x i)) = 1 := by
      apply Finset.prod_eq_one
      intro i hi
      rw [Function.update_of_ne (Finset.mem_erase.mp hi).1, GTorsor.coordinate_self]
    rw [h1, h2, mul_one] at hprod
    exact inv_eq_one.mp hprod
  transitive := by
    intro q1 q2
    refine Quotient.inductionOn q1 ?_
    intro x
    refine Quotient.inductionOn q2 ?_
    intro y
    refine ⟨tensorCoordinateProduct T n x y, ?_⟩
    change tensorSMul T n i0 (tensorCoordinateProduct T n x y)
        (Quotient.mk (tensorSetoid T n) x) = Quotient.mk (tensorSetoid T n) y
    rw [tensorSMul_mk]
    apply Quotient.sound
    change tensorRel T n (Function.update x i0 (tensorCoordinateProduct T n x y • x i0)) y
    rw [tensorRel_iff_coordinateProduct_eq_one]
    rw [tensorCoordinateProduct_update_left]
    rw [GTorsor.coordinate_basePoint_change]
    have hmul : T.coordinate (x i0) (y i0) *
        ∏ i ∈ Finset.univ.erase i0, T.coordinate (x i) (y i) =
        tensorCoordinateProduct T n x y :=
      Finset.mul_prod_erase Finset.univ (fun i => T.coordinate (x i) (y i))
        (Finset.mem_univ i0)
    rw [← hmul]
    exact mul_mul_inv_mul_eq_one _ _

/-- The n-fold contracted product T^⊗n for n ≥ 1, with the residual G-action
through the first coordinate.  This is the object underlying the degree-n torsor
arrows of Example 3.6. -/
def tensorPower (T : GTorsor G) (n : ℕ) (hn : 1 ≤ n) : GTorsor G :=
  tensorPowerAt T n ⟨0, Nat.pos_of_ne_zero (Nat.one_le_iff_ne_zero.mp hn)⟩

/-! ## The action on tensor points and the coordinate law -/

/-- The action on a tensor point is the first-coordinate update of the constant
tuple: h • [fun _ => x] = [(h • x, x, …, x)].  This is the precise sense in
which the residual action is a first-coordinate action; for n ≥ 2 it is not in
general the action on the tensor point of h • x. -/
theorem tensorSMul_tensorPoint (T : GTorsor G) (n : ℕ) (i0 : Fin n) (g : G)
    (x : T.carrier) :
    tensorSMul T n i0 g (tensorPoint T n x) =
      Quotient.mk (tensorSetoid T n)
        (Function.update (fun _ : Fin n => x) i0 (g • x)) := by
  simp [tensorPoint]

/-- **Coordinate law for tensor points.**  If t and x are points of T, then the
coordinate of the n-fold tensor of x relative to the n-fold tensor of t is the
n-th power of the coordinate of x relative to t. -/
theorem tensorPowerAt_coordinate_tensorPoint (T : GTorsor G) (n : ℕ) (i0 : Fin n)
    (t x : T.carrier) :
    (tensorPowerAt T n i0).coordinate (tensorPoint T n t) (tensorPoint T n x) =
      (T.coordinate t x) ^ n := by
  letI : MulAction G (tensorCarrier T n) := tensorMulAction T n i0
  have hpoint : ((T.coordinate t x) ^ n) • tensorPoint T n t = tensorPoint T n x := by
    change tensorSMul T n i0 ((T.coordinate t x) ^ n) (tensorPoint T n t) =
      tensorPoint T n x
    rw [tensorSMul_tensorPoint, tensorPoint]
    apply Quotient.sound
    change tensorRel T n
      (Function.update (fun _ : Fin n => t) i0 ((T.coordinate t x) ^ n • t))
      (fun _ : Fin n => x)
    rw [tensorRel_iff_coordinateProduct_eq_one]
    rw [tensorCoordinateProduct_update_left]
    have hcoord : T.coordinate ((T.coordinate t x) ^ n • t) x =
        T.coordinate t x * ((T.coordinate t x) ^ n)⁻¹ :=
      GTorsor.coordinate_basePoint_change T t ((T.coordinate t x) ^ n) x
    have hR : (∏ i ∈ Finset.univ.erase i0, T.coordinate t x) =
        (T.coordinate t x) ^ (n - 1) := by
      rw [Finset.prod_const, Finset.card_erase_of_mem (Finset.mem_univ i0),
        Finset.card_univ, Fintype.card_fin]
    have hnpos : 0 < n := lt_of_le_of_lt (Nat.zero_le (i0 : ℕ)) i0.isLt
    have hn1 : 1 ≤ n := Nat.succ_le_iff.mpr hnpos
    have hpow : (T.coordinate t x) ^ n =
        T.coordinate t x * (T.coordinate t x) ^ (n - 1) := by
      conv_lhs => rw [← Nat.sub_add_cancel hn1]
      rw [pow_succ']
    rw [hcoord, hR, hpow]
    exact mul_mul_inv_mul_eq_one _ _
  exact GTorsor.coordinate_apply (tensorPowerAt T n i0) (tensorPoint T n t) hpoint

/-- The coordinate law for the n-fold contracted product with the action through
the first coordinate. -/
theorem tensorPower_coordinate_tensorPoint (T : GTorsor G) (n : ℕ) (hn : 1 ≤ n)
    (t x : T.carrier) :
    (tensorPower T n hn).coordinate (tensorPoint T n t) (tensorPoint T n x) =
      (T.coordinate t x) ^ n :=
  tensorPowerAt_coordinate_tensorPoint T n
    ⟨0, Nat.pos_of_ne_zero (Nat.one_le_iff_ne_zero.mp hn)⟩ t x

/-! ## The case n = 1 -/

/-- For n = 1 the first-coordinate map to T is well defined on the quotient:
the product-one condition over Fin 1 forces the single multiplier to be one. -/
def tensorPowerOneToT (T : GTorsor G) (i0 : Fin 1) :
    tensorCarrier T 1 → T.carrier :=
  Quotient.lift (fun x : Fin 1 → T.carrier => x i0) (by
    intro x y hxy
    change tensorRel T 1 x y at hxy
    rw [tensorRel_iff_coordinateProduct_eq_one] at hxy
    have hc : T.coordinate (x i0) (y i0) = 1 := by
      rw [← fin_one_prod (fun i => T.coordinate (x i) (y i)) i0]
      exact hxy
    have hspec := T.coordinate_spec (x i0) (y i0)
    rw [hc, one_smul] at hspec
    exact hspec)

/-- The canonical equivalence between the contracted product T^⊗1 and T: the
class of an n-tuple is sent to its i0-th coordinate, with the tensor point as
inverse. -/
def tensorPowerOneEquiv (T : GTorsor G) (i0 : Fin 1) :
    tensorCarrier T 1 ≃ T.carrier where
  toFun := tensorPowerOneToT T i0
  invFun := tensorPoint T 1
  left_inv := by
    intro q
    refine Quotient.inductionOn q ?_
    intro x
    apply Quotient.sound
    change tensorRel T 1 (fun _ : Fin 1 => x i0) x
    rw [tensorRel_iff_coordinateProduct_eq_one]
    rw [tensorCoordinateProduct]
    rw [fin_one_prod (fun i => T.coordinate (x i0) (x i)) i0]
    exact T.coordinate_self (x i0)
  right_inv := by
    intro x
    rfl

/-- The n = 1 equivalence sends the tensor point of x to x. -/
@[simp]
theorem tensorPowerOneEquiv_tensorPoint (T : GTorsor G) (i0 : Fin 1)
    (x : T.carrier) :
    tensorPowerOneEquiv T i0 (tensorPoint T 1 x) = x :=
  rfl

/-- For n = 1 the contracted-product action is the given action on T: the
n = 1 equivalence is G-equivariant. -/
theorem tensorPowerOneEquiv_smul (T : GTorsor G) (i0 : Fin 1) (g : G)
    (q : tensorCarrier T 1) :
    tensorPowerOneEquiv T i0 (tensorSMul T 1 i0 g q) =
      g • tensorPowerOneEquiv T i0 q := by
  refine Quotient.inductionOn q ?_
  intro x
  change tensorPowerOneToT T i0
      (tensorSMul T 1 i0 g (Quotient.mk (tensorSetoid T 1) x)) = g • (x i0)
  rw [tensorSMul_mk]
  change (Function.update x i0 (g • x i0)) i0 = g • (x i0)
  rw [Function.update_self]

/-- The n = 1 action on tensor points is the given action on T. -/
theorem tensorSMul_tensorPoint_one (T : GTorsor G) (i0 : Fin 1) (g : G)
    (x : T.carrier) :
    tensorSMul T 1 i0 g (tensorPoint T 1 x) = tensorPoint T 1 (g • x) := by
  rw [tensorSMul_tensorPoint]
  apply Quotient.sound
  change tensorRel T 1 (Function.update (fun _ : Fin 1 => x) i0 (g • x))
    (fun _ : Fin 1 => g • x)
  rw [tensorRel_iff_coordinateProduct_eq_one]
  rw [tensorCoordinateProduct]
  change (∏ i, T.coordinate
    (Function.update (fun _ : Fin 1 => x) i0 (g • x) i) (g • x)) = 1
  rw [fin_one_prod
    (fun i => T.coordinate (Function.update (fun _ : Fin 1 => x) i0 (g • x) i)
      (g • x)) i0]
  rw [Function.update_self]
  exact T.coordinate_self (g • x)

/-- The n = 1 coordinate law: the coordinate on T^⊗1 is the coordinate on T. -/
theorem tensorPowerOne_coordinate_tensorPoint (T : GTorsor G) (i0 : Fin 1)
    (t x : T.carrier) :
    (tensorPowerAt T 1 i0).coordinate (tensorPoint T 1 t) (tensorPoint T 1 x) =
      T.coordinate t x := by
  rw [tensorPowerAt_coordinate_tensorPoint, pow_one]

end GTorsorTensor
end Example36
end LeanFormal.IUT.IUTII.Frobenioid
end
