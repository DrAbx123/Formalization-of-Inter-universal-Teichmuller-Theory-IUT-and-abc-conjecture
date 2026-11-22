import LeanFormal.IUT.IUTII.Frobenioid.Example36TorsorTheory
import LeanFormal.IUT.IUTII.Frobenioid.Example36LocalValueData
import LeanFormal.IUT.IUTII.Frobenioid.Example36GlobalPlaceData

/-!
# The local contracted product `Gamma_v x^G T` of IUT III, Example 3.6

This module constructs the local contraction of the torsor half of
IUT III, Example 3.6.  The input is

* a field `F` with unit group `F^x`,
* the local value data `D : LocalValueData F Gamma` of the place: an additive
  value group `Gamma`, the integral cone, and the local principal map
  `D.deltaAdd : F^x -> Gamma`,
* a nonempty `F^x`-torsor `T : GTorsor F^x` (the local unit torsor).

The local contraction is the contracted product
`T_v = Gamma_v x^G T`: the quotient of `Gamma x T.carrier` by the relation
`(gamma + delta(g), t) ~ (gamma, g • t)`.  It is the local model of the
`Gamma_v`-torsor on which the local value coordinates of Example 3.6 live.

Contents (bottom-up):

1. the relation and its equivalence-relation proof (`localContractionSetoid`),
   using only `deltaAdd_mul`, `deltaAdd_inv` and the torsor action laws; the
   quotient type `LocalContraction` and the defining relation lemma
   `localContractionMk_delta_smul`;
2. the action of the value group `Multiplicative Gamma` on the quotient by
   translation of the first coordinate, with its `MulAction` laws, and the
   freeness/transitivity proof; in the same-universe case the quotient is
   packaged as a `GTorsor (Multiplicative Gamma)`
   (`localContractionGTorsor`);
3. coordinate theory relative to a base point `t : T.carrier`:
   `localCoord D T t p` is the unique `gamma` with `[gamma, t] = p`;
   `localCoord_mk`, `localCoord_mk_self`, `localCoord_spec`,
   base-point change `localCoord (h • t) p = localCoord t p - delta(h)`, and
   the effect of the `F^x`-action on the torsor coordinate,
   `localCoord t [gamma, g • t] = gamma + delta(g)`;
4. the tensor-coordinate law.  In this `Gamma`-torsor model the `n`-fold
   tensor point is defined relative to a base point by multiplying the
   coordinate by `n`; the module records the coordinate law
   `localCoord (tensorPower t n p) = n • localCoord t p`, the iterated-tensor
   law, and the exact base-point-change correction.  This is a
   base-point-relative coordinate model, documented as such; no global tensor
   power of source objects is constructed here;
5. the finite-support predicate for a family of local points indexed by the
   finite places `v` of a number field, together with the base-point-change
   invariance of the predicate (changing the base point changes the coordinate
   by the principal divisor term `-D.finiteDelta h v`).

Boundary: this file constructs the local contraction and its coordinate
calculus only.  It does not construct the global torsor category, the global
contraction, the source theta-pilot objects, or the Hodge theater; the global
layer is expected to consume these local lemmas place by place.
-/

noncomputable section

namespace LeanFormal.IUT.IUTII.Frobenioid
namespace Example36

universe u v

/-! ## 0. Elementary laws of the local principal map -/

namespace LocalValueData

variable {F : Type u} {Gamma : Type v} [Field F] [AddCommGroup Gamma]

/-- The local principal map sends an inverse to the negative value. -/
theorem deltaAdd_inv_contraction (D : LocalValueData F Gamma) (x : Fˣ) :
    D.deltaAdd x⁻¹ = -D.deltaAdd x := by
  have hmul := D.deltaAdd_mul x x⁻¹
  rw [mul_inv_cancel, deltaAdd_one] at hmul
  exact eq_neg_of_add_eq_zero_right hmul.symm

/-- The local principal map sends a quotient to the difference of the values. -/
theorem deltaAdd_div (D : LocalValueData F Gamma) (x y : Fˣ) :
    D.deltaAdd (x / y) = D.deltaAdd x - D.deltaAdd y := by
  rw [div_eq_mul_inv, D.deltaAdd_mul, D.deltaAdd_inv_contraction]
  abel

end LocalValueData

/-! ## 1. The contracted product and its equivalence relation

The relation is the orbit relation of the diagonal action
`g • (gamma, t) = (gamma - delta(g), g • t)`: the pair `(gamma, t)` is
identified with `(gamma + delta(g), g • t)`.  We prove directly that it is an
equivalence relation, using additivity of `delta` and the torsor action
laws. -/

section Contraction

variable {F : Type u} {Gamma : Type v} [Field F] [AddCommGroup Gamma]
variable (D : LocalValueData F Gamma) (T : GTorsor Fˣ)

/-- The elementary relation of the contracted product: `q` is obtained from
`p` by moving the principal value `D.deltaAdd g` from the value coordinate
into the torsor coordinate.  Equivalently, `(gamma + delta(g), t)` is related
to `(gamma, g • t)`. -/
def localContractionRel (p q : Gamma × T.carrier) : Prop :=
  ∃ g : Fˣ, q = (p.1 - D.deltaAdd g, g • p.2)

/-- The relation is reflexive (the identity of `F^x` acts trivially). -/
theorem localContractionRel_refl (p : Gamma × T.carrier) :
    localContractionRel D T p p := by
  refine ⟨1, ?_⟩
  ext <;> simp

/-- The relation is symmetric, using `deltaAdd_inv_contraction` (the value of `g⁻¹` is
the negative of the value of `g`) and the inverse action law. -/
theorem localContractionRel_symm {p q : Gamma × T.carrier}
    (h : localContractionRel D T p q) : localContractionRel D T q p := by
  obtain ⟨g, rfl⟩ := h
  refine ⟨g⁻¹, ?_⟩
  ext
  · change p.1 = (p.1 - D.deltaAdd g) - D.deltaAdd g⁻¹
    rw [LocalValueData.deltaAdd_inv_contraction]
    abel
  · change p.2 = g⁻¹ • (g • p.2)
    rw [← mul_smul, inv_mul_cancel, one_smul]

/-- The relation is transitive, using additivity of the local principal map
and the action law `(h * g) • t = h • (g • t)`. -/
theorem localContractionRel_trans {p q r : Gamma × T.carrier}
    (h1 : localContractionRel D T p q) (h2 : localContractionRel D T q r) :
    localContractionRel D T p r := by
  obtain ⟨g, rfl⟩ := h1
  obtain ⟨h, rfl⟩ := h2
  refine ⟨h * g, ?_⟩
  ext
  · change (p.1 - D.deltaAdd g) - D.deltaAdd h = p.1 - D.deltaAdd (h * g)
    rw [LocalValueData.deltaAdd_mul]
    abel
  · change h • (g • p.2) = (h * g) • p.2
    rw [mul_smul]

/-- The setoid of the contracted product: the orbit equivalence of the
diagonal `F^x`-action. -/
def localContractionSetoid : Setoid (Gamma × T.carrier) where
  r := localContractionRel D T
  iseqv :=
    ⟨localContractionRel_refl D T,
      fun h => localContractionRel_symm D T h,
      fun h1 h2 => localContractionRel_trans D T h1 h2⟩

/-- The local contracted product `T_v = Gamma_v x^G T` of Example 3.6: the
quotient of `Gamma x T.carrier` by the relation
`(gamma + delta(g), t) ~ (gamma, g • t)`. -/
abbrev LocalContraction : Type (max u v) :=
  Quotient (localContractionSetoid D T)

/-- The class of a representative `(gamma, t)` in the local contraction. -/
abbrev localContractionMk (p : Gamma × T.carrier) : LocalContraction D T :=
  Quotient.mk (localContractionSetoid D T) p

/-- Two representatives define the same point of the local contraction exactly
when they are related. -/
theorem localContractionMk_eq_iff {p q : Gamma × T.carrier} :
    localContractionMk D T p = localContractionMk D T q ↔
      localContractionRel D T p q :=
  Quotient.eq

/-- The defining relation of the contracted product:
`(gamma + delta(g), t)` and `(gamma, g • t)` have the same class. -/
theorem localContractionMk_delta_smul (gamma : Gamma) (g : Fˣ) (t : T.carrier) :
    localContractionMk D T (gamma + D.deltaAdd g, t) =
      localContractionMk D T (gamma, g • t) := by
  apply Quotient.sound
  refine ⟨g, ?_⟩
  ext
  · change gamma = gamma + D.deltaAdd g - D.deltaAdd g
    abel
  · rfl

/-- The same defining relation in the other orientation. -/
theorem localContractionMk_smul_delta (gamma : Gamma) (g : Fˣ) (t : T.carrier) :
    localContractionMk D T (gamma, g • t) =
      localContractionMk D T (gamma + D.deltaAdd g, t) :=
  (localContractionMk_delta_smul D T gamma g t).symm

/-- Every point of the local contraction is represented by a pair. -/
theorem localContractionMk_surjective :
    Function.Surjective (localContractionMk D T) :=
  Quotient.mk_surjective

end Contraction

/-! ## 2. The action of the value group on the contracted product -/

section ValueGroupAction

variable {F : Type u} {Gamma : Type v} [Field F] [AddCommGroup Gamma]
variable (D : LocalValueData F Gamma) (T : GTorsor Fˣ)

open Multiplicative

/-- Translation of the value coordinate by a group element: the action of
`Multiplicative Gamma` on representatives of the contracted product. -/
def localContractionTranslate (m : Multiplicative Gamma) (p : Gamma × T.carrier) :
    Gamma × T.carrier :=
  (Multiplicative.toAdd m + p.1, p.2)

/-- The coordinate translation respects the contracted-product relation: it
acts only on the first coordinate. -/
theorem localContractionTranslate_respect (m : Multiplicative Gamma)
    {a b : Gamma × T.carrier} (h : localContractionRel D T a b) :
    localContractionRel D T (localContractionTranslate T m a)
      (localContractionTranslate T m b) := by
  obtain ⟨g, rfl⟩ := h
  refine ⟨g, ?_⟩
  ext
  · change Multiplicative.toAdd m + (a.1 - D.deltaAdd g) =
      (Multiplicative.toAdd m + a.1) - D.deltaAdd g
    abel
  · rfl

/-- The action of the value group `Multiplicative Gamma` on the local
contraction, by translation of the value coordinate. -/
def localContractionAddSmul (m : Multiplicative Gamma)
    (p : LocalContraction D T) : LocalContraction D T :=
  Quotient.map (localContractionTranslate T m)
    (fun _ _ h => localContractionTranslate_respect D T m h) p

instance localContractionSMul : SMul (Multiplicative Gamma) (LocalContraction D T) where
  smul := localContractionAddSmul D T

/-- The action on the class of a representative. -/
@[simp]
theorem localContractionAddSmul_mk (m : Multiplicative Gamma)
    (p : Gamma × T.carrier) :
    m • localContractionMk D T p =
      localContractionMk D T (Multiplicative.toAdd m + p.1, p.2) :=
  rfl

/-- The identity of the value group acts trivially. -/
theorem localContraction_one_smul (p : LocalContraction D T) :
    (1 : Multiplicative Gamma) • p = p := by
  induction p using Quotient.inductionOn with
  | h p =>
      rw [localContractionAddSmul_mk]
      apply Quotient.sound
      refine ⟨1, ?_⟩
      ext <;> simp

/-- The value-group action is associative. -/
theorem localContraction_mul_smul (m n : Multiplicative Gamma)
    (p : LocalContraction D T) :
    (m * n) • p = m • (n • p) := by
  induction p using Quotient.inductionOn with
  | h p =>
      rw [localContractionAddSmul_mk, localContractionAddSmul_mk,
        localContractionAddSmul_mk]
      have harith : Multiplicative.toAdd (m * n) + p.1 =
          Multiplicative.toAdd m + (Multiplicative.toAdd n + p.1) := by
        rw [toAdd_mul]
        abel
      rw [harith]

/-- The value-group action on the local contraction is a genuine `MulAction`. -/
instance localContractionMulAction :
    MulAction (Multiplicative Gamma) (LocalContraction D T) where
  one_smul := localContraction_one_smul D T
  mul_smul := localContraction_mul_smul D T

/-- **Freeness of the value-group action.**  If an element of the value group
fixes a point of the contracted product, then it is the identity. -/
theorem localContraction_smul_free (m : Multiplicative Gamma)
    (p : LocalContraction D T) (h : m • p = p) : m = 1 := by
  induction p using Quotient.inductionOn with
  | h p =>
      rw [localContractionAddSmul_mk] at h
      have hrel : localContractionRel D T
          (Multiplicative.toAdd m + p.1, p.2) p := Quotient.exact h
      obtain ⟨g, hg⟩ := hrel
      have hg1 : p.1 = (Multiplicative.toAdd m + p.1) - D.deltaAdd g :=
        congrArg Prod.fst hg
      have hg2 : p.2 = g • p.2 := congrArg Prod.snd hg
      have hg_eq : g = 1 := T.free g p.2 hg2.symm
      have hp1 : p.1 = Multiplicative.toAdd m + p.1 := by
        rw [hg_eq, LocalValueData.deltaAdd_one, sub_zero] at hg1
        exact hg1
      have hzero : Multiplicative.toAdd m = 0 := by
        have h4 : Multiplicative.toAdd m + p.1 = (0 : Gamma) + p.1 := by
          rw [zero_add]
          exact hp1.symm
        exact add_right_cancel h4
      rw [← ofAdd_toAdd m, hzero, ofAdd_zero]

/-- **Transitivity of the value-group action.**  Any two points of the local
contraction are related by a value-group element. -/
theorem localContraction_smul_transitive (p q : LocalContraction D T) :
    ∃ m : Multiplicative Gamma, m • p = q := by
  induction p using Quotient.inductionOn with
  | h p =>
      induction q using Quotient.inductionOn with
      | h q =>
          obtain ⟨g, hg⟩ := T.transitive p.2 q.2
          refine ⟨Multiplicative.ofAdd (q.1 + D.deltaAdd g - p.1), ?_⟩
          rw [localContractionAddSmul_mk]
          apply Quotient.sound
          refine ⟨g, ?_⟩
          ext
          · change q.1 = Multiplicative.toAdd (Multiplicative.ofAdd (q.1 + D.deltaAdd g - p.1)) +
                p.1 - D.deltaAdd g
            rw [toAdd_ofAdd]
            abel
          · change q.2 = g • p.2
            exact hg.symm

end ValueGroupAction

/-! ## 3. Packaging the contraction as a torsor

The `GTorsor` structure of `Example36TorsorTheory` requires the group and the
carrier to live in the same universe.  The value-group action above is
universe-polymorphic in `Gamma`; the torsor packaging is stated in the
same-universe case, which is the case of the Layer-1/2 local data (value group
`Gamma` and `F` both in one universe). -/

section GTorsorPackaging

variable {F : Type u} {Gamma : Type u} [Field F] [AddCommGroup Gamma]
variable (D : LocalValueData F Gamma) (T : GTorsor Fˣ)

/-- The local contracted product, packaged as a `Multiplicative Gamma`-torsor:
this is the local `Gamma_v`-torsor `T_v` of IUT III, Example 3.6. -/
def localContractionGTorsor : GTorsor (Multiplicative Gamma) where
  carrier := LocalContraction D T
  inst := localContractionMulAction D T
  nonempty := by
    obtain ⟨t⟩ := T.nonempty
    exact ⟨localContractionMk D T (0, t)⟩
  free := localContraction_smul_free D T
  transitive := localContraction_smul_transitive D T

/-- The carrier of the packaged torsor is the local contraction. -/
theorem localContractionGTorsor_carrier :
    (localContractionGTorsor D T).carrier = LocalContraction D T :=
  rfl

end GTorsorPackaging

/-! ## 4. Coordinate theory of the local contraction

A base point `t : T.carrier` gives the coordinate bijection
`LocalContraction D T ≃ Gamma`: the point `p` corresponds to the value
`gamma` with `[gamma, t] = p`.  This is the local value coordinate used by
the global degree/log-volume bookkeeping. -/

section Coordinates

variable {F : Type u} {Gamma : Type v} [Field F] [AddCommGroup Gamma]
variable (D : LocalValueData F Gamma) (T : GTorsor Fˣ)

/-- The value of a representative `(gamma, x)` relative to a base point `t`:
`gamma` plus the principal value of the torsor coordinate of `x` relative to
`t`.  This is the function on representatives that descends to the
coordinate map. -/
def localCoordRep (t : T.carrier) (p : Gamma × T.carrier) : Gamma :=
  p.1 + D.deltaAdd (T.coordinate t p.2)

/-- The representative-level formula is invariant under the contracted-product
relation, so it descends to the quotient. -/
theorem localCoordRep_respect (t : T.carrier) {a b : Gamma × T.carrier}
    (h : localContractionRel D T a b) :
    localCoordRep D T t a = localCoordRep D T t b := by
  obtain ⟨g, rfl⟩ := h
  have hcoord : T.coordinate t (g • a.2) = g * T.coordinate t a.2 :=
    GTorsor.coordinate_smul T t a.2 g
  rw [localCoordRep, localCoordRep, hcoord, LocalValueData.deltaAdd_mul,
    ← add_assoc, sub_add_cancel]

/-- The local value coordinate relative to a base point `t` of the torsor. -/
def localCoord (t : T.carrier) (p : LocalContraction D T) : Gamma :=
  Quotient.lift (localCoordRep D T t)
    (fun _ _ h => localCoordRep_respect D T t h) p

/-- The coordinate of the class of a representative `(gamma, x)`:
`gamma + delta(coordinate_t x)`. -/
@[simp]
theorem localCoord_mk (t : T.carrier) (gamma : Gamma) (x : T.carrier) :
    localCoord D T t (localContractionMk D T (gamma, x)) =
      gamma + D.deltaAdd (T.coordinate t x) :=
  rfl

/-- The coordinate of the class of `(gamma, t)` relative to the same base
point `t` is `gamma`. -/
@[simp]
theorem localCoord_mk_self (t : T.carrier) (gamma : Gamma) :
    localCoord D T t (localContractionMk D T (gamma, t)) = gamma := by
  rw [localCoord_mk, GTorsor.coordinate_self, LocalValueData.deltaAdd_one, add_zero]

/-- **The coordinate specifies the point**: the class of
`(localCoord t p, t)` is `p`. -/
theorem localCoord_spec (t : T.carrier) (p : LocalContraction D T) :
    localContractionMk D T (localCoord D T t p, t) = p := by
  induction p using Quotient.inductionOn with
  | h p =>
      rw [localCoord_mk]
      apply Quotient.sound
      refine ⟨T.coordinate t p.2, ?_⟩
      ext
      · change p.1 = p.1 + D.deltaAdd (T.coordinate t p.2) - D.deltaAdd (T.coordinate t p.2)
        abel
      · change p.2 = T.coordinate t p.2 • t
        exact (GTorsor.coordinate_spec T t p.2).symm

/-- **Base-point change**: the coordinate relative to `h • t` is the old
coordinate minus the principal value of `h`. -/
theorem localCoord_basePoint_change (t : T.carrier) (h : Fˣ)
    (p : LocalContraction D T) :
    localCoord D T (h • t) p = localCoord D T t p - D.deltaAdd h := by
  induction p using Quotient.inductionOn with
  | h p =>
      rw [localCoord_mk, localCoord_mk, GTorsor.coordinate_basePoint_change,
        LocalValueData.deltaAdd_mul, LocalValueData.deltaAdd_inv_contraction]
      abel

/-- The action of `F^x` on the torsor coordinate shifts the value coordinate
by the principal value. -/
@[simp]
theorem localCoord_mk_smul (t : T.carrier) (gamma : Gamma) (g : Fˣ) :
    localCoord D T t (localContractionMk D T (gamma, g • t)) =
      gamma + D.deltaAdd g := by
  rw [localCoord_mk, GTorsor.coordinate_smul, GTorsor.coordinate_self, mul_one]

/-- The value-group action shifts the coordinate additively. -/
theorem localCoord_smul (t : T.carrier) (m : Multiplicative Gamma)
    (p : LocalContraction D T) :
    localCoord D T t (m • p) = Multiplicative.toAdd m + localCoord D T t p := by
  induction p using Quotient.inductionOn with
  | h p =>
      rw [localContractionAddSmul_mk, localCoord_mk, localCoord_mk]
      abel

/-- The coordinate map is injective. -/
theorem localCoord_injective (t : T.carrier) :
    Function.Injective (localCoord D T t) := by
  intro p q h
  calc p = localContractionMk D T (localCoord D T t p, t) :=
        (localCoord_spec D T t p).symm
    _ = localContractionMk D T (localCoord D T t q, t) := by rw [h]
    _ = q := localCoord_spec D T t q

/-- Two points have the same coordinate relative to `t` exactly when they are
equal. -/
theorem localCoord_eq_iff (t : T.carrier) (p q : LocalContraction D T) :
    localCoord D T t p = localCoord D T t q ↔ p = q :=
  (localCoord_injective D T t).eq_iff

/-- The point of the local contraction with value coordinate `a` relative to
the base point `t`. -/
def localPoint (t : T.carrier) (a : Gamma) : LocalContraction D T :=
  localContractionMk D T (a, t)

/-- The coordinate of the point with coordinate `a` is `a`. -/
@[simp]
theorem localCoord_localPoint (t : T.carrier) (a : Gamma) :
    localCoord D T t (localPoint D T t a) = a :=
  localCoord_mk_self D T t a

/-- The point with coordinate `localCoord t p` is `p`. -/
theorem localPoint_localCoord (t : T.carrier) (p : LocalContraction D T) :
    localPoint D T t (localCoord D T t p) = p :=
  localCoord_spec D T t p

/-- The coordinate bijection `Gamma ≃ LocalContraction D T` determined by the
base point `t`. -/
def localPointEquiv (t : T.carrier) : Gamma ≃ LocalContraction D T where
  toFun := localPoint D T t
  invFun := localCoord D T t
  left_inv := localCoord_localPoint D T t
  right_inv := localPoint_localCoord D T t

/-- The coordinate bijection sends a value to the corresponding point. -/
@[simp]
theorem localPointEquiv_apply (t : T.carrier) (a : Gamma) :
    localPointEquiv D T t a = localPoint D T t a :=
  rfl

/-- The inverse of the coordinate bijection is the coordinate map. -/
@[simp]
theorem localPointEquiv_symm_apply (t : T.carrier) (p : LocalContraction D T) :
    (localPointEquiv D T t).symm p = localCoord D T t p :=
  rfl

end Coordinates

/-! ## 5. The tensor-coordinate law

In the `Gamma`-torsor model, the `n`-fold tensor point of a point `p` is
defined *relative to a chosen base point* `t` by multiplying the coordinate
`a = localCoord t p` by `n`.  This is the coordinate model of the tensor
power: the class is `[n • a, t]`.  The module proves the coordinate law, the
iterated-tensor law, and the exact base-point-change correction; it does not
construct a base-point-independent global tensor operation on source objects
(no sibling tensor-power file is available or used). -/

section TensorPower

variable {F : Type u} {Gamma : Type v} [Field F] [AddCommGroup Gamma]
variable (D : LocalValueData F Gamma) (T : GTorsor Fˣ)

/-- The `n`-fold tensor point of `p`, in the coordinate model relative to the
base point `t`: the point whose coordinate relative to `t` is `n` times the
coordinate of `p`. -/
def localTensorPower (t : T.carrier) (n : ℕ) (p : LocalContraction D T) :
    LocalContraction D T :=
  localPoint D T t (n • localCoord D T t p)

/-- **Tensor-coordinate law**: the `n`-fold tensor point has coordinate
`n • a` when `p` has coordinate `a`. -/
theorem localTensorPower_coordinate (t : T.carrier) (n : ℕ)
    (p : LocalContraction D T) :
    localCoord D T t (localTensorPower D T t n p) = n • localCoord D T t p :=
  localCoord_localPoint D T t (n • localCoord D T t p)

/-- The tensor point is represented by the pair `(n • a, t)`. -/
theorem localTensorPower_eq_localPoint (t : T.carrier) (n : ℕ)
    (p : LocalContraction D T) :
    localTensorPower D T t n p = localPoint D T t (n • localCoord D T t p) :=
  rfl

/-- The one-fold tensor point is the original point. -/
theorem localTensorPower_one (t : T.carrier) (p : LocalContraction D T) :
    localTensorPower D T t 1 p = p := by
  rw [localTensorPower_eq_localPoint, one_nsmul, localPoint_localCoord]

/-- The zero-fold tensor point is the zero coordinate point. -/
theorem localTensorPower_zero (t : T.carrier) (p : LocalContraction D T) :
    localTensorPower D T t 0 p = localPoint D T t 0 := by
  rw [localTensorPower_eq_localPoint, zero_nsmul]

/-- Iterating tensor powers multiplies the exponents. -/
theorem localTensorPower_tensorPower (t : T.carrier) (m n : ℕ)
    (p : LocalContraction D T) :
    localTensorPower D T t m (localTensorPower D T t n p) =
      localTensorPower D T t (m * n) p := by
  apply localCoord_injective D T t
  rw [localTensorPower_coordinate, localTensorPower_coordinate,
    localTensorPower_coordinate]
  rw [mul_comm m n, mul_nsmul]

/-- The coordinate of the tensor point under a base-point change: the
coordinate is transported through the principal correction term. -/
theorem localCoord_tensorPower_basePoint_change (t : T.carrier) (h : Fˣ)
    (n : ℕ) (p : LocalContraction D T) :
    localCoord D T t (localTensorPower D T (h • t) n p) =
      n • (localCoord D T t p - D.deltaAdd h) + D.deltaAdd h := by
  have hcoord : T.coordinate t (h • t) = h :=
    GTorsor.coordinate_apply T t (show h • t = h • t from rfl)
  rw [localTensorPower_eq_localPoint, localPoint, localCoord_mk, hcoord,
    localCoord_basePoint_change]

/-- **Base-point change of the tensor point**: changing the base point
`t ↦ h • t` changes the tensor point by the principal value-group element
`delta(h) - n • delta(h)`. -/
theorem localTensorPower_basePoint_change (t : T.carrier) (h : Fˣ)
    (n : ℕ) (p : LocalContraction D T) :
    localTensorPower D T (h • t) n p =
      Multiplicative.ofAdd (D.deltaAdd h - n • D.deltaAdd h) •
        localTensorPower D T t n p := by
  apply localCoord_injective D T t
  rw [localCoord_smul, localCoord_tensorPower_basePoint_change,
    localTensorPower_coordinate, toAdd_ofAdd, nsmul_sub]
  abel

end TensorPower

/-! ## 6. Finite support of a family of local points -/

section FiniteSupport

open scoped NumberField
open IsDedekindDomain NumberField

variable {F : Type u} [Field F] [NumberField F]
variable (D : GlobalPlaceData F) (T : GTorsor Fˣ)
variable (tau : (v : HeightOneSpectrum (𝓞 F)) → LocalContraction (D.finiteValue v) T)

/-- The value coordinate of the local point `tau v` at the finite place `v`
relative to the base point `t` of the global unit torsor. -/
def localCoordFamily (t : T.carrier) (v : HeightOneSpectrum (𝓞 F)) : ℤ :=
  localCoord (D.finiteValue v) T t (tau v)

/-- The finite places at which the family `tau` has a nonzero value
coordinate relative to the base point `t`. -/
def localPointFamilySupport (t : T.carrier) : Set (HeightOneSpectrum (𝓞 F)) :=
  {v | localCoordFamily D T tau t v ≠ 0}

/-- The family of local points has finite support if relative to some base
point of the torsor, only finitely many local coordinates are nonzero.  The
base-point-change lemmas below show that this does not depend on the choice of
base point, provided the global place data has finite principal support. -/
def HasFiniteSupportLocalFamily : Prop :=
  ∃ t : T.carrier, (localPointFamilySupport D T tau t).Finite

/-- Base-point change of the local coordinate family: changing the base point
`t ↦ h • t` subtracts the principal divisor value `D.finiteDelta h v`. -/
theorem localCoordFamily_basePoint_change (t : T.carrier) (h : Fˣ)
    (v : HeightOneSpectrum (𝓞 F)) :
    localCoordFamily D T tau (h • t) v =
      localCoordFamily D T tau t v - D.finiteDelta h v := by
  rw [localCoordFamily, localCoordFamily,
    localCoord_basePoint_change (D.finiteValue v) T t h (tau v)]
  rfl

/-- Changing the base point changes the support only by the (finite) principal
divisor support: the new support is contained in the union of the old support
and the support of `D.finiteDelta h`. -/
theorem localPointFamilySupport_basePoint_change_subset (t : T.carrier) (h : Fˣ) :
    localPointFamilySupport D T tau (h • t) ⊆
      localPointFamilySupport D T tau t ∪
        {v : HeightOneSpectrum (𝓞 F) | D.finiteDelta h v ≠ 0} := by
  intro v hv
  rw [Set.mem_union]
  by_cases hdelta : D.finiteDelta h v = 0
  · left
    rw [localPointFamilySupport, Set.mem_setOf_eq] at hv ⊢
    rw [localCoordFamily_basePoint_change, hdelta, sub_zero] at hv
    exact hv
  · right
    exact hdelta

/-- Finiteness of the local support is preserved under a base-point change,
provided the global place data has finite principal support. -/
theorem localPointFamilySupport_basePoint_change_finite
    (hfin : D.HasFiniteSupport) {t : T.carrier} (h : Fˣ)
    (ht : (localPointFamilySupport D T tau t).Finite) :
    (localPointFamilySupport D T tau (h • t)).Finite :=
  (ht.union (hfin h)).subset
    (localPointFamilySupport_basePoint_change_subset D T tau t h)

/-- Finiteness of the local support is independent of the base point. -/
theorem localPointFamilySupport_finite_iff_basePoint
    (hfin : D.HasFiniteSupport) (t : T.carrier) :
    (∃ t' : T.carrier, (localPointFamilySupport D T tau t').Finite) ↔
      (localPointFamilySupport D T tau t).Finite := by
  constructor
  · rintro ⟨t', ht'⟩
    obtain ⟨h, rfl⟩ := T.transitive t' t
    exact localPointFamilySupport_basePoint_change_finite D T tau hfin h ht'
  · intro ht
    exact ⟨t, ht⟩

/-- The finite-support predicate is equivalent to finiteness relative to any
chosen base point. -/
theorem hasFiniteSupportLocalFamily_iff_basePoint
    (hfin : D.HasFiniteSupport) (t : T.carrier) :
    HasFiniteSupportLocalFamily D T tau ↔
      (localPointFamilySupport D T tau t).Finite :=
  localPointFamilySupport_finite_iff_basePoint D T tau hfin t

/-- The identically zero family of local points. -/
def localFamilyZero (t : T.carrier) :
    (v : HeightOneSpectrum (𝓞 F)) → LocalContraction (D.finiteValue v) T :=
  fun v => localPoint (D.finiteValue v) T t 0

/-- The identically zero family has finite support (in fact empty support). -/
theorem localFamilyZero_hasFiniteSupport (t : T.carrier) :
    HasFiniteSupportLocalFamily D T (localFamilyZero D T t) := by
  refine ⟨t, ?_⟩
  have hempty : localPointFamilySupport D T (localFamilyZero D T t) t = ∅ := by
    ext v
    simp [localPointFamilySupport, localCoordFamily, localFamilyZero]
  rw [hempty]
  exact Set.finite_empty

end FiniteSupport

end Example36
end LeanFormal.IUT.IUTII.Frobenioid
