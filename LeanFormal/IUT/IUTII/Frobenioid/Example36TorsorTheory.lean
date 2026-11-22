import Mathlib.GroupTheory.GroupAction.Basic

/-!
# Torsor theory for IUT III, Example 3.6

Layer 3 begins here.  This file freezes the elementary theory of nonempty
G-torsors used in Example 3.6: a torsor is a type with a free and transitive
G-action.  We prove:

* translations on a torsor are unique, so the coordinate of a point relative
  to a base point is well defined;
* every torsor is nonempty and the coordinate map gives a bijection
  G ~ carrier for every base point;
* the base-point change formula for coordinates;
* every equivariant map of torsors is bijective, is determined by the image of
  a single base point, and every point of the target gives such a map.

The regular torsor (G acting on itself by left multiplication) is constructed.
These are the standard ingredients of the torsor half of Example 3.6; the local
contracted products Gamma_v x^G T and the global torsor category are in the
following files.
-/

noncomputable section

universe u

namespace LeanFormal.IUT.IUTII.Frobenioid
namespace Example36

/-- A nonempty G-torsor: a type with a free and transitive G-action. -/
structure GTorsor (G : Type u) [Group G] where
  /-- The underlying type of the torsor. -/
  carrier : Type u
  /-- The action of G on the carrier. -/
  [inst : MulAction G carrier]
  /-- The torsor is nonempty. -/
  nonempty : Nonempty carrier
  /-- The action is free. -/
  free : ∀ (g : G) (x : carrier), g • x = x → g = 1
  /-- The action is transitive. -/
  transitive : ∀ x y : carrier, ∃ g : G, g • x = y

attribute [instance] GTorsor.inst

namespace GTorsor

variable {G : Type u} [Group G]

/-- Two elements of the group translating a fixed point to a fixed point are
equal. -/
theorem translate_unique (T : GTorsor G) {x y : T.carrier} {g h : G}
    (hg : g • x = y) (hh : h • x = y) : g = h := by
  have h1 : (g⁻¹ * h) • x = x := by
    rw [mul_smul, hh, ← hg, inv_smul_smul]
  have h2 : g⁻¹ * h = 1 := T.free (g⁻¹ * h) x h1
  have h3 : h = g := by
    calc h = 1 * h := (one_mul h).symm
      _ = (g * g⁻¹) * h := by rw [mul_inv_cancel]
      _ = g * (g⁻¹ * h) := by rw [mul_assoc]
      _ = g * 1 := by rw [h2]
      _ = g := mul_one g
  exact h3.symm

/-- The coordinate of a point x relative to a base point t: the unique group
element g with g • t = x. -/
def coordinate (T : GTorsor G) (t x : T.carrier) : G :=
  Classical.choose (T.transitive t x)

theorem coordinate_spec (T : GTorsor G) (t x : T.carrier) :
    T.coordinate t x • t = x :=
  Classical.choose_spec (T.transitive t x)

theorem coordinate_apply (T : GTorsor G) (t : T.carrier) {g : G} {x : T.carrier}
    (h : g • t = x) : T.coordinate t x = g :=
  (translate_unique T (x := t) (y := x) h (coordinate_spec T t x)).symm

theorem coordinate_eq_iff (T : GTorsor G) (t x : T.carrier) (g : G) :
    T.coordinate t x = g ↔ g • t = x := by
  constructor
  · intro h
    rw [← h]
    exact coordinate_spec T t x
  · intro h
    exact coordinate_apply T t h

@[simp]
theorem coordinate_smul (T : GTorsor G) (t x : T.carrier) (g : G) :
    T.coordinate t (g • x) = g * T.coordinate t x :=
  coordinate_apply T t (by rw [mul_smul, coordinate_spec])

@[simp]
theorem coordinate_self (T : GTorsor G) (t : T.carrier) :
    T.coordinate t t = 1 :=
  coordinate_apply T t (one_smul G t)

/-- Base-point change for coordinates: the coordinate relative to h • t is the
old coordinate multiplied by h⁻¹ on the right. -/
theorem coordinate_basePoint_change (T : GTorsor G) (t : T.carrier) (h : G)
    (x : T.carrier) :
    T.coordinate (h • t) x = T.coordinate t x * h⁻¹ := by
  apply coordinate_apply
  rw [mul_smul, inv_smul_smul, coordinate_spec]

/-- The coordinate bijection of a torsor with its group, relative to a base
point. -/
def pointEquiv (T : GTorsor G) (t : T.carrier) : G ≃ T.carrier where
  toFun g := g • t
  invFun x := T.coordinate t x
  left_inv g := by
    show T.coordinate t (g • t) = g
    rw [coordinate_smul, coordinate_self, mul_one]
  right_inv x := coordinate_spec T t x

@[simp]
theorem pointEquiv_apply (T : GTorsor G) (t : T.carrier) (g : G) :
    T.pointEquiv t g = g • t := rfl

@[simp]
theorem pointEquiv_symm_apply (T : GTorsor G) (t x : T.carrier) :
    (T.pointEquiv t).symm x = T.coordinate t x := rfl

/-- The map determined by a base point x1 of the source and a point y2 of the
target: x is sent to coordinate(x1, x) • y2. -/
def equivariantMapOfPoint (T₁ T₂ : GTorsor G) (x₁ : T₁.carrier) (y₂ : T₂.carrier) :
    T₁.carrier → T₂.carrier :=
  fun x => T₁.coordinate x₁ x • y₂

theorem equivariantMapOfPoint_smul (T₁ T₂ : GTorsor G) (x₁ : T₁.carrier)
    (y₂ : T₂.carrier) (g : G) (x : T₁.carrier) :
    equivariantMapOfPoint T₁ T₂ x₁ y₂ (g • x) =
      g • equivariantMapOfPoint T₁ T₂ x₁ y₂ x := by
  simp only [equivariantMapOfPoint]
  rw [coordinate_smul, mul_smul]

@[simp]
theorem equivariantMapOfPoint_base (T₁ T₂ : GTorsor G) (x₁ : T₁.carrier)
    (y₂ : T₂.carrier) :
    equivariantMapOfPoint T₁ T₂ x₁ y₂ x₁ = y₂ := by
  simp [equivariantMapOfPoint]

theorem eq_equivariantMapOfPoint (T₁ T₂ : GTorsor G)
    (f : T₁.carrier → T₂.carrier)
    (hf : ∀ (g : G) (x : T₁.carrier), f (g • x) = g • f x) (x₁ : T₁.carrier) :
    f = equivariantMapOfPoint T₁ T₂ x₁ (f x₁) := by
  funext x
  conv_lhs => rw [← coordinate_spec T₁ x₁ x]
  rw [hf]
  rfl

theorem exists_eq_equivariantMapOfPoint (T₁ T₂ : GTorsor G)
    (f : T₁.carrier → T₂.carrier)
    (hf : ∀ (g : G) (x : T₁.carrier), f (g • x) = g • f x) (x₁ : T₁.carrier) :
    ∃ y₂ : T₂.carrier, f = equivariantMapOfPoint T₁ T₂ x₁ y₂ :=
  ⟨f x₁, eq_equivariantMapOfPoint T₁ T₂ f hf x₁⟩

theorem equivariantMapOfPoint_injective (T₁ T₂ : GTorsor G) (x₁ : T₁.carrier) :
    Function.Injective (fun y₂ : T₂.carrier => equivariantMapOfPoint (G := G) T₁ T₂ x₁ y₂) := by
  intro y₂ y₂' h
  have h' := congrFun h x₁
  simpa [equivariantMapOfPoint_base] using h'

/-- Every equivariant map of torsors is bijective. -/
theorem equivariantMapOfPoint_bijective (T₁ T₂ : GTorsor G) (x₁ : T₁.carrier)
    (y₂ : T₂.carrier) :
    Function.Bijective (equivariantMapOfPoint (G := G) T₁ T₂ x₁ y₂) := by
  constructor
  · intro x x' h
    have h1 : T₁.coordinate x₁ x • y₂ = T₁.coordinate x₁ x' • y₂ := h
    have h2 : ((T₁.coordinate x₁ x')⁻¹ * T₁.coordinate x₁ x) • y₂ = y₂ := by
      rw [mul_smul, h1, inv_smul_smul]
    have h3 : (T₁.coordinate x₁ x')⁻¹ * T₁.coordinate x₁ x = 1 :=
      T₂.free _ _ h2
    have hc : T₁.coordinate x₁ x = T₁.coordinate x₁ x' := by
      calc T₁.coordinate x₁ x
          = (T₁.coordinate x₁ x' * (T₁.coordinate x₁ x')⁻¹) * T₁.coordinate x₁ x := by
            rw [mul_inv_cancel, one_mul]
        _ = T₁.coordinate x₁ x' * ((T₁.coordinate x₁ x')⁻¹ * T₁.coordinate x₁ x) := by
            rw [mul_assoc]
        _ = T₁.coordinate x₁ x' * 1 := by rw [h3]
        _ = T₁.coordinate x₁ x' := mul_one _
    calc x = T₁.coordinate x₁ x • x₁ := (coordinate_spec T₁ x₁ x).symm
      _ = T₁.coordinate x₁ x' • x₁ := by rw [hc]
      _ = x' := coordinate_spec T₁ x₁ x'
  · intro y
    obtain ⟨c, hc⟩ := T₂.transitive y₂ y
    refine ⟨c • x₁, ?_⟩
    simp only [equivariantMapOfPoint]
    rw [coordinate_smul, coordinate_self, mul_one]
    exact hc

/-- The regular G-torsor: G acting on itself by left multiplication. -/
def regular (G : Type u) [Group G] : GTorsor G where
  carrier := G
  inst := inferInstance
  nonempty := ⟨1⟩
  free := by
    intro g x h
    have hx : g * x = x := by simpa using h
    calc g = g * 1 := (mul_one g).symm
      _ = g * (x * x⁻¹) := by rw [mul_inv_cancel]
      _ = (g * x) * x⁻¹ := (mul_assoc g x x⁻¹).symm
      _ = x * x⁻¹ := by rw [hx]
      _ = 1 := mul_inv_cancel x
  transitive := by
    intro x y
    refine ⟨y * x⁻¹, ?_⟩
    show (y * x⁻¹) * x = y
    rw [mul_assoc, inv_mul_cancel, mul_one]

/-- In the regular torsor the coordinate of x relative to x1 is x * x1⁻¹. -/
theorem regular_coordinate (x₁ x : G) :
    (regular G).coordinate x₁ x = x * x₁⁻¹ := by
  apply coordinate_apply
  show (x * x₁⁻¹) * x₁ = x
  rw [mul_assoc, inv_mul_cancel, mul_one]

/-- Equivariant maps between regular torsors are left multiplications. -/
theorem regular_equivariantMapOfPoint_apply (x₁ y₂ x : G) :
    equivariantMapOfPoint (regular G) (regular G) x₁ y₂ x = x * (x₁⁻¹ * y₂) := by
  simp only [equivariantMapOfPoint]
  rw [regular_coordinate]
  show (x * x₁⁻¹) * y₂ = x * (x₁⁻¹ * y₂)
  rw [mul_assoc]

end GTorsor

end Example36
end LeanFormal.IUT.IUTII.Frobenioid
