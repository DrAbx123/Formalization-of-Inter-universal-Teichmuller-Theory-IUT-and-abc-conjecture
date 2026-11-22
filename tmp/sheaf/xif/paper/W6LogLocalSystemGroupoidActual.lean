import Mathlib.CategoryTheory.Action
import Mathlib.CategoryTheory.IsConnected
import Mathlib.CategoryTheory.Groupoid
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# W6: log local systems, monodromy, and the groupoid encoding of Cor 3.12

Task W6 asks whether the qPilot/Theta compatibility can be encoded as
path-connectedness in a groupoid/stack of processions, Theta x mu-LGP links and
Ind1-3 indeterminacies, with the log-volume a local system to @Real@, and
"trivial monodromy => paths preserve the log".

This file builds the abstract categorical layer only; the IUT specific
instantiation is in @W6ActualPilotMonodromyActual@ and
@W6RootStackMonodromyActual@.

The structural facts proved here:

* @LogLocalSystem.val_eq_of_monodromy_eq_zero@ and the connected version: zero
  monodromy really does make the log value path independent;
* @LogLocalSystem.le_iff_monodromy_nonneg@: the oriented paper inequality
  @qLog <= thetaLog@ along a link is *exactly* nonnegativity of the monodromy
  of the log local system along that link;
* @laxLog_val_eq_of_groupoid@: in a **groupoid** every morphism is invertible,
  so an oriented (lax) log comparison automatically collapses to *equality*.
  A groupoid encoding of compatibility is therefore strictly stronger than
  Cor 3.12 and cannot be paper-faithful unless the two log values coincide;
* the indiscrete translation groupoid on @Real@ (@linkGroupoid@) is the
  log-value shadow of any link groupoid: any two log values are connected, the
  monodromy of the connector is exactly the difference of the values, and a
  *zero* monodromy connector exists iff the two values are equal
  (@linkGroupoid_trivial_monodromy_iff_eq@).

No sorry, no axiom, no fake carrier.
-/

noncomputable section
open CategoryTheory

universe u v

namespace LeanFormal.IUT.XiFPaper.W6LogLocalSystemGroupoidActual

/-! ## 1. Log local systems and monodromy -/

/-- A real valued log local system on a category: a real value on objects, and an
additive monodromy along morphisms which measures the change of the log value.
This is the unbundled form of a functor to the delooping of the additive reals,
together with the invariant value function. -/
structure LogLocalSystem (C : Type u) [Category.{v} C] where
  /-- The log value on objects. -/
  val : C -> Real
  /-- The monodromy (log transport) along a morphism. -/
  monodromy : {X Y : C} -> (X ⟶ Y) -> Real
  /-- The identity morphism has zero monodromy. -/
  monodromy_id : forall (X : C), monodromy (𝟙 X) = 0
  /-- Monodromy is additive under composition. -/
  monodromy_comp : forall {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z),
    monodromy (f ≫ g) = monodromy f + monodromy g
  /-- A morphism changes the log value by its monodromy. -/
  val_eq : forall {X Y : C} (f : X ⟶ Y), val Y = val X + monodromy f

namespace LogLocalSystem

variable {C : Type u} [Category.{v} C]

/-- A morphism with zero monodromy preserves the log value: the precise form of
"if the monodromy is trivial then the path preserves the log". -/
theorem val_eq_of_monodromy_eq_zero (L : LogLocalSystem C) {X Y : C} (f : X ⟶ Y)
    (h : L.monodromy f = 0) : L.val X = L.val Y := by
  have h' := L.val_eq f
  rw [h, add_zero] at h'
  exact h'.symm

/-- Conversely, a morphism along which the log value is unchanged has zero
monodromy. -/
theorem monodromy_eq_zero_of_val_eq (L : LogLocalSystem C) {X Y : C} (f : X ⟶ Y)
    (h : L.val X = L.val Y) : L.monodromy f = 0 := by
  have h' := L.val_eq f
  rw [h] at h'
  linarith

/-- If every morphism has zero monodromy, the log is constant on a connected
category. -/
theorem val_eq_of_isConnected (L : LogLocalSystem C) [IsConnected C]
    (h : forall {X Y : C} (f : X ⟶ Y), L.monodromy f = 0) (X Y : C) :
    L.val X = L.val Y :=
  constant_of_preserves_morphisms L.val
    (fun X Y f => L.val_eq_of_monodromy_eq_zero f (h f)) X Y

/-- On a connected category, path independence of the log is *equivalent* to
triviality of the monodromy of every morphism. -/
theorem val_const_iff_monodromy_zero (L : LogLocalSystem C) [IsConnected C] :
    (forall X Y : C, L.val X = L.val Y) <->
      (forall {X Y : C} (f : X ⟶ Y), L.monodromy f = 0) := by
  constructor
  · intro h X Y f
    exact L.monodromy_eq_zero_of_val_eq f (h X Y)
  · intro h X Y
    exact L.val_eq_of_isConnected h X Y

/-- **The oriented form of Cor 3.12.**  Along a link @f : q ⟶ theta@, the paper
inequality @val q <= val theta@ holds if and only if the monodromy of the log
local system along the link is nonnegative.  Cor 3.12 is therefore precisely an
*orientation* statement about the monodromy; it is not a triviality of
connectedness. -/
theorem le_iff_monodromy_nonneg (L : LogLocalSystem C) {X Y : C} (f : X ⟶ Y) :
    (L.val X <= L.val Y) <-> 0 <= L.monodromy f := by
  have h := L.val_eq f
  constructor <;> intro hh <;> linarith

/-- If the two log values differ, then *no* morphism between them can have zero
monodromy.  This is the obstruction form used for the actual pilots. -/
theorem no_zero_monodromy_of_val_ne (L : LogLocalSystem C) {X Y : C} (f : X ⟶ Y)
    (h : L.val X ≠ L.val Y) : L.monodromy f ≠ 0 := by
  intro hzero
  exact h (L.val_eq_of_monodromy_eq_zero f hzero)

end LogLocalSystem

/-! ## 2. Oriented (lax) logs and the groupoid collapse -/

/-- An oriented log comparison: the log value can only *increase* along
morphisms.  This is a lax functor to the poset @(Real, <=)@; it is the structure
that actually matches the paper's @Iic@ ray @hullLogVolumeRay@. -/
structure LaxLog (C : Type u) [Category.{v} C] where
  /-- The log value on objects. -/
  val : C -> Real
  /-- The value is monotone along morphisms. -/
  mono : forall {X Y : C}, (X ⟶ Y) -> val X <= val Y

/-- **The groupoid collapse.**  In a groupoid every morphism is invertible, so an
oriented (lax) log comparison forces equality of the two log values.  Thus, if
compatibility is encoded as a morphism in a *groupoid* and the log is order
preserving, the conclusion is the *equality* of the two log volumes, not the
paper's inequality.  Equality is strictly stronger than Cor 3.12 and, for the
actual stacky/qPilot scalars, is equivalent to the open S736 statement
@c_norm = order@ (see @W6RootStackMonodromyActual@). -/
theorem laxLog_val_eq_of_groupoid {C : Type u} [Groupoid C] (L : LaxLog C)
    {X Y : C} (f : X ⟶ Y) : L.val X = L.val Y :=
  le_antisymm (L.mono f) (L.mono (Groupoid.inv f))

/-! ## 3. The translation link groupoid: connectedness is free, monodromy is the
log difference -/

/-- The indiscrete translation groupoid on @Real@: objects are possible log
values, and a morphism @x ⟶ y@ is a real number @t@ with @x + t = y@ (the
translation, i.e. the log transport).  Every two objects are connected by a
unique morphism, so this is the "space in which the two pilots are homotopic"
seen through the log-volume only. -/
abbrev linkGroupoid : Type := Real

namespace linkGroupoid

instance : Category linkGroupoid where
  Hom x y := { t : Real // x + t = y }
  id := fun x => ⟨0, by simp⟩
  comp := fun {x y z} f g => ⟨f.val + g.val, by
    have hf : x + f.val = y := f.property
    have hg : y + g.val = z := g.property
    show x + (f.val + g.val) = z
    rw [← add_assoc, hf, hg]⟩
  id_comp := fun {x y} f => by apply Subtype.ext; simp
  comp_id := fun {x y} f => by apply Subtype.ext; simp
  assoc := fun {w x y z} f g h => by apply Subtype.ext; simp [add_assoc]


/-- Every morphism of the translation groupoid is invertible: it is the groupoid
of log transports. -/
instance : Groupoid linkGroupoid where
  inv := fun {x y} f => ⟨-f.val, by
    have h : x + f.val = y := f.property
    show y + -f.val = x
    linarith⟩
  inv_comp := fun {x y} f => by
    apply Subtype.ext
    show -f.val + f.val = 0
    ring
  comp_inv := fun {x y} f => by
    apply Subtype.ext
    show f.val + -f.val = 0
    ring

/-- The translation groupoid is connected: any two log values are joined by a
unique transport. -/
instance : IsConnected linkGroupoid := by
  apply zigzag_isConnected
  intro x y
  have h : x ⟶ y := ⟨y - x, by show x + (y - x) = y; ring⟩
  exact Zigzag.of_hom h

/-- The log local system of the translation groupoid: the value is the point
itself and the monodromy is the translation. -/
def logSystem : LogLocalSystem linkGroupoid where
  val x := x
  monodromy f := f.val
  monodromy_id X := rfl
  monodromy_comp f g := rfl
  val_eq f := by
    linarith [f.property]

/-- Any two log values are connected: connectedness carries no information. -/
theorem exists_hom (x y : linkGroupoid) : Nonempty (x ⟶ y) :=
  ⟨⟨y - x, by show x + (y - x) = y; ring⟩⟩

/-- The monodromy along the canonical connector is exactly the log difference. -/
theorem monodromy_eq_sub (x y : linkGroupoid) :
    exists f : x ⟶ y, logSystem.monodromy f = y - x :=
  ⟨⟨y - x, by show x + (y - x) = y; ring⟩, rfl⟩

/-- **The crux.**  A connector with trivial monodromy exists iff the two log
values are equal.  "Same connected component and trivial monodromy" is
literally the log equality, not a weaker geometric statement. -/
theorem trivial_monodromy_iff_eq (x y : linkGroupoid) :
    (exists f : x ⟶ y, logSystem.monodromy f = 0) <-> x = y := by
  constructor
  · rintro ⟨f, hf⟩
    have h := logSystem.val_eq f
    rw [hf, add_zero] at h
    exact h.symm
  · rintro rfl
    exact ⟨𝟙 _, logSystem.monodromy_id _⟩

/-- The oriented form: the paper inequality between two log values is exactly
nonnegativity of the monodromy of the connector. -/
theorem le_iff_monodromy_nonneg (x y : linkGroupoid) :
    x <= y <-> exists f : x ⟶ y, 0 <= logSystem.monodromy f := by
  constructor
  · intro h
    obtain ⟨f, hf⟩ := monodromy_eq_sub x y
    exact ⟨f, by rw [hf]; linarith⟩
  · rintro ⟨f, hf⟩
    exact (logSystem.le_iff_monodromy_nonneg f).mpr hf

/-- The log-value shadow of an arbitrary link: any morphism of any category with
a log local system produces a morphism of the translation groupoid whose
monodromy is exactly the monodromy of the original link.  So no information is
lost by passing to this groupoid, and none is gained. -/
theorem shadow_monodromy {C : Type u} [Category.{v} C] (L : LogLocalSystem C)
    {X Y : C} (f : X ⟶ Y) :
    logSystem.monodromy ⟨L.val Y - L.val X, by
      show L.val X + (L.val Y - L.val X) = L.val Y
      ring⟩ = L.monodromy f := by
  show L.val Y - L.val X = L.monodromy f
  have h := L.val_eq f
  linarith

end linkGroupoid

end LeanFormal.IUT.XiFPaper.W6LogLocalSystemGroupoidActual
