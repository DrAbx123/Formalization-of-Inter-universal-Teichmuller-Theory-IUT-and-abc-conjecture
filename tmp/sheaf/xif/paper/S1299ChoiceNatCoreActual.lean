import LeanFormal.IUT.IUTIII.Theorem311.MultiradialOutputKernel
import tmp.sheaf.xif.paper.S1225SourceStripOfChoiceActual

/-! # S1299: an actual Core on Choice = I.family.index × Nat

## What this file does

S1282 proved that on the original source choice

    Choice = I.family.index

there is no total level with the additive law level (ind3 n c) = level c + n
(and, more strongly, any level invariant under the actual ind1/ind2 is
constant).  This file follows the recommended enlargement

    Choice := I.family.index × Nat,
    ind3 n (i, m) = (i, m + n),
    level (i, m) = m.

Strictly, the kernel type is Core Label Choice.  The requested product is the
Choice parameter; Label remains ℤ, as in S1231.  OriginalInput supplies no
AddGroup instance on I.family.index, so the product cannot be used as Label
without adding structure, and all three operations below act on Choice.  The
reading of level = id used here is the identity on the added Nat coordinate:
level (i, m) = m.

The first coordinate is the original source index and the second coordinate is
an added Nat bookkeeping coordinate.  ind1 acts on the first coordinate by
the actual family permutation I.family.permutation (the S1256 Ind1 candidate),
ind2 preserves the first coordinate (the identity action), and ind3 acts
only on the Nat coordinate.  Thus the additive level law holds exactly,
unlike on the original choice.

## Scope and honesty

This CHANGES the Choice object.  It is not a Core on
Choice = I.family.index, does not contradict S1282's
no_additive_sourceLevel, and does not construct the source Ind1/Ind2
operations.  In particular:

* the Nat coordinate is an added coordinate, not a field extracted from
  OriginalInput;
* ind2 is the identity on the index coordinate because no actual source
  Ind2 operation on I.family.index is available;
* ind1 is the actual I.family.permutation, not a coordinate shift through
  index_equiv (the substitution excluded by S1256).

The construction is therefore a genuine Core on the enlarged object, with an
explicit statement of what was added.  It is not presented as a solution of the
original source-level problem.

## The fifteen law statements

The Core structure has fourteen law fields:
ind1_zero, ind1_add, ind1_inverse, ind2_zero, ind2_add,
ind2_inverse, ind3_zero, ind3_add, ind1_ind2_commute,
ind1_ind3_commute, ind2_ind3_commute, ind1_level, ind2_level,
ind3_level.  All fourteen are proved below.  The additive law
core_ind3_level_eq is the fifteenth law statement; it is the exact law that
fails on the old choice and holds here by construction.

## Strip map

stripOfChoice is the actual S1225 strip map on the first coordinate and
ignores the Nat coordinate.  It is not a new choice of strip.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.XiFPaper.S1299ChoiceNatCoreActual

open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.MultiradialKernel

universe ua uv upi umon ui
variable {l : PrimeGeFive} {V : Type uv}
variable (I : OriginalInput.{ua, uv, upi, umon, ui} l V)

/-! ## 1. The enlarged choice and its three operations -/

/-- The enlarged choice: the original source index together with an added
Nat coordinate.  This is a change of the Choice object, not of the source
index. -/
abbrev Choice : Type ui := I.family.index × Nat

/-- The base point: the source base index with level 0. -/
def base : Choice (I := I) := (I.indexOf 0 0, 0)

/-- The level is the added Nat coordinate (level = id on that
coordinate). -/
def level (c : Choice (I := I)) : Nat := c.2

/-- The actual family-permutation action on the source index, lifted into the
first coordinate.  This is I.family.permutation, not a coordinate shift
through index_equiv. -/
noncomputable def familyPermAction (g : ℤ) (i : I.family.index) : I.family.index :=
  (I.family.permutation ^ (-g)) i

/-- ind1 acts on the source index by the actual family permutation and
preserves the Nat coordinate. -/
noncomputable def ind1 (g : ℤ) (c : Choice (I := I)) : Choice (I := I) :=
  (familyPermAction I g c.1, c.2)

/-- ind2 preserves the source index coordinate.  No actual source Ind2
operation is being asserted; this is the allowed index-preserving action. -/
def ind2 (_g : ℤ) (c : Choice (I := I)) : Choice (I := I) := c

/-- ind3 acts only on the added Nat coordinate. -/
def ind3 (n : Nat) (c : Choice (I := I)) : Choice (I := I) :=
  (c.1, c.2 + n)

/-! ## 2. Coordinate behaviour, stated explicitly -/

@[simp] theorem ind1_fst (g : ℤ) (c : Choice (I := I)) :
    (ind1 I g c).1 = familyPermAction I g c.1 := rfl

@[simp] theorem ind1_snd (g : ℤ) (c : Choice (I := I)) :
    (ind1 I g c).2 = c.2 := rfl

@[simp] theorem ind2_fst (g : ℤ) (c : Choice (I := I)) :
    (ind2 I g c).1 = c.1 := rfl

@[simp] theorem ind2_snd (g : ℤ) (c : Choice (I := I)) :
    (ind2 I g c).2 = c.2 := rfl

@[simp] theorem ind3_fst (n : Nat) (c : Choice (I := I)) :
    (ind3 I n c).1 = c.1 := rfl

@[simp] theorem ind3_snd (n : Nat) (c : Choice (I := I)) :
    (ind3 I n c).2 = c.2 + n := rfl

/-! ## 3. The actual Core and its fourteen structure laws -/

/-- A Core on Choice = I.family.index × Nat with level the Nat
coordinate.  ind1 is the actual family permutation, ind2 preserves the
index coordinate, and ind3 shifts the Nat coordinate. -/
noncomputable def core : Core ℤ (Choice (I := I)) where
  base := base I
  level := level I
  ind1 := ind1 I
  ind2 := ind2 I
  ind3 := ind3 I
  ind1_zero := by
    intro c
    exact Prod.ext (by
      change familyPermAction I 0 c.1 = c.1
      unfold familyPermAction
      rw [neg_zero, zpow_zero]
      rfl) rfl
  ind1_add := by
    intro g h c
    exact Prod.ext (by
      change familyPermAction I (g + h) c.1 =
        familyPermAction I h (familyPermAction I g c.1)
      unfold familyPermAction
      rw [← Equiv.Perm.mul_apply]
      congr 1
      rw [← zpow_add]
      congr 1
      ring_nf) rfl
  ind1_inverse := by
    intro g c
    exact Prod.ext (by
      change familyPermAction I (-g) (familyPermAction I g c.1) = c.1
      unfold familyPermAction
      rw [← Equiv.Perm.mul_apply]
      rw [← zpow_add]
      have h : - -g + -g = 0 := by ring
      rw [h, zpow_zero]
      rfl) rfl
  ind2_zero := by
    intro c
    rfl
  ind2_add := by
    intro g h c
    rfl
  ind2_inverse := by
    intro g c
    rfl
  ind3_zero := by
    intro c
    exact Prod.ext rfl (Nat.add_zero c.2)
  ind3_add := by
    intro m n c
    exact Prod.ext rfl (Nat.add_assoc c.2 m n).symm
  ind1_ind2_commute := by
    intro g h c
    rfl
  ind1_ind3_commute := by
    intro g n c
    rfl
  ind2_ind3_commute := by
    intro g n c
    rfl
  ind1_level := by
    intro g c
    rfl
  ind2_level := by
    intro g c
    rfl
  ind3_level := by
    intro n c
    exact Nat.le_add_right c.2 n

/-! ## 4. Projection lemmas for the constructed core -/

@[simp] theorem core_base : (core I).base = base I := rfl

@[simp] theorem core_level (c : Choice (I := I)) :
    (core I).level c = c.2 := rfl

@[simp] theorem core_ind1 (g : ℤ) (c : Choice (I := I)) :
    (core I).ind1 g c = ind1 I g c := rfl

@[simp] theorem core_ind2 (g : ℤ) (c : Choice (I := I)) :
    (core I).ind2 g c = ind2 I g c := rfl

@[simp] theorem core_ind3 (n : Nat) (c : Choice (I := I)) :
    (core I).ind3 n c = ind3 I n c := rfl

/-- The fifteenth law statement: the level is additive under ind3.  This is
the law that S1282 proved impossible on the original Choice. -/
theorem core_ind3_level_eq (n : Nat) (c : Choice (I := I)) :
    (core I).level ((core I).ind3 n c) = (core I).level c + n := rfl

/-! ## 5. Non-degeneracy of the level -/

/-- Every natural number occurs as a level. -/
theorem level_unbounded (N : Nat) : ∃ c : Choice (I := I), (core I).level c = N :=
  ⟨(I.indexOf 0 0, N), rfl⟩

/-- The level is not constant. -/
theorem level_not_constant : (core I).level (I.indexOf 0 0, 1) ≠
    (core I).level (I.indexOf 0 0, 0) := by
  simp

/-- A positive ind3 shift strictly increases the level. -/
theorem level_ind3_strict (n : Nat) (hn : 0 < n) (c : Choice (I := I)) :
    (core I).level c < (core I).level ((core I).ind3 n c) := by
  rw [core_ind3_level_eq]
  omega

/-! ## 6. The strip map ignores the added Nat coordinate -/

/-- The first-coordinate projection, which forgets the added Nat
coordinate. -/
def forgetNat (c : Choice (I := I)) : I.family.index := c.1

@[simp] theorem forgetNat_mk (i : I.family.index) (m : Nat) :
    forgetNat I (i, m) = i := rfl

@[simp] theorem forgetNat_ind1 (g : ℤ) (c : Choice (I := I)) :
    forgetNat I (ind1 I g c) = familyPermAction I g (forgetNat I c) := rfl

@[simp] theorem forgetNat_ind2 (g : ℤ) (c : Choice (I := I)) :
    forgetNat I (ind2 I g c) = forgetNat I c := rfl

@[simp] theorem forgetNat_ind3 (n : Nat) (c : Choice (I := I)) :
    forgetNat I (ind3 I n c) = forgetNat I c := rfl

/-- The actual S1225 strip map, applied to the first coordinate. -/
noncomputable def stripOfChoice (c : Choice (I := I)) :
    FPrimeStrip.{umon, uv, upi} V :=
  S1225SourceStripOfChoiceActual.stripOfChoice I c.1

@[simp] theorem stripOfChoice_mk (i : I.family.index) (m : Nat) :
    stripOfChoice I (i, m) =
      S1225SourceStripOfChoiceActual.stripOfChoice I i := rfl

/-- stripOfChoice ignores the Nat coordinate. -/
theorem stripOfChoice_ignores_nat (i : I.family.index) (m n : Nat) :
    stripOfChoice I (i, m) = stripOfChoice I (i, n) := rfl

/-- In particular, stripOfChoice is invariant under ind3. -/
theorem stripOfChoice_ind3 (n : Nat) (c : Choice (I := I)) :
    stripOfChoice I (ind3 I n c) = stripOfChoice I c := rfl

/-- stripOfChoice is invariant under the index-preserving ind2. -/
theorem stripOfChoice_ind2 (g : ℤ) (c : Choice (I := I)) :
    stripOfChoice I (ind2 I g c) = stripOfChoice I c := rfl

/-- The strip map factors through forgetNat. -/
theorem stripOfChoice_comp_forgetNat :
    stripOfChoice I = fun c : Choice (I := I) =>
      S1225SourceStripOfChoiceActual.stripOfChoice I (forgetNat I c) := rfl

/-- At a lattice point, the strip map is the actual fPrimeStripAt. -/
theorem stripOfChoice_indexOf (a b : Int) (m : Nat) :
    stripOfChoice I (I.indexOf a b, m) = I.fPrimeStripAt a b := by
  simp [stripOfChoice]

/-- The strip map recovers the source theater strip at the first
coordinate. -/
theorem stripOfChoice_eq_theater (i : I.family.index) (m : Nat) :
    stripOfChoice I (i, m) = (I.family.theater i).primeStrip := by
  simp [stripOfChoice,
    S1225SourceStripOfChoiceActual.stripOfChoice_eq_theater]

end LeanFormal.IUT.XiFPaper.S1299ChoiceNatCoreActual
end
