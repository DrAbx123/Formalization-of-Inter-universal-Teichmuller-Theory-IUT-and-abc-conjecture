/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.RefLANAMultiradialSpecActual

/-!
# Mzk1ProcessionInd23ObjectActual — LANA procession / Ind2 / Ind3 / roots-of-unity objects

A516: reference objects from LANA latest `Iut/Multiradial/Spec.lean` and
`Iut/HodgeTheater/Procession.lean`:

* the `n`-procession object `Procession C n` and its groupoid of isomorphisms
  (IUT I Def. 4.10; input groupoid of Theorem 3.11(i));
* the (Ind2)-group `Ind2Group lstar V Ism` and its single-copy element;
* the (Ind3) upper-semi-compatibility data `UpperSemi`/`ind3Possible` and the
  union identity `sUnion_ind3Possible`;
* data up to roots of unity `ModMu` (Remark 3.11.4(i)).

No new axiom, no comparison. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 8000000

namespace LeanFormal.IUT.XiFPaper.Mzk1ProcessionInd23ObjectActual

open Iut.Multiradial
universe u v w w'

/-! ### Procession object -/

/-- The `n`-procession object (IUT I Def. 4.10). -/
abbrev ProcessionObject (C : Type u) [Category.{v} C] (n : ℕ) :=
  Procession C n

/-- The groupoid structure of processions (input groupoid of Thm 3.11(i)). -/
instance processionGroupoid (C : Type u) [Category.{v} C] (n : ℕ) :
    Groupoid (Procession C n) := Procession.groupoid

/-- The identity isomorphism of a procession object. -/
def processionId {C : Type u} [Category.{v} C] {n : ℕ} (P : Procession C n) : P ⟶ P := 𝟙 P

/-! ### (Ind2)-group -/

variable {lstar : ℕ} {V : Type*} {Ism : V → Type*} [∀ v, Group (Ism v)]

/-- The (Ind2)-group object: independent copies on each summand of each factor. -/
abbrev Ind2Object := Ind2Group lstar V Ism

/-- A single-copy element of the (Ind2)-group. -/
noncomputable def ind2Object_single [DecidableEq V]
    (j : Fin (lstar + 1)) (i : Fin (j + 1)) (v : V) (g : Ism v) :
    Ind2Object (lstar := lstar) (V := V) (Ism := Ism) :=
  Ind2Group.single j i v g

/-- The single-copy element acts as `g` on its own summand. -/
theorem ind2Object_single_apply [DecidableEq V]
    (j : Fin (lstar + 1)) (i : Fin (j + 1)) (v : V) (g : Ism v) :
    ind2Object_single (lstar := lstar) (V := V) (Ism := Ism) j i v g j i v = g :=
  Ind2Group.single_apply_self j i v g

/-! ### (Ind3): upper semi-compatibility -/

variable {X : Type*}

/-- The (Ind3) possible-region object: regions upper semi-compatible with `R`. -/
def Ind3Object (R : Set X) : Set (Set X) := ind3Possible R

/-- The union of the possible regions modulo (Ind3) is the region itself. -/
theorem ind3Object_union (R : Set X) : ⋃₀ Ind3Object R = R :=
  sUnion_ind3Possible R

/-- The possible regions modulo (Ind3) form the lower set `Iic R`. -/
theorem ind3Object_eq (R : Set X) : Ind3Object R = Set.Iic R :=
  ind3Possible_eq_Iic R

/-! ### Data up to roots of unity -/

variable (M : Type*) [CommMonoid M]

/-- The data object modulo multiplication by roots of unity (Remark 3.11.4(i)). -/
abbrev ModMuObject := ModMu M

/-- The class of `x` modulo roots of unity. -/
def modMuObject_mk (x : M) : ModMuObject M := ModMu.mk x

/-- Two classes agree iff the data differ by a root of unity. -/
theorem modMuObject_mk_eq_mk_iff (x y : M) :
    modMuObject_mk M x = modMuObject_mk M y ↔
      ∃ ζ : Mˣ, IsOfFinOrder ζ ∧ (ζ : M) * x = y :=
  ModMu.mk_eq_mk_iff x y

#check ind2Object_single_apply
#check ind3Object_union
#check modMuObject_mk_eq_mk_iff

end LeanFormal.IUT.XiFPaper.Mzk1ProcessionInd23ObjectActual
end
