import tmp.sheaf.xif.paper.S1962R1AbstractActionActual
import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.Group.Hom.Basic

set_option maxHeartbeats 1000000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

/-!
# S1976: the abstract dagger-F_v G-action and the local actual strip

Layer: O (original Theta-link / q-pilot), continuation of S1962.

## The question

S1962 isolates the third R1 missing:

  R1AbstractActionOnDaggerFMissing F v

meaning that the abstract F-prime-strip F admits a G-action on its value
monoid whose pullback along the mono-analytic projection is the given
Pi-action.  The local actual F-prime-strip of S1962 inhabits this interface
(the actual Krull action), but the paper's abstract dagger-F is an explicit
source input: SourceTheaterRealization proves that its carrier is not
determined by Definition 3.1 data alone.  Thus the interface is a genuine
comparison gap, not a vacuous Nonempty gate.

This file determines exactly what can and cannot be proved about that
interface from the FPrimeStrip fields alone.

## What is constructed

1. Characterization.  For an arbitrary FPrimeStrip F and place v, a
   compatible G-action exists if and only if the Pi-action is constant on the
   fibres of F.proj v.  This is the descent condition PiActionDescends F v.
   The proof of the forward direction is immediate from compatibility; the
   reverse direction chooses preimages of the surjection F.proj v and uses
   descent to prove that the resulting map is a well-defined MonoidHom.

2. Uniqueness.  A compatible G-action is unique when it exists.  Hence the
   construction from descent does not depend on the chosen preimages, and the
   chosen-preimage formula is canonical on any section of F.proj v.

3. Transport along FPrimeStripEquiv.  A G-action transports across a prime
   strip equivalence, so existence of the action is invariant under
   FPrimeStripEquiv.  This gives the genuine comparison route: an explicit
   FPrimeStripEquiv between an abstract strip and the local actual strip
   transports the actual Krull action to the abstract strip.

4. The local actual model.  localFPrimeStrip v has proj = id, so its
   Pi-action descends; the construction returns exactly the Krull action and
   agrees with S1962's localAbstractGvAction.  Refl comparison to the local
   actual strip recovers the same action.

5. Non-derivability.  A concrete FPrimeStrip over PUnit has a non-descending
   Pi-action: Pi = PUnit x MulAut (Multiplicative (ZMod 3)), G = PUnit,
   proj = fst, and the action is snd (the tautological action of the
   automorphism kernel).  It has no compatible G-action.  A twin FPrimeStrip
   has the same DPrimeStrip and the same value monoid, but the trivial
   Pi-action, and it does have a compatible G-action.  For this concrete pair
   the degree is also identical (sameDegree).  Therefore the action is not
   determined by the D-prime-strip, the value monoid and the degree: it is an
   additional source datum.

## Exact first missing

For the paper's abstract dagger-F_v the first missing is the source-level
descent datum: the Pi-action on the value monoid must be known to factor
through the mono-analytic projection, equivalently the source supplies a
G-action whose pullback along proj is the Pi-action.  The equivalence
R1AbstractActionOnDaggerFMissing_iff_sourceCondition makes this exact, and
no_uniform_construction proves that it is not a consequence of the
FPrimeStrip interface.  For the local actual strip the datum is present and
is the actual Krull action; for the abstract paper strip it must come from the
source construction, not from Definition 3.1 data.

No sorry, axiom, True/PUnit slot (PUnit occurs only as the one-point place
index or as the trivial group in the counterexample, never as a witness for a
missing action), empty type, arbitrary inhabitant, or vacuous Nonempty gate is
used.  The only Classical.choice is the choice of a preimage under the
surjection F.proj v in the construction from a proof of descent; uniqueness
proves that the resulting action is independent of that choice.

## Source locations

* IUT III, Definition 1.1, (i), text l.1259-1351 (the G_v(dagger-Pi_v)-action
  on the ind-topological field and the functoriality in the F-prime-strip).
* IUT III, Definition 1.1, (iii), l.1503-1521 (log(dagger-F_v) with its
  natural G_v(dagger-Pi_v)-action).
* IUT I, Definition 5.2 (F-prime-strip data: Pi, G, surjective projection,
  Pi-action on the value monoid, degree).
* S1962, localAbstractGvAction and R1AbstractActionOnDaggerFMissing.
-/

noncomputable section

open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S1962R1AbstractActionActual

namespace LeanFormal.IUT.XiFPaper.S1976AbstractDaggerFActionActual

/-! ## 0. The descent condition -/

variable {V : Type} (F : FPrimeStrip.{0, 0, 0} V) (v : V)

/-- The Pi-action on the value monoid is constant on the fibres of the
mono-analytic projection.  This is exactly the condition for the action to
descend to the quotient group G. -/
def PiActionDescends : Prop :=
  ∀ a b : F.Pi v, F.proj v a = F.proj v b → F.action v a = F.action v b

theorem piActionDescends_iff :
    PiActionDescends F v ↔
      ∀ a b : F.Pi v, F.proj v a = F.proj v b → F.action v a = F.action v b :=
  Iff.rfl

/-- If the projection is injective, the action descends automatically. -/
theorem piActionDescends_of_injective
    (h : Function.Injective (F.proj v)) : PiActionDescends F v := by
  intro a b hab
  rw [h hab]

/-- A trivial action descends automatically. -/
theorem piActionDescends_of_action_one
    (h : ∀ a : F.Pi v, F.action v a = 1) : PiActionDescends F v := by
  intro a b _
  rw [h a, h b]

/-! ## 1. Constructing the G-action from descent -/

/-- The value of the descended action at g: act by any preimage of g under the
surjection F.proj v. -/
noncomputable def actionOfDescends (h : PiActionDescends F v) :
    F.G v →* MulAut (F.Mon v) where
  toFun g := F.action v (Classical.choose (F.proj_surjective v g))
  map_one' := by
    have hh := h (Classical.choose (F.proj_surjective v 1)) 1 (by
      rw [Classical.choose_spec (F.proj_surjective v 1), map_one])
    simpa using hh
  map_mul' g h' := by
    have hh := h
      (Classical.choose (F.proj_surjective v (g * h')))
      (Classical.choose (F.proj_surjective v g) *
        Classical.choose (F.proj_surjective v h')) (by
      rw [Classical.choose_spec (F.proj_surjective v (g * h')), map_mul,
        Classical.choose_spec (F.proj_surjective v g),
        Classical.choose_spec (F.proj_surjective v h')])
    simpa [map_mul] using hh

theorem actionOfDescends_apply (h : PiActionDescends F v) (g : F.G v) :
    actionOfDescends F v h g =
      F.action v (Classical.choose (F.proj_surjective v g)) := rfl

/-- The compatible G-action constructed from a proof of descent. -/
noncomputable def abstractGvActionOfDescends (h : PiActionDescends F v) :
    AbstractGvActionOnFPrimeStrip F v where
  action := actionOfDescends F v h
  compatible_proj := fun π => by
    have hh := h (Classical.choose (F.proj_surjective v (F.proj v π))) π (by
      rw [Classical.choose_spec (F.proj_surjective v (F.proj v π))])
    simpa [actionOfDescends] using hh

/-- **Characterization of the abstract G-action interface.**  A compatible
G-action exists exactly when the Pi-action descends along the projection. -/
theorem R1AbstractActionOnDaggerFMissing_iff_descends :
    R1AbstractActionOnDaggerFMissing F v ↔ PiActionDescends F v := by
  constructor
  · rintro ⟨A⟩ a b hab
    rw [← A.compatible_proj a, ← A.compatible_proj b, hab]
  · intro h
    exact ⟨abstractGvActionOfDescends F v h⟩

/-- Restatement in terms of Nonempty of the action structure itself. -/
theorem nonempty_abstractGvAction_iff_descends :
    Nonempty (AbstractGvActionOnFPrimeStrip F v) ↔ PiActionDescends F v :=
  R1AbstractActionOnDaggerFMissing_iff_descends F v

/-! ## 2. Uniqueness and the section formula -/

/-- A compatible G-action is unique.  Consequently the construction from
descent is independent of the chosen preimages. -/
theorem abstractGvAction_unique
    (A B : AbstractGvActionOnFPrimeStrip F v) : A = B := by
  cases A with
  | mk actionA compatA =>
  cases B with
  | mk actionB compatB =>
  congr 1
  apply MonoidHom.ext
  intro g
  obtain ⟨π, rfl⟩ := F.proj_surjective v g
  rw [compatA π, compatB π]

theorem abstractGvAction_subsingleton :
    Subsingleton (AbstractGvActionOnFPrimeStrip F v) :=
  ⟨abstractGvAction_unique F v⟩

/-- The formula of a compatible action on any preimage. -/
theorem abstractGvAction_apply_eq
    (A : AbstractGvActionOnFPrimeStrip F v) {g : F.G v} {π : F.Pi v}
    (h : F.proj v π = g) : A.action g = F.action v π := by
  rw [← h, A.compatible_proj]

/-- The formula of a compatible action along a section of the projection. -/
theorem abstractGvAction_apply_section
    (A : AbstractGvActionOnFPrimeStrip F v) (s : F.G v → F.Pi v)
    (hs : ∀ g, F.proj v (s g) = g) (g : F.G v) :
    A.action g = F.action v (s g) := by
  have h := A.compatible_proj (s g)
  rwa [hs g] at h

/-- The action constructed from descent is the unique compatible action. -/
theorem abstractGvActionOfDescends_unique
    (h : PiActionDescends F v) (A : AbstractGvActionOnFPrimeStrip F v) :
    abstractGvActionOfDescends F v h = A :=
  abstractGvAction_unique F v _ _

/-- The construction from descent agrees with the action formula on every
section of the projection, not only on the chosen preimages. -/
theorem abstractGvActionOfDescends_apply_section
    (h : PiActionDescends F v) (s : F.G v → F.Pi v)
    (hs : ∀ g, F.proj v (s g) = g) (g : F.G v) :
    (abstractGvActionOfDescends F v h).action g = F.action v (s g) :=
  abstractGvAction_apply_section F v _ s hs g

/-! ## 3. Transport along a prime-strip equivalence -/

section Transport

variable {F F' : FPrimeStrip.{0, 0, 0} V} (v : V)

/-- Conjugate a G-action on F' by an FPrimeStripEquiv to obtain a G-action on
F at the same place. -/
def transportMulAut (φ : FPrimeStripEquiv F F')
    (A : AbstractGvActionOnFPrimeStrip F' v) (g : F.G v) : MulAut (F.Mon v) :=
  (φ.isoMon v).trans ((A.action (φ.isoG v g)).trans (φ.isoMon v).symm)

/-- The conjugated action as a monoid homomorphism. -/
def transportAction (φ : FPrimeStripEquiv F F')
    (A : AbstractGvActionOnFPrimeStrip F' v) : F.G v →* MulAut (F.Mon v) where
  toFun := transportMulAut v φ A
  map_one' := by
    apply MulEquiv.ext
    intro x
    simp [transportMulAut, MulEquiv.trans_apply, A.action.map_one]
  map_mul' g h := by
    apply MulEquiv.ext
    intro x
    simp [transportMulAut, MulEquiv.trans_apply, A.action.map_mul]

/-- Transport a compatible G-action across a prime-strip equivalence. -/
def transportAbstractGvAction (φ : FPrimeStripEquiv F F')
    (A : AbstractGvActionOnFPrimeStrip F' v) :
    AbstractGvActionOnFPrimeStrip F v where
  action := transportAction v φ A
  compatible_proj := fun π => by
    apply MulEquiv.ext
    intro x
    change (φ.isoMon v).symm
      (A.action (φ.isoG v (F.proj v π)) ((φ.isoMon v) x)) =
        F.action v π x
    rw [show A.action (φ.isoG v (F.proj v π)) =
      F'.action v (φ.isoPi v π) from by
        rw [← A.compatible_proj (φ.isoPi v π), φ.compatProj_apply v]]
    rw [← φ.compatAction v π x, MulEquiv.symm_apply_apply]

/-- Existence of a compatible G-action is invariant under FPrimeStripEquiv. -/
theorem nonempty_transport_iff (φ : FPrimeStripEquiv F F') :
    Nonempty (AbstractGvActionOnFPrimeStrip F v) ↔
      Nonempty (AbstractGvActionOnFPrimeStrip F' v) := by
  constructor
  · rintro ⟨A⟩
    exact ⟨transportAbstractGvAction v (FPrimeStripEquiv.symm φ) A⟩
  · rintro ⟨A⟩
    exact ⟨transportAbstractGvAction v φ A⟩

/-- The missing proposition is invariant under FPrimeStripEquiv. -/
theorem R1AbstractActionOnDaggerFMissing_transport_iff
    (φ : FPrimeStripEquiv F F') :
    R1AbstractActionOnDaggerFMissing F v ↔
      R1AbstractActionOnDaggerFMissing F' v :=
  nonempty_transport_iff v φ

end Transport

/-! ## 4. The local actual model and the comparison route -/

section LocalActual

open LeanFormal.IUT.XiFPaper.OneColumnFinitePrimePlaceActual

variable (v : FinitePrimePlace 2 7)

/-- The local actual F-prime-strip has proj = id, so its actual Krull
Pi-action descends to a G-action. -/
theorem localFPrimeStrip_descends :
    PiActionDescends (S1962R1AbstractActionActual.localFPrimeStrip v) PUnit.unit := by
  intro a b hab
  change a = b at hab
  rw [hab]

/-- The actual local compatible G-action: the actual Krull action itself. -/
noncomputable def localGvActionOfDescends :
    AbstractGvActionOnFPrimeStrip (S1962R1AbstractActionActual.localFPrimeStrip v) PUnit.unit where
  action := (S1962R1AbstractActionActual.localFPrimeStrip v).action PUnit.unit
  compatible_proj := fun _ => rfl

/-- The descent construction returns exactly the explicit actual Krull action
(not an arbitrary preimage choice). -/
theorem localGvActionOfDescends_eq_generic :
    localGvActionOfDescends v =
      abstractGvActionOfDescends (S1962R1AbstractActionActual.localFPrimeStrip v) PUnit.unit
        (localFPrimeStrip_descends v) :=
  abstractGvAction_unique _ _ _ _

/-- The local actual action is S1962's localAbstractGvAction. -/
theorem localGvActionOfDescends_eq :
    localGvActionOfDescends v = S1962R1AbstractActionActual.localAbstractGvAction v :=
  abstractGvAction_unique _ _ _ _

/-- The local actual action is the actual Krull action on the ind integral
monoid. -/
theorem localGvAction_action :
    (localGvActionOfDescends v).action =
      (S1962R1AbstractActionActual.localFPrimeStrip v).action PUnit.unit := rfl

/-- The local actual model inhabits the abstract interface. -/
theorem localGvAction_missing :
    R1AbstractActionOnDaggerFMissing (S1962R1AbstractActionActual.localFPrimeStrip v) PUnit.unit :=
  S1962R1AbstractActionActual.localAbstractGvAction_inhabited v

/-- A comparison of an abstract one-place F-prime-strip with the local actual
F-prime-strip: a prime-strip equivalence to localFPrimeStrip v. -/
structure DaggerFComparison (F : FPrimeStrip.{0, 0, 0} PUnit)
    (v : FinitePrimePlace 2 7) where
  stripEquiv : FPrimeStripEquiv F (S1962R1AbstractActionActual.localFPrimeStrip v)

namespace DaggerFComparison

variable {F : FPrimeStrip.{0, 0, 0} PUnit} {v : FinitePrimePlace 2 7}

/-- Transport the actual local Krull action to the abstract strip along a
comparison. -/
noncomputable def toGvAction (C : DaggerFComparison F v) :
    AbstractGvActionOnFPrimeStrip F PUnit.unit :=
  transportAbstractGvAction PUnit.unit C.stripEquiv (S1962R1AbstractActionActual.localAbstractGvAction v)

/-- A comparison with the local actual strip constructs the abstract
G-action. -/
theorem missing (C : DaggerFComparison F v) :
    R1AbstractActionOnDaggerFMissing F PUnit.unit :=
  ⟨C.toGvAction⟩

/-- A comparison with the local actual strip implies descent. -/
theorem descends (C : DaggerFComparison F v) :
    PiActionDescends F PUnit.unit :=
  (R1AbstractActionOnDaggerFMissing_iff_descends F PUnit.unit).mp C.missing

end DaggerFComparison

/-- The reflexivity comparison of the local actual strip with itself. -/
noncomputable def localComparisonRefl (v : FinitePrimePlace 2 7) :
    DaggerFComparison (S1962R1AbstractActionActual.localFPrimeStrip v) v where
  stripEquiv := FPrimeStripEquiv.refl (S1962R1AbstractActionActual.localFPrimeStrip v)

/-- The reflexivity comparison transports the local actual action to the same
local actual action. -/
theorem localComparisonRefl_toGvAction (v : FinitePrimePlace 2 7) :
    (localComparisonRefl v).toGvAction = S1962R1AbstractActionActual.localAbstractGvAction v :=
  abstractGvAction_unique _ _ _ _

end LocalActual

/-! ## 5. Non-derivability: a strip with no compatible G-action -/

section Counterexample

/-- The nontrivial automorphism of the multiplicative group Z/3 given by
inversion. -/
def zmod3InvAut : MulAut (Multiplicative (ZMod 3)) where
  toFun x := x⁻¹
  invFun x := x⁻¹
  left_inv x := inv_inv x
  right_inv x := inv_inv x
  map_mul' x y := by
    rw [mul_inv_rev, mul_comm]

theorem zmod3InvAut_ne_one : zmod3InvAut ≠ 1 := by
  intro h
  have hx := congrArg (fun e : MulAut (Multiplicative (ZMod 3)) =>
    e (Multiplicative.ofAdd (1 : ZMod 3))) h
  have hx' := congrArg Multiplicative.toAdd hx
  simp [zmod3InvAut] at hx'
  exact (by decide : (-1 : ZMod 3) ≠ 1) hx'

/-- The value monoid of the counterexample. -/
abbrev CexMon : Type := Multiplicative (ZMod 3)

/-- The kernel of the projection in the counterexample. -/
abbrev CexKernel : Type := MulAut CexMon

/-- The projection PUnit x MulAut CexMon -> PUnit is surjective. -/
def projCommon : PUnit × CexKernel →* PUnit :=
  MonoidHom.fst PUnit CexKernel

theorem projCommon_surjective : Function.Surjective projCommon :=
  fun g => ⟨(g, 1), rfl⟩

/-- The non-descending Pi-action: the second projection, i.e. the
tautological action of the automorphism kernel. -/
def actionNontrivial : PUnit × CexKernel →* MulAut CexMon :=
  MonoidHom.snd PUnit CexKernel

/-- The trivial Pi-action on the same kernel. -/
def actionTrivialCommon : PUnit × CexKernel →* MulAut CexMon where
  toFun _ := 1
  map_one' := rfl
  map_mul' := by intro a b; simp

/-- The trivial degree on the counterexample value monoid. -/
def degreeTrivial : CexMon →* Multiplicative Real where
  toFun _ := 1
  map_one' := rfl
  map_mul' := by intro a b; simp

/-- A concrete F-prime-strip with the same D-prime-strip data as the twin but
with the automorphism kernel acting by its defining automorphisms (the
non-descending action). -/
noncomputable def nondescendingFPrimeStrip : FPrimeStrip.{0, 0, 0} PUnit where
  Pi := fun _ => PUnit × CexKernel
  groupPi := fun _ => inferInstance
  G := fun _ => PUnit
  groupG := fun _ => inferInstance
  proj := fun _ => projCommon
  proj_surjective := fun _ => projCommon_surjective
  Mon := fun _ => CexMon
  commMonoidMon := fun _ => inferInstance
  action := fun _ => actionNontrivial
  degree := fun _ => degreeTrivial

/-- The twin with the trivial Pi-action. -/
noncomputable def descendingTwinFPrimeStrip : FPrimeStrip.{0, 0, 0} PUnit where
  Pi := fun _ => PUnit × CexKernel
  groupPi := fun _ => inferInstance
  G := fun _ => PUnit
  groupG := fun _ => inferInstance
  proj := fun _ => projCommon
  proj_surjective := fun _ => projCommon_surjective
  Mon := fun _ => CexMon
  commMonoidMon := fun _ => inferInstance
  action := fun _ => actionTrivialCommon
  degree := fun _ => degreeTrivial

theorem nondescendingFPrimeStrip_action_kernel :
    nondescendingFPrimeStrip.action PUnit.unit (PUnit.unit, zmod3InvAut) =
      zmod3InvAut := rfl

/-- The counterexample action is not constant on the fibre of the projection:
the identity and the inversion automorphism have the same projection but
different actions. -/
theorem nondescendingFPrimeStrip_not_descends :
    ¬ PiActionDescends nondescendingFPrimeStrip PUnit.unit := by
  intro h
  have hσ := h (PUnit.unit, 1) (PUnit.unit, zmod3InvAut) rfl
  rw [nondescendingFPrimeStrip_action_kernel] at hσ
  exact zmod3InvAut_ne_one hσ.symm

/-- The non-descending strip has no compatible G-action. -/
theorem nondescendingFPrimeStrip_noAction :
    ¬ R1AbstractActionOnDaggerFMissing nondescendingFPrimeStrip PUnit.unit := by
  intro h
  exact nondescendingFPrimeStrip_not_descends
    ((R1AbstractActionOnDaggerFMissing_iff_descends
      nondescendingFPrimeStrip PUnit.unit).mp h)

/-- The twin with the trivial action descends. -/
theorem descendingTwinFPrimeStrip_descends :
    PiActionDescends descendingTwinFPrimeStrip PUnit.unit := by
  intro a b _
  rfl

/-- The twin with the trivial action has a compatible G-action. -/
theorem descendingTwinFPrimeStrip_hasAction :
    R1AbstractActionOnDaggerFMissing descendingTwinFPrimeStrip PUnit.unit :=
  (R1AbstractActionOnDaggerFMissing_iff_descends
    descendingTwinFPrimeStrip PUnit.unit).mpr
      descendingTwinFPrimeStrip_descends

theorem sameDPrimeStrip :
    nondescendingFPrimeStrip.toDPrimeStrip =
      descendingTwinFPrimeStrip.toDPrimeStrip := rfl

theorem sameMon :
    nondescendingFPrimeStrip.Mon = descendingTwinFPrimeStrip.Mon := rfl

theorem sameDegree :
    nondescendingFPrimeStrip.degree = descendingTwinFPrimeStrip.degree := rfl

/-- **The action is not determined by the D-prime-strip and the value
monoid.**  Two F-prime-strips with identical D-prime-strip data and identical
value monoid differ in whether a compatible G-action exists; for this concrete
pair the degree is also identical (sameDegree).  Hence the G-action is an
additional source datum. -/
theorem action_not_determined_by_DPrimeStrip :
    ∃ F G : FPrimeStrip.{0, 0, 0} PUnit,
      F.toDPrimeStrip = G.toDPrimeStrip ∧
      F.Mon = G.Mon ∧
      R1AbstractActionOnDaggerFMissing F PUnit.unit ∧
      ¬ R1AbstractActionOnDaggerFMissing G PUnit.unit := by
  refine ⟨descendingTwinFPrimeStrip, nondescendingFPrimeStrip,
    ?_, ?_, ?_, ?_⟩
  · exact sameDPrimeStrip.symm
  · exact sameMon.symm
  · exact descendingTwinFPrimeStrip_hasAction
  · exact nondescendingFPrimeStrip_noAction

/-- The two strips above are not related by any FPrimeStripEquiv: an
equivalence would force the non-descending kernel action to be trivial. -/
theorem no_equiv_nondescending_descendingTwin :
    ¬ Nonempty (FPrimeStripEquiv
      nondescendingFPrimeStrip descendingTwinFPrimeStrip) := by
  rintro ⟨φ⟩
  have h : ∀ (π : PUnit × CexKernel) (x : CexMon),
      nondescendingFPrimeStrip.action PUnit.unit π x = x := by
    intro π x
    apply (φ.isoMon PUnit.unit).injective
    rw [φ.compatAction]
    change (1 : MulAut CexMon) ((φ.isoMon PUnit.unit) x) =
      (φ.isoMon PUnit.unit) x
    rfl
  have hx := h (PUnit.unit, zmod3InvAut)
    (Multiplicative.ofAdd (1 : ZMod 3))
  change zmod3InvAut (Multiplicative.ofAdd (1 : ZMod 3)) =
    Multiplicative.ofAdd (1 : ZMod 3) at hx
  have hx' := congrArg Multiplicative.toAdd hx
  simp [zmod3InvAut] at hx'
  exact (by decide : (-1 : ZMod 3) ≠ 1) hx'

end Counterexample

/-! ## 6. The exact first missing -/

/-- The exact source condition for the abstract dagger-F_v G-action: the
Pi-action on the value monoid descends along the mono-analytic projection.
This is the first missing datum for the paper's abstract strip when only the
FPrimeStrip interface is available. -/
def DaggerFActionSourceCondition (F : FPrimeStrip.{0, 0, 0} V) (v : V) : Prop :=
  PiActionDescends F v

/-- The abstract-action interface is exactly the source condition. -/
theorem R1AbstractActionOnDaggerFMissing_iff_sourceCondition :
    R1AbstractActionOnDaggerFMissing F v ↔ DaggerFActionSourceCondition F v :=
  R1AbstractActionOnDaggerFMissing_iff_descends F v

/-- The local actual strip satisfies the source condition. -/
theorem localActual_sourceCondition (v : FinitePrimePlace 2 7) :
    DaggerFActionSourceCondition (S1962R1AbstractActionActual.localFPrimeStrip v) PUnit.unit := by
  exact (R1AbstractActionOnDaggerFMissing_iff_sourceCondition
    (S1962R1AbstractActionActual.localFPrimeStrip v) PUnit.unit).mp (localGvAction_missing v)

/-- The source condition is exactly the existence of a source-level
G-action whose pullback along the projection is the Pi-action. -/
theorem sourceCondition_iff_exists_sourceAction :
    DaggerFActionSourceCondition F v ↔
      ∃ A : F.G v →* MulAut (F.Mon v),
        A.comp (F.proj v) = F.action v := by
  constructor
  · intro h
    refine ⟨(abstractGvActionOfDescends F v h).action, ?_⟩
    apply MonoidHom.ext
    intro π
    exact (abstractGvActionOfDescends F v h).compatible_proj π
  · rintro ⟨A, hA⟩ a b hab
    have h : ∀ π : F.Pi v, A (F.proj v π) = F.action v π := by
      intro π
      have hπ := DFunLike.congr_fun hA π
      simpa using hπ
    rw [← h a, ← h b, hab]

/-- **No uniform construction from FPrimeStrip data.**  There is no theorem
producing a compatible G-action for every FPrimeStrip; the counterexample
refutes it.  The paper's abstract dagger-F therefore needs the source-level
descent datum. -/
theorem no_uniform_construction :
    ¬ ∀ F : FPrimeStrip.{0, 0, 0} PUnit,
      R1AbstractActionOnDaggerFMissing F PUnit.unit := by
  intro h
  exact nondescendingFPrimeStrip_noAction (h nondescendingFPrimeStrip)

/-- The same no-go statement for an arbitrary place index type. -/
theorem no_uniform_construction_any_index :
    ¬ ∀ (V : Type) (F : FPrimeStrip.{0, 0, 0} V) (v : V),
      R1AbstractActionOnDaggerFMissing F v := by
  intro h
  exact nondescendingFPrimeStrip_noAction
    (h PUnit nondescendingFPrimeStrip PUnit.unit)

/-! ## 7. Axiom probes -/

#print axioms R1AbstractActionOnDaggerFMissing_iff_descends
#print axioms abstractGvAction_unique
#print axioms abstractGvAction_apply_section
#print axioms abstractGvActionOfDescends_apply_section
#print axioms nonempty_transport_iff
#print axioms localFPrimeStrip_descends
#print axioms localGvActionOfDescends_eq
#print axioms DaggerFComparison.missing
#print axioms nondescendingFPrimeStrip_not_descends
#print axioms nondescendingFPrimeStrip_noAction
#print axioms action_not_determined_by_DPrimeStrip
#print axioms no_equiv_nondescending_descendingTwin
#print axioms R1AbstractActionOnDaggerFMissing_iff_sourceCondition
#print axioms sourceCondition_iff_exists_sourceAction
#print axioms no_uniform_construction
#print axioms no_uniform_construction_any_index

end LeanFormal.IUT.XiFPaper.S1976AbstractDaggerFActionActual

end