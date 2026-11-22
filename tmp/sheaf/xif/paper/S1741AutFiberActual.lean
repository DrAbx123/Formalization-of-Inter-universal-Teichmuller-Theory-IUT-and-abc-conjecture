/-
Copyright (c) 2026 IUT Lean formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: IUT Lean formalization contributors
-/
import Mathlib.CategoryTheory.Galois.Action
import Mathlib.CategoryTheory.Galois.IsFundamentalgroup
import Mathlib.Topology.Algebra.Category.ProfiniteGrp.Basic

/-!
# S1741: actual fundamental-group certificates from fiber functors

This file constructs, from Mathlib's Galois-category theory, actual
`PreGaloisCategory.IsFundamentalGroup` certificates together with the profinite
automorphism group `Aut F` of a fiber functor.  Nothing here is a placeholder:
the group is `Aut F` (or the actual group acting on `Action FintypeCat G`), the
action is the evaluation action (or the action recorded by `Action`), and the
`IsFundamentalGroup` field is a proof.

## Main results

* `S1741.FiberFundamentalGroupCertificate` packages exactly the data needed by
  the `isFundamentalGroup` field of a structure such as
  `Iut.Orbicurve.EtaleFundamentalGroup`: a profinite group, its action on every
  fiber, and the `IsFundamentalGroup` proof.

* For a general Galois category `C` and fiber functor `F`, the group `Aut F`
  carries Mathlib's canonical compact totally-disconnected group topology
  (`Mathlib.CategoryTheory.Galois.Topology`), hence
  `autProfiniteGrp F : ProfiniteGrp` is an actual profinite group, and
  `autProfiniteGrp_isFundamentalGroup` is Mathlib's instance
  `IsFundamentalGroup F (Aut F)`.  There is no missing datum in this direction.

* For `Action FintypeCat.{0} G`, the forgetful functor is a fiber functor for
  every group `G`.  The automorphism group certificate
  `actionForget_aut_isFundamentalGroup` is unconditional in `G`.  When `G` is
  finite and carries the discrete topology, the acting group `G` itself is a
  fundamental group (`actionForget_isFundamentalGroup`), and the canonical
  comparison `G ≃* Aut (forget)` (even a topological-group isomorphism) is
  `actionForgetToAutMulEquiv` / `actionForgetToAutHomeo` /
  `actionForgetContinuousMulEquiv`.

* `isFundamentalGroup_of_continuousMulEquiv` is the precise transport step for
  the case where the paper's fundamental group is *not* definitionally `Aut F`
  (for example `Iut.AbsoluteGaloisProfinite F`): a continuous group isomorphism
  `e : G ≃ₜ* Aut F` together with the action identification
  `(e g).hom.app X x = g • x` yields `IsFundamentalGroup F G`.  These two data
  are the exact missing input in that case; the file does not fabricate them.

## Boundary of the `Action` construction

The plain category `Action FintypeCat G` does not record continuity of the
action.  For a finite `G` the discrete topology makes every action continuous,
so the certificate for `G` itself is complete.  For a general profinite `G` the
correct ambient category is the project's `ContAction FintypeCat G` (whose
objects carry `ContinuousSMul`), as used in
`Iut/Foundations/SourceContinuousAnabelioid.lean`; the transport theorem above
records what is needed to compare such a group with `Aut F`.
-/

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.PreGaloisCategory

namespace S1741

universe u v w g

/-! ## A certificate for the `isFundamentalGroup` field -/

/-- A real certificate for the `isFundamentalGroup` field of a Galois-category
datum: a profinite group, its action on every fiber of the fiber functor, and
the proof that it is a fundamental group for that fiber functor. -/
structure FiberFundamentalGroupCertificate
    (C : Type u) [Category.{v} C] [GaloisCategory C]
    (F : C ⥤ FintypeCat.{w}) [FiberFunctor F] (group : ProfiniteGrp.{g}) where
  /-- The actual action of the group on each fiber. -/
  action : ∀ X : C, MulAction group (F.obj X)
  /-- The certificate that the group is a fundamental group for `F`. -/
  isFundamentalGroup :
    letI (X : C) := action X
    IsFundamentalGroup F group

namespace FiberFundamentalGroupCertificate

variable {C : Type u} [Category.{v} C] [GaloisCategory C]
  {F : C ⥤ FintypeCat.{w}} [FiberFunctor F] {group : ProfiniteGrp.{g}}
  (data : FiberFundamentalGroupCertificate C F group)

/-- The stored field is exactly a proof of `IsFundamentalGroup`. -/
theorem certified :
    letI (X : C) := data.action X
    IsFundamentalGroup F group :=
  data.isFundamentalGroup

end FiberFundamentalGroupCertificate

/-! ## General Galois category and fiber functor: `Aut F` -/

section General

variable {C : Type u} [Category.{v} C] (F : C ⥤ FintypeCat.{w})

/-- The automorphism group of a fiber functor, bundled with Mathlib's canonical
profinite topology (compact, Hausdorff, totally disconnected).  The universe is
`max u w`: `Aut F` depends on the object universe of `C` and on the universe of
the finite types, but not on the hom universe. -/
noncomputable abbrev autProfiniteGrp : ProfiniteGrp.{max u w} :=
  ProfiniteGrp.of (Aut F)

@[simp]
theorem autProfiniteGrp_coe : (autProfiniteGrp F : Type (max u w)) = Aut F :=
  rfl

variable [GaloisCategory C] [FiberFunctor F]

/-- `Aut F`, regarded as the profinite group `autProfiniteGrp F`, acts on the
fibers by evaluation. -/
@[implicit_reducible]
noncomputable def autProfiniteGrpAction (X : C) :
    MulAction (autProfiniteGrp F) (F.obj X) :=
  inferInstanceAs (MulAction (Aut F) (F.obj X))

/-- `Aut F` is a fundamental group for `F`; this is Mathlib's instance, restated
for the bundled profinite group. -/
noncomputable instance autProfiniteGrp_isFundamentalGroup :
    IsFundamentalGroup F (autProfiniteGrp F) :=
  inferInstance

/-- The canonical certificate for a general Galois category and fiber functor:
the group is `Aut F`, the action is evaluation, and the field is Mathlib's
`IsFundamentalGroup F (Aut F)` instance. -/
noncomputable def autCertificate :
    FiberFundamentalGroupCertificate C F (autProfiniteGrp F) where
  action _ := inferInstance
  isFundamentalGroup := inferInstance

end General

/-! ## Transport to an arbitrary abstract fundamental group -/

section Transport

variable {C : Type u} [Category.{v} C] [GaloisCategory C]
variable {F : C ⥤ FintypeCat.{w}} [FiberFunctor F]
variable {G : Type g} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
variable [∀ X : C, MulAction G (F.obj X)]

/-- If `G` is a compact topological group acting naturally on the fibers of `F`
and is continuously isomorphic to `Aut F` with the actions identified, then `G`
is a fundamental group for `F`.

The hypothesis `hact` is not a definable consequence of the other data: it is
the exact comparison datum needed when the paper's group is not definitionally
`Aut F`. -/
theorem isFundamentalGroup_of_continuousMulEquiv
    (e : G ≃ₜ* Aut F)
    (hact : ∀ (g : G) (X : C) (x : F.obj X), (e g).hom.app X x = g • x) :
    IsFundamentalGroup F G := by
  refine
    { naturality := ?_
      transitive_of_isGalois := ?_
      continuous_smul := ?_
      non_trivial' := ?_ }
  · intro g X Y f x
    calc
      F.map f (g • x) = F.map f ((e g).hom.app X x) := by rw [hact]
      _ = (e g).hom.app Y (F.map f x) := (NatTrans.naturality_apply (e g).hom f x).symm
      _ = g • F.map f x := by rw [hact]
  · intro X hX
    haveI := hX
    haveI : MulAction.IsPretransitive (Aut F) (F.obj X) :=
      FiberFunctor.isPretransitive_of_isConnected F X
    refine ⟨fun x y => ?_⟩
    obtain ⟨σ, hσ⟩ := MulAction.exists_smul_eq (Aut F) x y
    obtain ⟨g, rfl⟩ := e.surjective σ
    have hσ' : (e g).hom.app X x = y := by
      simpa only [mulAction_def] using hσ
    exact ⟨g, by rw [← hact g X x]; exact hσ'⟩
  · intro X
    constructor
    have hcont : Continuous fun p : G × F.obj X => (e p.1) • p.2 :=
      (continuousSMul_aut_fiber F X).continuous_smul.comp
        ((e.continuous_toFun.comp continuous_fst).prodMk continuous_snd)
    convert hcont using 1
    ext p
    exact (hact p.1 X p.2).symm
  · intro g h
    have h' : ∀ (X : C) (x : F.obj X), (e g) • x = x := by
      intro X x
      calc
        (e g) • x = (e g).hom.app X x := rfl
        _ = g • x := hact g X x
        _ = x := h X x
    have hg : e g = 1 := IsFundamentalGroup.non_trivial (F := F) (G := Aut F) (e g) h'
    exact e.injective (by simpa using hg)

end Transport

/-! ## `Action FintypeCat.{0} G`: the forgetful fiber functor -/

/-- The forgetful functor from finite `G`-sets to finite sets. -/
abbrev actionForget (G : Type) [Group G] :
    Action FintypeCat.{0} G ⥤ FintypeCat.{0} :=
  forget₂ (Action FintypeCat.{0} G) FintypeCat.{0}

section Action

variable (G : Type) [Group G]

/-- The actual action of `G` on the fiber of the forgetful functor, i.e. on the
underlying finite set of a finite `G`-set. -/
instance actionForgetMulAction (X : Action FintypeCat.{0} G) :
    MulAction G ((actionForget G).obj X) :=
  Action.instMulAction X

/-- For every group `G`, the automorphism group of the forgetful fiber functor is
a fundamental group.  No finiteness of `G` is needed for this certificate. -/
noncomputable instance actionForget_aut_isFundamentalGroup :
    IsFundamentalGroup (actionForget G) (Aut (actionForget G)) :=
  inferInstance

/-- The automorphism group of the forgetful functor, bundled as a profinite
group.  (The category `Action FintypeCat.{0} G` lives in `Type 1`, so its
automorphism group is a `ProfiniteGrp.{1}`.) -/
noncomputable abbrev actionAutProfiniteGrp : ProfiniteGrp.{1} :=
  ProfiniteGrp.of (Aut (actionForget G))

/-- The bundled automorphism group of the forgetful functor is a fundamental
group for it. -/
noncomputable instance actionAutProfiniteGrp_isFundamentalGroup :
    IsFundamentalGroup (actionForget G) (actionAutProfiniteGrp G) :=
  inferInstance

/-- Certificate for the `Aut`-group of the forgetful functor, valid for every
group `G`. -/
noncomputable def actionAutCertificate :
    FiberFundamentalGroupCertificate (Action FintypeCat.{0} G) (actionForget G)
      (actionAutProfiniteGrp G) where
  action _ := inferInstance
  isFundamentalGroup := inferInstance

end Action

/-! ## `Action FintypeCat.{0} G` for finite `G`: the acting group itself -/

section ActionFinite

variable (G : Type) [Group G] [Finite G] [TopologicalSpace G] [DiscreteTopology G]

/-- For a finite group `G` with the discrete topology, the acting group `G`
itself is a fundamental group for the forgetful fiber functor.  The action is
the real `Action.instMulAction`, and triviality of the action is tested on the
regular `G`-set. -/
noncomputable instance actionForget_isFundamentalGroup :
    IsFundamentalGroup (actionForget G) G where
  naturality g {X Y} f x := by
    exact ConcreteCategory.congr_hom (f.comm g) x
  transitive_of_isGalois X := by
    exact FintypeCat.Action.pretransitive_of_isConnected G X
  continuous_smul X := by
    constructor
    exact continuous_of_discreteTopology
  non_trivial' g h := by
    letI : Fintype G := Fintype.ofFinite G
    let X₀ : Action FintypeCat.{0} G := Action.FintypeCat.ofMulAction G (FintypeCat.of G)
    have hg : g • (1 : FintypeCat.of G) = (1 : FintypeCat.of G) :=
      h X₀ (1 : FintypeCat.of G)
    simpa [actionForgetMulAction, X₀] using hg

/-- The canonical comparison between `G` and the automorphism group of the
forgetful functor, as a group isomorphism. -/
noncomputable def actionForgetToAutMulEquiv : G ≃* Aut (actionForget G) :=
  toAutMulEquiv (actionForget G) G

/-- The comparison is a homeomorphism for the canonical topologies. -/
noncomputable def actionForgetToAutHomeo : G ≃ₜ Aut (actionForget G) :=
  toAutHomeo (actionForget G) G

/-- The comparison bundled as a continuous group isomorphism. -/
noncomputable def actionForgetContinuousMulEquiv : G ≃ₜ* Aut (actionForget G) :=
  ContinuousMulEquiv.mk' (actionForgetToAutHomeo G)
    (fun g h => map_mul (toAut (actionForget G) G) g h)

/-- Certificate for the acting group `G` itself (with an arbitrary discrete
topology on the finite group). -/
noncomputable def actionCertificate :
    FiberFundamentalGroupCertificate (Action FintypeCat.{0} G) (actionForget G)
      (ProfiniteGrp.of G) where
  action := actionForgetMulAction G
  isFundamentalGroup := actionForget_isFundamentalGroup G

end ActionFinite

/-! ## The canonical discrete topology on a finite group -/

section FiniteDiscrete

variable (G : Type) [Group G] [Finite G]

/-- A finite group with the discrete topology, as a profinite group. -/
noncomputable def finiteGroupProfinite : ProfiniteGrp.{0} :=
  letI : TopologicalSpace G := ⊥
  letI : DiscreteTopology G := ⟨rfl⟩
  ProfiniteGrp.of G

@[simp]
theorem finiteGroupProfinite_coe : (finiteGroupProfinite G : Type) = G :=
  rfl

/-- The fully canonical certificate for a finite group: no topology has to be
chosen by the consumer. -/
noncomputable def finiteActionCertificate :
    FiberFundamentalGroupCertificate (Action FintypeCat.{0} G) (actionForget G)
      (finiteGroupProfinite G) := by
  letI : TopologicalSpace G := ⊥
  letI : DiscreteTopology G := ⟨rfl⟩
  exact
    { action := actionForgetMulAction G
      isFundamentalGroup := actionForget_isFundamentalGroup G }

end FiniteDiscrete

end S1741
