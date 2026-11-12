# S1741: actual profinite fundamental group from a fiber functor — Aut(F), Action certificates, exact boundary

Date: 2026-11-01

Lean: tmp/sheaf/xif/paper/S1741AutFiberActual.lean

EXIT=0

SHA256 (source): 32AEB3FD13A8890F3922FC7D11FED9FD3E04018A60D03D1DFFF64FE1F4334D69

Source size: 13108 bytes.

olean: D:/lean/.lake/build/lib/lean/tmp/sheaf/xif/paper/S1741AutFiberActual.olean (328296 bytes)

SHA256 (olean): 493445668C1035D9D8C5EA53D76206EFD26354677AAC3EACA453A6206C5A3029

No `sorry`, no `admit`, no new axiom, no `Shrink`/`ULift`/`PUnit`, no fake group or action.

## Actual constructions

* `S1741.FiberFundamentalGroupCertificate` is a structure with exactly the
  shape of the `isFundamentalGroup` field of `EtaleFundamentalGroup` /
  `OrbicurveEtaleFundamentalGroup`: a `ProfiniteGrp`, its action on every fiber
  of a fiber functor, and a proof of `PreGaloisCategory.IsFundamentalGroup`.
  `FiberFundamentalGroupCertificate.certified` projects the proof.

* General Galois category and fiber functor (unconditional):
  for `C : Type u`, `[Category.{v} C]`, `F : C ⥤ FintypeCat.{w}`,
  `autProfiniteGrp F := ProfiniteGrp.of (Aut F) : ProfiniteGrp.{max u w}`.
  This is Mathlib's canonical compact, Hausdorff, totally-disconnected
  topology on `Aut F`.  `autProfiniteGrp_isFundamentalGroup` is Mathlib's
  instance `IsFundamentalGroup F (Aut F)` restated for the bundled group, and
  `autCertificate` packages the evaluation action and the proof.  There is no
  missing datum in this direction; the proof uses no continuity hypothesis
  beyond Mathlib's canonical topology.

* `Action FintypeCat.{0} G`, automorphism group, for every group `G`:
  `actionForget_aut_isFundamentalGroup :
    IsFundamentalGroup (actionForget G) (Aut (actionForget G))`.
  `actionAutProfiniteGrp : ProfiniteGrp.{1}` is the bundled automorphism group
  (the category `Action FintypeCat.{0} G` is Type 1), and
  `actionAutCertificate` packages the certificate.  No finiteness of `G` is
  needed for this Aut-based statement.

* `Action FintypeCat.{0} G`, the acting group itself, for finite `G` with the
  discrete topology:
  `actionForget_isFundamentalGroup :
    IsFundamentalGroup (actionForget G) G`.
  The action is the real `Action.instMulAction`; naturality is the `comm`
  field of an `Action.Hom`; transitivity on Galois objects is
  `FintypeCat.Action.pretransitive_of_isConnected`; triviality of the action is
  tested on the regular `G`-set `Action.FintypeCat.ofMulAction G (FintypeCat.of G)`.
  `actionForgetToAutMulEquiv : G ≃* Aut (actionForget G)`,
  `actionForgetToAutHomeo : G ≃ₜ Aut (actionForget G)`, and
  `actionForgetContinuousMulEquiv : G ≃ₜ* Aut (actionForget G)` give the
  canonical comparison.  `actionCertificate` bundles the certificate with
  `ProfiniteGrp.of G`; `finiteGroupProfinite` and `finiteActionCertificate`
  choose the canonical discrete topology so the consumer does not have to
  provide a topology.

* Transport to an external abstract group:
  `isFundamentalGroup_of_continuousMulEquiv
    (e : G ≃ₜ* Aut F)
    (hact : ∀ g X x, (e g).hom.app X x = g • x) :
    IsFundamentalGroup F G`.
  This is a real proof; `e` and `hact` are the exact comparison data.  It is
  the interface for a Type 0 group such as `Iut.AbsoluteGaloisProfinite F` when
  the paper-side Galois correspondence supplies a continuous isomorphism to the
  Type 1 automorphism group of a Type 1 cover category.

## Universe observations (important for S1737)

* `Aut F` for `C : Type u` and `F : C ⥤ FintypeCat.{w}` lives in
  `Type (max u w)`; it does not depend on the hom universe `v`.  Therefore
  `autProfiniteGrp F : ProfiniteGrp.{max u w}` applies to categories with
  `Category.{0,1}`, not only to `Category.{u,u}`.

* `Action FintypeCat.{0} G` is a Type 1 category with `Category.{0,1}`.
  Hence `Aut (actionForget G) : Type 1` and
  `actionAutProfiniteGrp G : ProfiniteGrp.{1}`.

* `Iut.OrbicurveFiniteEtaleCover X` is Type 1.  Even after S1728 supplies a
  small `Category.{0}` carrier, a fiber functor on that category has
  `Aut fiber : Type 1`, so `autProfiniteGrp fiber : ProfiniteGrp.{1}`.
  S1737's `OrbicurveEtaleFundamentalGroup` / `S1737OrbicurveFields` fix
  `G : ProfiniteGrp.{0}`.  Therefore `autCertificate` for the orbicurve fiber
  functor cannot fill that Type 0 field directly.

## Exact missing / consumer guidance for S1737

* If S1737 fills the orbicurve `isFundamentalGroup` field with the Type 0 group
  `G = Iut.AbsoluteGaloisProfinite F'`, the precise missing data are:
  `e : Iut.AbsoluteGaloisProfinite F' ≃ₜ* Aut fiber` and
  `hact : ∀ g X x, (e g).hom.app X x = g • x`.
  Then `S1741.isFundamentalGroup_of_continuousMulEquiv e hact` gives
  `IsFundamentalGroup fiber (Iut.AbsoluteGaloisProfinite F')`.  Constructing
  `e` and `hact` is exactly the Galois-correspondence/fiber-identification
  work that S1737 lists as missing; this file does not fake it.

* The alternative is to fill the field with `Aut fiber` itself.  This is
  unconditional and real, but for the Type 1 orbicurve cover category it lives
  in `ProfiniteGrp.{1}`, so S1737's structure would need a group-universe or
  small-model adjustment to accept it.

* For the plain full action category with an infinite profinite `G`,
  `IsFundamentalGroup (Action.forget FintypeCat G) G` is not automatic.  S1737
  proves it is equivalent to "every finite-index subgroup of `G` is open"
  (`S1737AllFiniteActionsContinuous_iff_everyFiniteIndexOpen` and
  `S1737ActionForget_isFundamentalGroup_iff_allContinuous`).  This file does
  not claim the general literal statement; its `actionForget_isFundamentalGroup`
  is the finite/discrete discharge, and the Aut-based statement is
  unconditional.

* For the continuous-action category `ContAction FintypeCat G`, S1737 already
  uses the project's `Iut.continuousAction_isFundamentalGroup`; that Type 0
  certificate is the correct route for `G` itself and needs no change.

## Axiom audit

`#print axioms` on `autCertificate`, `actionCertificate`,
`finiteActionCertificate`, `isFundamentalGroup_of_continuousMulEquiv` and the
individual instances reports only:

`propext, Classical.choice, Quot.sound`.

There is no `sorryAx` and no other axiom in the checked declarations.

## Verification commands

`lake env lean tmp/sheaf/xif/paper/S1741AutFiberActual.lean` — EXIT=0.

`lake env lean -o .lake/build/lib/lean/tmp/sheaf/xif/paper/S1741AutFiberActual.olean tmp/sheaf/xif/paper/S1741AutFiberActual.lean` — EXIT=0.

`lake env lean tmp/sheaf/xif/paper/S1741Check.lean` — EXIT=0; checker for
`#check` and `#print axioms`.
