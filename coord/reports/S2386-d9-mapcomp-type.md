# S2386: mapComp' app is a Cat morphism, not an action-category hom

Date: 2026-11-02.

Exact #check output:

  (Pseudofunctor.mapComp' S2152Q f g h hh).hom.toNatTrans.app M :
    (S2152Q.map h).toFunctor.obj M ⟶ (S2152Q.map f ≫ S2152Q.map g).toFunctor.obj M

Here M is an object of the category S2152Q.obj A. The app component is a
natural-transformation component, i.e. a 1-morphism in Cat (a functor between
action categories), not a SignGroup-labelled action-category morphism.
Therefore the earlier statement ((...app M).val = 1) is ill-typed; .val is
not the sign label.

The correct sign projection must instead use the functor's effect on objects/morphisms,
or the pullHom composite must be reconstructed without passing through this Cat-level app.

Status: mapComp' .val=1 is invalid; sign projection MISSING; Psub NatIso MISSING; IsStack not claimed.

Verification:
- EXIT=0
- SHA256: fd87027a16db91a275b139f246464cb8372b444b44892ef4a14f1fb8932e989e
- olean: D:\lean\.lake\build\lib\lean\tmp\sheaf\xif\paper\S2386MapCompSign2Actual.olean, size 3568
- axioms: propext, Classical.choice, Quot.sound.