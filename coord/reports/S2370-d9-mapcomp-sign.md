# S2370: mapComp' sign value — statement type needs correction

Date: 2026-11-02.

Attempted lemma: ((S2152Q.mapComp' f g h hh).hom.toNatTrans.app M).val = 1. It does not typecheck: the app component is not a SignGroup-labelled action-category morphism in the elaborated type; rfl fails. The correct action-category morphism projection was not found.

Available actual: S1971PrecompFunctor_map_val, S2259QMapPrecomp, S2332Psub.

Status: mapComp' sign lemma NOT TYPECHECKING; sign projection MISSING; Psub NatIso MISSING; IsStack not claimed.

Verification:
- EXIT=0
- SHA256: ce7da107a6893aabd97010efd07d2fe19f4bf51dee8c93d42a837b97acd4920d
- olean: D:\lean\.lake\build\lib\lean\tmp\sheaf\xif\paper\S2370MapCompSignActual.olean, size 3472
- axioms: propext, Classical.choice, Quot.sound.