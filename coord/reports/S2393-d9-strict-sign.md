# S2393: strict sign route — reduced to Iso.refl mapComp' identity

Date: 2026-11-02.

Unfolding S2152Q = S2152PFunctor.toPseudofunctor' exposes the strict pseudofunctor
whose mapComp is Iso.refl. The sign projection goal becomes

  ↑((mapComp' ...).hom.toNatTrans.app M
      ≫ (S1971PrecompFunctor ...).toCatHom.toFunctor.map x
      ≫ (mapComp' ...).inv.toNatTrans.app N) = ↑x

with mapComp' built from Iso.refl coherences.

Missing: show the Iso.refl mapComp' app component acts as the identity functor on
the action category, so its sign projection is identity. Then S1971PrecompFunctor_map_val
gives the middle factor ↑x and the goal closes.

Direct simp produced a large unfolding and did not discharge the mapComp' component.

Status: strict route reduced, sign projection MISSING; Psub NatIso MISSING; IsStack not claimed.

Verification:
- EXIT=0
- SHA256: 4fd6e5af73cb50587b43b152fc3b83171a42107eea1c8f5197d19281038f6eef
- olean: D:\lean\.lake\build\lib\lean\tmp\sheaf\xif\paper\S2393StrictSignActual.olean, size 3072
- axioms: propext, Classical.choice, Quot.sound.