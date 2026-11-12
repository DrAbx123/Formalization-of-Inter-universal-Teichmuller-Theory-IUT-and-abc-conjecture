# S2366: Q hom sign projection — reduced to mapComp' coherence value

Date: 2026-11-02. Status: sign projection equality is not proved; the goal is
reduced to the sign value of the mapComp' coherence app M/N. No fake, no IsStack
claim.

## 1. Reduced goal

After unfolding Pseudofunctor.presheafHom.map and
Pseudofunctor.LocallyDiscreteOpToCat.pullHom, the sign projection goal is

  ↑((mapComp' S2152Q (T1.hom).op.toLoc (p.left).op.toLoc (T2.hom).op.toLoc _).hom.toNatTrans.app M
      ≫ (S2152Q.map (p.left).op.toLoc).toFunctor.map x
      ≫ (mapComp' ...).inv.toNatTrans.app N)
    = ↑x

## 2. What is available

- S1971PrecompFunctor_map_val: ((S1971PrecompFunctor f).map φ).val = φ.val;
- S2259QMapPrecomp: (S2152Q.map f).toFunctor = S1971PrecompFunctor f.

So the middle factor's sign value is x.val.  The remaining issue is the sign
value of the mapComp' coherence app M/N (eqToIso coherences of
Functor.toPseudofunctor'), which was not reduced to 1.

## 3. Exact remaining goal

Prove for every f g h (with composability) and object M:

  ((S2152Q.mapComp' f g h ...).hom.toNatTrans.app M).val = 1

(or both hom/inv coherence app values are 1).  Then the sign projection follows
from associativity/unit laws in the action category.

## 4. Status

| Item | Status |
|---|---|
| pullHom goal reduction | DONE |
| middle factor sign value | available via S2259 + S1971PrecompFunctor_map_val |
| mapComp' sign value | MISSING exact |
| sign projection | MISSING |
| IsStack | not claimed |
| axioms | propext, Classical.choice, Quot.sound |

## Verification

- EXIT=0
- SHA256: f685f5ab5c950590aa16a3207491edc4bd5be4d453029343745d41161f75c425
- olean: D:\lean\.lake\build\lib\lean\tmp\sheaf\xif\paper\S2366QHomSignProjectionActual.olean, size 2960
- axioms: propext, Classical.choice, Quot.sound.
