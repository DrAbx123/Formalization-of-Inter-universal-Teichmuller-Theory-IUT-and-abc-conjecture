# S1399: Kappa O^x(G) exact first field

Date: 2026-10-30
Lean: tmp/sheaf/xif/paper/S1399KappaOxGActual.lean
EXIT=0; SHA256 69F129A0A73FA037D35C29CDD39F154B267C2FBBC21B72217F6E7C1EA01D38AB.

## Actual (S1388)

S1399ActualPairDatum I :
  KappaOrbitUnitsActionPairDatum (MiddleGraph I) (S00 I) (S11 I)
  := actualMiddlePairDatum I.

sourceUnits v = (S01.Mon v)^x; sourceAction = actual unitsAction composed
with middleEval; kappaUpper/kappaLower are actual S1187 link Kummer
isomorphisms from fLinkAt 0 1 0 0 and 0 1 1 1.  No self/refl, no finite model.

## Exact first field

S1399PaperOxGModule I G:
  sourceUnits : V -> Type
  [CommGroup sourceUnits]
  sourceAction : forall v, G ->* MulAut (sourceUnits v)
  groupEquiv : G ≃* MiddleGraph I
  unitsEquiv : forall v, sourceUnits v ≃* (S01.Mon v)^x
  action_compat : unitsEquiv (sourceAction gamma u) =
    (S01.unitsAction v) (middleEval v (groupEquiv gamma)) (unitsEquiv u).

No inhabitant is asserted.  The paper group-theoretic O^x(G) algorithm and
its identification with the middle-strip units remain exact; S1388 supplies
the actual pair datum on MiddleGraph, not the abstract paper G.

No weak interface, no identity Kummer representative, no finite model.
