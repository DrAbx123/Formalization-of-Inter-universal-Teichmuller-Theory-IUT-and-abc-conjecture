# S2142: actual H^1 tower interface and exact gap

Date: 2026-11-02. Layer O. Consumer: S2138 / S2114 / S2046M3M4 / S2091.

## File

tmp/sheaf/xif/paper/S2142ActualH1TowerActual.lean
Source SHA256 4acd21ce89b5c1b81b724eaa0c26493dbcd4586795ce5beccdee14795b9f6fb5
olean SHA256 779b7cb3f8df7aad94a21242262f48026cbd1a2fbd1f6ff82dc1856614bb9723
EXIT=0. Axioms [propext, Classical.choice, Quot.sound].

## Built

S2142ActualMuH1Tower is the exact actual arithmetic tower structure:
- p : Nat, Fact (Nat.Prime p);
- coefficient groups coeff n with CommGroup, TopologicalSpace, DiscreteTopology,
  IsTopologicalGroup;
- actn n : ContinuousGroupAction (LocalAbsoluteGalois p) (coeff n);
- finiteH1 n : Finite (Iut.ContinuousH1 (actn n));
- proj n : H1(n+1) ->* H1(n) and proj_surjective n.
S2142ToS2138Tower maps it to the S2138 abstract tower.
S2142MittagLeffler proves the S2138 ML condition from it.
No inhabitant of S2142ActualMuH1Tower is constructed.

## Exact first missing

The actual arithmetic instantiation:
1. coeff n = mu_n in AlgebraicClosure Q_p, with its natural G_v-action
   (or the paper's coefficient system);
2. the transition mu_{n+1} -> mu_n (and the chosen divisibility chain);
3. finite H^1(G_v, mu_n);
4. surjectivity of the induced h1Proj;
5. the lim^1 connecting map and lim^1 H^1 = 0, or directly the S2114
   representative lift.

S2112/S2114 have no H^1 tower/h1Proj/lim1; S2091 records the same missing
coefficient/cocycle/lim1 comparison steps. No unconditional surjectivity or
CoboundaryLift is claimed.
