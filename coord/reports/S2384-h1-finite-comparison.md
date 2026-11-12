# S2384: finite external H^1 and the internal/external comparison gap

Date: 2026-11-02. Layer O. Consumer: S2372 / S2360 / S2204 / S2214.

## File

tmp/sheaf/xif/paper/S2384H1ComparisonActual.lean
Source SHA256 b067c8ab27898458b57f6cdcaa6cbcea366af5bbc12de669989e931dc4445768
olean SHA256 6cdb6a7f8f4c377f03c9566b678dbc70c6f91141628f94d22129bdb1346474fe
EXIT=0. Axioms [propext, Classical.choice, Quot.sound].

## Built

S2384ExternalH1 p n is the external
ContH1 Gal(Qp^alg/Qp)(Mu (n!)) type.
S2384ExternalH1_finite: Finite (S2384ExternalH1 p n), transported from the
finite Kummer quotient S2372KummerQuotient via S2360KummerEquiv.
S2384H1Comparison is the exact missing equivalence between the actual
Iut.ContinuousH1 carrier S2204H1 p n and S2384ExternalH1.
S2384FiniteH1OfComparison: given the comparison, Finite (S2204H1 p n).

## Exact first missing

An inhabitant of S2384H1Comparison, i.e. an equivalence between
Iut.ContinuousH1 ((S2196MuActionTower p).actn n) and
ContH1 Gal(Qp^alg/Qp)(Mu (n!)).  The two definitions differ in the choice of
continuous crossed homomorphisms and coboundary convention; no comparison API
exists.  Once it exists, Finiteness of the actual H^1 follows immediately from
S2384ExternalH1_finite.

No unconditional Finite (S2204H1) or transition surjectivity is claimed.
