# S2204: actual H^1 carrier and the H^1 instance gap

Date: 2026-11-02. Layer O. Consumer: S2196 / S2145 / S2142 / S2138 / S2114.

## File

tmp/sheaf/xif/paper/S2204ActualH1InstanceActual.lean
Source SHA256 1e005dea87cc5423e4236a9738cc53d6a8c9fe028f4d2b910e7e09f670e53e3d
olean SHA256 27980603f24c45bcc92c1394650e673aa513dc9d1d4cdbb930b43a68aa3d40b0
EXIT=0. Axioms [propext, Classical.choice, Quot.sound].

## Built

S2204H1 p n = Iut.ContinuousH1 ((S2196MuActionTower p).actn n) is the actual
level H^1 carrier of the mu_{n!} tower.
S2204H1InstanceData is the remaining data: finiteH1, power-induced proj, and
proj_surjective.
S2204ToS2145Instance: given S2204H1InstanceData, S2196MuActionTower extends to
S2145ActualMuH1Instance.

## Exact first missing

1. S2204H1FiniteRequired: forall n, Finite (H1(G_v,mu_{n!})).
2. S2204H1ProjRequired n: the actual monoid hom
   H1(n+1) ->* H1(n) induced by the coefficient power map
   mu_{(n+1)!} -> mu_{n!}; construction from ContinuousH1 requires the
   coefficient-change map on continuous 1-cocycles and its compatibility with
   the coboundary relation.
3. S2204H1ProjSurjectiveRequired: surjectivity of that transition.
4. lim1 H1 = 0 / S2114CompatibleRepresentativeLift.

No finiteness or surjectivity is claimed.
