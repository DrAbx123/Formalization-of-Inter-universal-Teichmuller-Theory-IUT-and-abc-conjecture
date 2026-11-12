# S2399: coboundary correspondence and the internal-to-external H^1 map

Date: 2026-11-02. Layer O. Consumer: S2390 / S2384 / S2204.

## File

tmp/sheaf/xif/paper/S2399H1QuotientActual.lean
Source SHA256 142ccb4a08fcbad0e827fa09f2def7c0382a0d0d23e060df35f903de25f83967
olean SHA256 5db8efe805ee5bac1e017688d81363d7c5e1c0ab2e118635961ddfbae0e9d70d
EXIT=0. Axioms [propext, Classical.choice, Quot.sound].

## Built

S2399Twist_external_coboundary: for a continuous 1-cocycle z and a in mu_{n!},
the quotient (To z)/(To (z.twist a)) is an external coboundary, with witness
a^{-1}; the proof reduces to the commutativity identity
a^{-1} * act_g a = (act_g a)^{-1} * a.
S2399_mk_twist_eq: hence To z and To (z.twist a) have the same external H^1
class.
S2399ToExternal: the induced map
  S2204H1 p n -> ContH1 (LocalAbsoluteGalois p) (S2145Coeff p n),
using Quotient.lift and S2399_mk_twist_eq.

## Exact first missing

The reverse quotient map and the equivalence:
for an external coboundary relation, produce an internal Cohomologous relation
(the same commutativity, opposite direction), then Quotient.lift on the external
quotient; combine with S2399ToExternal to obtain
S2204H1 p n ≃ ContH1 G_v (S2145Coeff p n).
The needed remaining lemma is:
  IsMulCoboundary₁ (fun g => To z g / To (z.twist a) g) =>
  Cohomologous z (z.twist a)
and its quotient descent.

Once the equivalence exists, S2384FiniteH1OfComparison gives
Finite (S2204H1 p n).  No unconditional Finite or surjectivity is claimed.
