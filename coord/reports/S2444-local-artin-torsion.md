# S2444: local Artin torsion map from the commutator-width input

Date: 2026-11-03. Layer O. Consumer: S2048/S2027/S2109/S2116.

## File

tmp/sheaf/xif/paper/S2444LocalArtinTorsionActual.lean
Source SHA256 4ab6ec75775f798c8bccd55cf3e4bb310a12128216407fcbe2c34f0604566fe0
olean SHA256 e089aed2f24a35ae5e865dba2d067cd574506fee700dd0a530588eb98322fe7a
EXIT=0, axioms [propext, Classical.choice, Quot.sound].

## Built

S2444CommutatorWidthInputRequired = CommutatorWidthInput p (exact missing input).
S2444CanonicalTorsionComparison: given CommutatorWidthInput p, forall U,
  canonicalTorsionComparison p U (from S2116).
S2444LocalArtinTorsionMap: given CommutatorWidthInput p, an actual
  LocalArtinTorsionMap p, with artin U = (canonicalEquiv U h).symm.
S2444LocalArtinTorsionMap_of_width: the same in Nonempty form.

## Exact first missing

CommutatorWidthInput p, i.e. forall U, CommutatorWidthBounded U: every local
Galois group G_L has bounded commutator width (Nikolov-Segal input).  No
unconditional inhabitant is constructed here.  This is the only missing input
for the LocalArtinTorsionMap and for canonicalTorsionComparison at every level
in this route; S2116 already reduces it to finite generation plus the
Nikolov-Segal width theorem.

No unconditional LocalArtinTorsionMap or canonicalTorsionComparison is claimed.
