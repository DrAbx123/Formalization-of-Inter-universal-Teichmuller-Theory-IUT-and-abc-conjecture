# S2164: actual G_v-action on mu_{n!} and power compatibility

Date: 2026-11-02. Layer O. Consumer: S2145 / S2142 / S2138 / S2114.

## File

tmp/sheaf/xif/paper/S2164MuActionTowerActual.lean
Source SHA256 73c9c697e17fe5ddbc813f9f6b1513d09f6db592045ea6d97f0687556ee1219b
olean SHA256 f7e98d3ad68893eef308b845a835ad984610feba75e9640a4d19ae78c7138c88
EXIT=0. Axioms [propext, Classical.choice, Quot.sound].

## Built

S2164Roots p n is the subgroup mu_{n!} of (AlgebraicClosure Q_p)^x.
S2164RootsMulAut (n) (e) is the MulAut of mu_{n!} induced by a units
automorphism e; the proof that e maps mu_{n!} onto itself is
S2164Roots_map.
S2164RootsActionAut n : LocalAbsoluteGalois p →* MulAut (mu_{n!}) is the
actual action homomorphism induced by localGaloisUnitsAction.
S2164PowMap_equivariant proves the power transition zeta |-> zeta^(n+1)
intertwines the level n+1 and level n actions.

## Exact first missing

S2164ActionContinuous p n: continuity of the restricted action map
  LocalAbsoluteGalois p × mu_{n!} -> mu_{n!}.
The units action is continuous (LocalGaloisKummerAction.continuous_units_smul),
but the restricted action has its own declared topology S2145Coeff_top; a
topology-bridge/continuity lemma is still missing.  Given
S2164ActionContinuous at every n, S2164MuActionTowerOfContinuous constructs
S2145MuActionTower.

Then Finite H1, h1Proj surjectivity and lim1 remain missing.  No H1 finite or
surjectivity is claimed.
