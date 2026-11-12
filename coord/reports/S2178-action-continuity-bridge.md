# S2178: topology bridge for the restricted G_v-action

Date: 2026-11-02. Layer O. Consumer: S2164 / S2145 / S2142.

## File

tmp/sheaf/xif/paper/S2178ActionContinuousActual.lean
Source SHA256 b6fb60c4b11149df21f43133ff9316fccf109052a1b6944db3b5ea9fe45ca788
olean SHA256 10fd4ea18f007f1b2ea6de90b4ae55027ba6c3037244bf73e859e5174e0eb2e5
EXIT=0. Axioms [propext, Classical.choice, Quot.sound].

## Proved

S2178TopologyBridge p n identifies the declared topology
S2145Coeff_top p n on mu_{n!} with the subtype topology inherited from the
units carrier.  S2178TopologyBridge_holds proves it for every n.

## Exact first missing

S2178ActionContinuousRequired p n := S2164ActionContinuous p n, i.e. continuity
of the restricted action map G_v x mu_{n!} -> mu_{n!}.  The bridge is now
available, but the remaining proof needs the local-constant/stabilizer
argument for the restricted map (or a direct continuity transfer from the
continuous units action); the naive Continuous.subtype_mk elaboration still
runs into the product-topology instance mismatch.  Once it is proved,
S2164MuActionTowerOfContinuous yields S2145MuActionTower.

No Finite H1, h1Proj surjectivity, lim1 or h2Comparison surjectivity is claimed.
