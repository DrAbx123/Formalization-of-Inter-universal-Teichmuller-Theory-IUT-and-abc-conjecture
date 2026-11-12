# S2196: restricted action continuity proved; actual S2145MuActionTower

Date: 2026-11-02. Layer O. Consumer: S2145 / S2142 / S2138 / S2114.

## File

tmp/sheaf/xif/paper/S2196ActionContinuousProofActual.lean
Source SHA256 ada16a33006afcff94c87235007919a19c12cf9b07745c61bb42d3f11c32f5f7
olean SHA256 2fb4327527db514148cb0f0cfa44b3f1d4ef4dfacaf9ad068f7497d36b16467a
EXIT=0. Axioms [propext, Classical.choice, Quot.sound].

## Proved

S2196ActionContinuous (n) proves S2164ActionContinuous p n, i.e. continuity of
G_v x mu_{n!} -> mu_{n!}.  Proof: the target mu_{n!} is discrete; for each
zeta the fiber of the restricted action is the preimage of the singleton
{zeta} under the continuous units action, pulled back along the continuous
inclusion G_v x mu_{n!} -> G_v x units.  This uses the topology bridge
S2178TopologyBridge_holds.  The preimage of an arbitrary open set U is the
union of the singleton fibers.

S2196MuActionTower : S2145MuActionTower p is then built by
S2164MuActionTowerOfContinuous.

## Remaining first missing

S2145ActualMuH1Instance: Finite (H1(G_v, mu_{n!})) and the induced h1Proj
surjective; then the lim1 connecting map / lim1 H1 = 0 (or directly the S2114
compatible representative lift).  No H1 finiteness/surjectivity or h2Comparison
surjectivity is claimed.
