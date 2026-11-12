# FACE2-VERDICT2 — arch/infinite component included (A901)

Status: corrected verdict. Not an IUT theorem, not Lean evidence.

## 1. Real definition of V = logVol(hull(vcI))

lana source (read-only):
- `Iut/Wall/Ind3.lean:58-62`: `vcIComp i .infinite c = LocalTheory.logShell D.Kt .infinite ...`;
- `Iut/Wall/VcI.lean`: `hullPacket` / `packetVol` include the `.infinite` rational place;
- `Iut/Concrete/LocalConstruct/ArchLogShell.lean`: `archLogShell` is compact, of positive
  Haar measure (`haar_archLogShell_pos`), and `archLogShell ⊆ (sqrt2*pi)^|I| * archIntegral`
  (`archLogShell_subset`).

So V is NOT only finite places: the archimedean component contributes a nonzero
(in general positive) term.

## 2. Tame-everywhere recomputation

At finite tame places e=1:
- hullPacket_tame term = (1-1/e) log p = 0;
- logMuPaper = -(r/n) log p <= 0.
At infinity:
- arch component is bounded above by |I| * log(sqrt2*pi) (green
  componentVol_archLogShell_le_leastHull_le: componentVol(arch hull) <= |I| log(sqrt2*pi));
- its sign is not forced to be negative; positive measure of archLogShell means the
  component can be positive (up to the bound).

Hence tame-everywhere gives
    V_tame <= C_arch := |I| * log(sqrt2*pi)   (finite tame contribution 0)
and the q side is (sF-1)*A with A = |log q|.

## 3. Corrected verdict

- The original claim 'RHS = 0, strict failure' is WRONG: arch/infinity is a positive
  bounded term, so V_tame is not zero.
- The comparison in tame-everywhere becomes
      (sF-1) A <= V_tame <= C_arch (+ wild buffer),
  i.e. it holds only for A <= C_arch/(sF-1) and FAILS for large A.
- Since A = |log q| is unbounded over data, tame-everywhere is NOT a uniform
  counterexample, but it is also NOT a proof of SSIneq: it reduces to a bounded-A
  regime; large A requires wild-place positive buffer or the target lower bound
  D_exact >= c*A.

## 4. Consequence

- FACE2 cannot be dismissed by a zero-RHS counterexample; arch gives a constant buffer.
- Attack face 2 is still not an unconditional route: needs a uniform lower bound
  V >= c*A for large A, which is the target inequality (or wild buffer).
- Refined split: tame-everywhere with small A can hold; large A needs wild places.
