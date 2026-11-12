# VCI-FROM-HULL — V's q-dependence (A904)

Status: source audit (lana read-only). Not an IUT theorem, not Lean evidence.

## 1. vcI finite components contain NO q-power

lana `Iut/Wall/Ind3.lean:58-62`:
    vcIComp i .finite p c = LocalTheory.shell D.Kt p (tuple ...)
    vcIComp i .infinite c = LocalTheory.logShell D.Kt .infinite (tuple ...)

`shell`/`logShell` depend only on K, p, the tuple; there is no `scaleElt`, no
`qroot` and no `q` in `vcIComp`.  The theta scaling `D.scaleElt` appears in
`lgp D S` / theta-pilot components (`IdentifiedCopies.lean`), NOT in `vcI`.

## 2. Consequence for V = logVol(hull(vcI))

- Finite finite-place hull at p: `componentVol_leastHull_tensorLogShell_eq`
  = sum_j logShellRadius(finPart) * log p, independent of q magnitude;
- Archimedean: `archLogShell` independent of q; bounded above by |I| log(sqrt 2 pi)
  (green `componentVol_archLogShell_le_leastHull_le`);
- Hence V is q-magnitude independent for fixed bad-prime support:
      V = V(K, p, e, tuple)   (no |log q| term).

An exact upper bound:
    V <= sum over bad p of sum_j logShellRadius(p,e) log p + |I| log(sqrt2 pi),
and at tame p this is sum_c w_c sum_j (1 - 1/e) log p + arch.

## 3. SSIneq large-q issue

SSIneq: `(sFactor(nC)-1) * absLogQ <= V`, with absLogQ = logQ/(2l) proportional
to |log q|.  Since V has NO |log q| dependence and absLogQ is unbounded when q
is scaled (support unchanged), SSIneq would fail for sufficiently large q.
Thus either:
(a) lana's q is bounded/normalized by additional data not in vcI, or
(b) SSIneq as stated is not stable under q-scaling and the large-q failure is real.

The source shows no q-boundedness in `vcI`; this is a genuine audit finding for
qpilot/abc.  It also means the FACE2/tame discussion must track q magnitude:
V is a q-independent constant, q side grows with |log q|.
