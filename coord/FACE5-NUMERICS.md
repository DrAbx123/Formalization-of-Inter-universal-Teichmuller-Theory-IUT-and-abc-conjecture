# FACE5 — numerical check of V vs (sF-1)A (l=5, p=2/11)

Status: definition-based model calculation. qpilot's SSINEQ-ANATOMY.md was not present in
the workspace at write time; this file uses the lana definitions read directly and the
hull/Theta-data numbers already recorded (shehdd A893 + hull volume data + A892 arch).
It is not a compiled lana computation and not a proof of SSIneq.

## 1. lana definitions (source)

- Iut/Wall/MultiContainer.lean:88-89:
    SSIneq D := (sFactor (nC D) - 1) * D.qPilot.absLogQ <=
                logVol D (hullOf D (vcI D)).
- Iut/Wall/Rss.lean:302-303: nC D = (l - 1) / 2; l=5 => nC = 2.
- Iut/Wall/Pilots.lean:55-67: sFactor n = (sum j<n (j+1)^2)/n = (n+1)(2n+1)/6;
  n=2 => sFactor = 3*5/6 = 2.5; coefficient sFactor-1 = 1.5.
- Iut/Cor312/LeftHandSide.lean:86-88:
    absLogQ = logQ / (2*l); l=5 => absLogQ = logQ/10.
  Hence (sF-1)*absLogQ = 1.5*logQ/10 = 0.15 logQ.
- vcI: Iut/Wall/Ind3.lean:80-81, productRegion of vcIComp = log-shell (finite) or
  archimedean log-shell.
- hullOf / logVol: Iut/Wall/Rss.lean:324-329, hullFamily and processionVol.

## 2. Theta-data used (A893 / shehdd)

- l=5, p=2: (e,n,r) = (1,4,1) => finite term
  logMuPaper = (1 + 1 - 1 - 1/4) log2 = (3/4)log2 = 0.5198604.
- odd bad places: (e,n,r) = (1,1,0) => logMuPaper = 0.
- arch = 1.491303, applied globally once (A892).
- torsion assumed 0 (not supplied; threshold given below).

For D with bad places {2,11}:
    V0 = finite(p=2) + finite(p=11) + arch - torsion
       = 0.5198604 + 0 + 1.491303 - 0
       = 2.0111634.
(If the arch is divided by the number of capsules, V would be
0.5198604 + 1.491303/2 = 1.2655; it still exceeds the requirement below. The global-once
reading is the A892 choice used here.)

## 3. Explicit D candidates

Stage4 model q = 22 (bad places 2 and 11):
    logQ = log 22 = 3.0910425,
    A = absLogQ = logQ/10 = 0.3091043,
    requirement = (sF-1)A = 1.5*0.3091043 = 0.4636564,
    V = 2.0111634,
    V - requirement = 1.547507 > 0  => SSIneq HOLDS numerically.
  Gap decomposition: finite p=2 contributes 0.51986, p=11 contributes 0, arch contributes
  1.491303; the requirement is only 0.46366. The margin is 1.5475, dominated by arch;
  without arch the finite part already exceeds the requirement by 0.0562 (barely).

Single-prime variants:
| D bad set | q | logQ | A | requirement | V | V - req | SSIneq |
|---|---|---:|---:|---:|---:|---:|---|
| {2} | 2 | 0.693147 | 0.069315 | 0.103972 | 2.011163 | 1.907191 | TRUE |
| {11} | 11 | 2.397895 | 0.239790 | 0.359684 | 1.491303 | 1.131619 | TRUE |
| {2,11} | 22 | 3.091043 | 0.309104 | 0.463656 | 2.011163 | 1.547507 | TRUE |

In all three model choices V > (sF-1)A, so SSIneq is numerically true.

## 4. Sensitivity / where the gap is

Let T = sum torsion.
- For D={2,11}: V - req = 2.011163 - T - 0.463656 = 1.547507 - T. SSIneq holds for
  T < 1.5475; fails only for torsion above 1.55.
- D={2}: margin 1.9072 - T; D={11}: margin 1.1316 - T.
- The positive margin is dominated by the single global arch term 1.491303. The finite
  p=2 term (0.51986) alone gives only a 0.0562 margin over the requirement; if the arch
  term were absent or normalized away, the inequality would be very tight.
- No negative finite place appears in this model: odd places have logMuPaper = 0
  (unramified), p=2 is positive. Thus the "gap item" is not a missing finite term; it is
  the arch normalization (global once vs per capsule) and torsion.

## 5. Verdict

At the model level (lana definitions + A893 Theta-data + A892 arch):
- V = 2.011163 for D={2,11}; (sF-1)A = 0.463656; V - (sF-1)A = +1.547507.
- SSIneq is numerically TRUE, with the margin coming almost entirely from the arch term;
  finite terms alone leave only +0.056.
- The critical unverified item is the arch normalization (1.491303 global-once) and the
  torsion sum; no finite negative contribution is present in this model.

Caveat: qpilot's SSINEQ-ANATOMY.md was absent; actual explicit D (curve, field F, ramification)
and compiled vcI/hullOf/logVol are still required. This is a definition-level numeric check,
not a lana/Lean theorem.
