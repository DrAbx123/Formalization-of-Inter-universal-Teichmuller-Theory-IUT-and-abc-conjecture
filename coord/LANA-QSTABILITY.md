# LANA-QSTABILITY — lana's acknowledged sF/gap/Step(xi) instability and S2717/S2807 level terms (A1119)

Status: read-only; no compile.

## 1. What lana explicitly acknowledges

### 1.1 Cor 3.12 statement is a specification boundary, not the paper

Iut/Cor312/Statement.lean:26-60:
- Corollary312Variant is a Prop-valued DEFINITION, deliberately left without
  proof and without axioms.
- The theta-pilot region is an INPUT (RHSData.thetaPilot), not the output of a
  multiradial algorithm.
- The container/log-volume/hull are interface abstractions; their
  correspondence with IUT III Propositions 3.1-3.3, 3.9 and Remark 3.9.5 is
  documented but NOT itself a theorem.
- Explicit sentence: "The intended statement may differ from the formulation
  printed in the IUT papers."
So lana already flags that its statement is a project-specific variant.

### 1.2 Gap: Ind2 terms are open (0 or >0)

Iut/WallEquiv/Gap.lean:29-37:
- gap D = (1/l*) sum_i sum_vQ gapHullAt D i vQ.
- gapHullAt = sum_c w_c ind2Term at primes, 0 at infinity.
- "Open: whether the (Ind2)-terms at the bad primes are 0 or >0 ... so the
  sign gap >= 0 is all that is proved."
So lana does NOT assert gap=0; only gap>=0. The q-linear term sF*A inside
gap_eq_rhs_add is a decomposition, not a cancellation.

### 1.3 Non-derivability of Step (xi): the sF>1 / q-instability acknowledgment

Iut/WallEquiv/NonDerivable.lean:10-104 is the explicit statement:
- "Theorem 3.11 of IUT III, as formalised here, does not imply Step (xi) of the
  proof of Corollary 3.12."
- The package decouples arithmetic: ell, log q, a=|log q|=log q/(2ell),
  V=log-vol(hull(VC(I))), R=-|log Theta|.
- xi_iff: Step (xi) holds iff (s-1)*a <= V, i.e. Step (xi) is exactly the
  Scholze-Stix inequality over the package.
- not_xi_family: for all ell, log q>0, V,R with V - s*a <= R, Step (xi) fails
  whenever V < (s-1)*a.
- Explicit counterexample (NonDerivable:482-494): ell=7, log q=14, a=1,
  s=sFactor(3)=14/3, V=R=1; (s-1)*a=11/3 > 1=V, so Step (xi) fails.
- exists_package_not_xi_nonneg: V=0 is compatible with failure for every ell.
- exists_package_not_xi_ge: for every lower bound L <= V independent of a,
  choose a > L/(s-1), then Step (xi) fails with V=L.
- "Upper bounds on V cannot force Step (xi)" (header line 87).
This is exactly the q-instability/sF>1 obstruction: with sF>1, the q term
(sF-1)*a grows with a, and V bounds independent of a cannot dominate it.

### 1.4 sF>1 is a lana theorem

- sFactor n := (sum_{j=1}^n j^2)/n = (n+1)(2n+1)/6 (Pilots:55/67).
- one_lt_sFactor: for n >= ? (used at n=(ell-1)/2 with ell>=7), sF > 1.
  NonDerivable:511 uses 1 < sFactor ((ell-1)/2).
- With ell=7: sF=14/3 > 1, sF-1=11/3.

### 1.5 Step(xi) alignment pins the normalization

Iut/Wall/Step3115AlignmentProofActual.lean:75-106:
- det_eq_lhs_div_twoL_of_hull_alignment: det readout = qPilot.lhs/(2l).
- alignment_forces_normalisation: if hull and det readouts align, then
  rhs = qPilot.lhs/(2l).
- Comment: "pins the mismatch to the sFactor versus 1/(2l) normalisations
  (model-level, not a proof gap of the comparison)."
So lana itself records the sFactor vs 1/(2l) normalization tension.

## 2. S2717/S2807: is there a level term?

S2717Cor312FullTargetActual:47-67:
  S2717ThetaHullLogVolume = 
    - (globalThetaHullInterface).logVolume (globalThetaHull)
  where globalThetaHull is the C3 least lambda-O holomorphic hull on the
  ArithmeticTensorTupleBlock, and nu is an arbitrary additive Haar measure.

No occurrence of:
- nC / ell* / capsule count;
- j-average over F_l^*;
- sFactor;
- any level index;
- any theta value q^{j^2} / qOrder.
It is just the C3 tensor-block holomorphic hull log-volume, negated.

S2807ThetaHullVolumeIdentityActual:40-47:
  S2717ThetaHullLogVolume = - haarLogVolume (actualC3LogShellTensorHaar)
    (actualC3LogShellTensorRegion).
Again no level/j/sFactor term; only equality to the C3 Haar region volume.

By contrast lana:
- Wall.logVol (Rss:324) = processionVol = (sum_i globalVol (U i)) / proc.length;
- processionVol (Cor312/LogVolume:207) = (sum_i globalVol)/D.proc.length;
- lana rhs includes the theta-pilot hull and gap_eq_rhs_add has +sFactor(nC)*absLogQ;
- lana's gap and SSIneq explicitly contain sF.

So:
- Our S2717/S2807 R has NO level term and NO sFactor term.
- Lana's rhs/gap/SSIneq DO have the capsule average and sFactor.
- No theorem in our tree identifies S2717ThetaHullLogVolume with lana
  logVol(rhs) or with -(lana rhs). S2807 only identifies it with the C3 Haar
  region volume.

## 3. Consequences

1. The lana q-instability counterexamples (NonDerivable) are about lana's
   package numbers (a, V, R with sF). They do not directly transfer to our R
   because our R is a different object: C3 global theta hull Haar, no
   procession/j-average, no sF.
2. But the same structural obstruction applies: our R is not known to contain
   a positive q-linear term (S2807 is a Haar identity; no qOrder), and gap is
   not constructed in S2717. Our target M = A - R is still not proved.
3. S2717UpperGap uses CThetaPaper * paperQAbsLog, i.e. the paper CTheta
   comparison, not lana gap; it is a different route.
4. If one wanted to import lana's sF analysis, one first needs a theorem
   identifying S2717ThetaHullLogVolume with lana's procession-normalized rhs,
   including the level/j-average. That theorem is absent.

## 4. Verdict

- lana DOES acknowledge: statement may differ from paper; Ind2 terms open;
  Theorem 3.11 does not imply Step (xi); sF>1 creates a growing q term that
  V bounds independent of a cannot dominate (explicit counterexamples).
- S2717ThetaHullLogVolume and S2807 contain NO level term, no sFactor, no
  j-average; they are C3 tensor-block Haar hull volumes.
- lana logVol/rhs/gap DO contain the procession average and sFactor.
- No equality between our R and lana rhs is proved; our R is a different
  normalization.
- Therefore our line cannot directly reuse lana's q-instability theorems, but
  also cannot claim lana's sF analysis has been internalized; the missing
  identification remains a GAP.
