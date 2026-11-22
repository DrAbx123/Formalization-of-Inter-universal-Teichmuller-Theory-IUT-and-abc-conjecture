# Q symbol audit: how many q's and which q is used where

Paper evidence: IUT I p.71, IUT II p.2, IUT III pp.173 and 125 (lines 7475-7480).

## Distinct q symbols

| Signifier | Typography | Paper meaning | Lean object(s) | Status |
|---|---|---|---|---|
| q_v | ONE underline under q, one under v | local q-parameter (Tate q), v in V_bad | `qVFamily T b`, `PaperQParameter`, `sourceQUnit`, `qVFamNormalizedGenerator` | q-parameter; used for q-pilot |
| q_v | TWO underlines under q, one under v | 2l-th root of q-parameter q_v^(1/2l) | `twoLthRootAt`, `paperRootThetaUnit`, `PaperQRoot` | root; used for theta values |
| q in q^(j^2) | double-underlined q in Fig. I.1 / Fig. 3.4 | theta value q̲_v^(j^2) | `paperRootThetaValue`, `rootNormedThetaValue` | root q |
| q in log(q)=ord_v(q_v) log p_v | single-underlined q_v on RHS | local q-parameter q_v | `qVFamily T b` valuation/order | q-parameter; q-pilot log |
| q in q^N substitution | local q_v | local q-parameter | `qVFamily T b` | q-parameter |
| q in classical theta series q^{...} | q-parameter (not theta value) | Tate q | `FiniteThetaPacket.q` of qVFamily packet | q-parameter |

No global product q was found in the q-pilot definition: IUT III Def. 3.8 uses
the collection of local q_v for v in V_bad (corpus lines 6640-6655).

## Important consequences

1. Paper q-pilot log-volume is CLASSICAL local valuation:
     log(q) := ord_v(q_v) * log(p_v)   (IUT III lines 7475-7480).
   It is NOT the spectral-normalized norm of a normalized completion element.

2. Paper Theta values use the double-underlined 2l-th root q̲_v,
   not the single-underlined q-parameter q_v.

3. Therefore the bridge
     qVFamNormalizedCoefficient = order(q_v) * rationalDegree
   is NOT an artifact and cannot simply be removed by redefining q-pilot
   with a normalized norm.  It is exactly the identification of the
   normalized Theta-side coefficient with the paper's classical q-pilot log.

4. If that equality fails, the problem is the choice/normalization of
   `qVFamNormalizedGenerator` / normalized spectral norm, not the q-pilot
   definition.  One must adjust/prove the normalized generator norm to match
   p^{-(order*degree)}, not redefine the target.

5. `qUnit` is an ambiguous name: it must be annotated as `qParameterUnit`
   (single underline) or `qRootUnit` (double underline).  Current new files
   mostly use `sourceQUnit` for q-parameter and `paperRootThetaUnit` for root;
   any remaining `qUnit` consumer must be checked.

## Audit rule

Every Lean q-valued object must carry one of:
  QParameter (single underline), QRoot (double underline), ThetaValue (root power).
No object may be called just `q` or `qUnit` without one of these tags.
## 2l normalization audit (CRITICAL)

`C3.q` is q[1u], not q[2u] (see SourcePilotRegion.lean and
PaperQPilotLogVolume.lean).  Therefore:

  paper theta value = q[2u]^(j^2) = q[1u]^(j^2/(2l))

`realThetaValue q j := q^(j^2)` is correct only when q is q[2u].
For q = q[1u] it is off by the missing exponent 1/(2l).

Current `FiniteThetaPacket`/`c3ThetaProcession` use `realThetaValue q j`.
If their q is the source q[1u], their signed theta average is 2l times too
large; the q = 1/5 counterexample is a normalization artifact, not a paper
counterexample.

Fix routes:
  1. use `Real.rpow q ((j^2 : Real)/(2*l))` for the Real theta magnitude;
  2. or construct actual q[2u] in the extension/root stack and use its j^2
     power.  Completion roots are impossible (S342).
