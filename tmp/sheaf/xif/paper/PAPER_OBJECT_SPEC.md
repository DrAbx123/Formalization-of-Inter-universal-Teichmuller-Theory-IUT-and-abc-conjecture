# PAPER OBJECT SPEC (authoritative after object audit)

This spec supersedes prior surrogate objects.  Do not prove the xi-f inequality
until every object below is constructed with its exact paper meaning.

## Notation (verified typographically)

- `q_v` with ONE underline under q (and one under v): the local q-parameter.
  Lean: `QParameter_v`; source: `qVFamily T b`.
- `q_v` with TWO underlines under q (and one under v): a 2l-th root of the
  q-parameter.  Lean: `QRoot_v`; source: `twoLthRootAt` / `paperRootThetaUnit`.
- Theta labels: nonzero positive representatives j=1,...,l*
  (`ThetaLabel = {j // 0<j}`), NOT all `SignedLabel`.
- Theta value at label j: `(QRoot_v)^(j^2)`.
- `mu_{2l}`: roots-of-unity indeterminacy multiplying theta values.

## Theta side objects (must all exist)

1. `ThetaPilotCarrier`: actual finite carrier of the theta-pilot procession.
2. `ThetaPossibleImage`: for each label j and each Ind/Kummer choice, the actual
   image point in the multiradial tensor/carrier.
3. `Ind1Action`, `Ind2Action`, `Ind3Action`: actual actions on the final tensor
   packet (or on the chosen actual carrier), not Props.
4. `ThetaPossibleImageUnion`: union over labels and the three Ind actions.
5. `ThetaHolomorphicHull`: actual lambda-O/scaling hull of that union
   (NOT the full unit ball; NOT merely closure of a finite set unless proved).
6. `ThetaHullHaar`: genuine product Haar on the hull.
7. `ThetaHullMuLog`: procession-normalized mono-analytic mu_log.

## q side objects (must all exist)

1. `QPilotObject`: actual object determined by the local q-parameters q_v
   (v in V_bad), not by a spectral-normalized coefficient.
2. `QPilotImage`: actual image in the multiradial representation.
3. `QPilotHaar`: actual Haar on the image.
4. `QPilotLog`: classical `log(q) = ord_v(q_v)*log(p_v)`, processioned.

## Forbidden

- replacing qPilot by `c_norm*log p` or `qVFamNormalizedNorm`;
- replacing theta by `thetaPacket.scale = q_parameter^(j^2)` when the root
  value is required;
- hull = unitBall with log 0;
- closure of finite image as hull without scaling proof;
- Dirac counting measure as Haar/mu_log;
- correction terms or conditional source fields as the final target;
- all `SignedLabel` rather than `ThetaLabel` for theta labels.

Only after this spec is implemented may the comparison

  -|log(Theta)| >= -|log(q)|

be stated.
