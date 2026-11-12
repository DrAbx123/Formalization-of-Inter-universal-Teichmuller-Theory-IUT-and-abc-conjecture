# QBUNDLE-BASE — geometric base of S2735 qPilotLineBundle

Status: read-only; no compile.

## Definition chain

S2735 (S2735QPilotLineBundleActual):
- S2735Arithmetic l := gaussianInitialThetaArithmeticData l;
  its K is GaussianField = Q(i).
- SourceOK := NumberField.RingOfIntegers (S2735Arithmetic l).K
  = Gaussian integers.
- qPilotIdeal l := gaussianFieldFivePrimePlus * gaussianFieldFivePrimeMinus
  * gaussianField2161Plus * gaussianField2161Minus.
- qPilotLineBundle l := (qPilotIdeal l : FractionalIdeal
    (nonZeroDivisors SourceOK) (S2735Arithmetic l).K).
- qPilotLineBundleExtended J := qPilotIdeal l * J.
- S2736QPilotLineBundleLogVolume J :=
  Real.log (FractionalIdeal.absNorm (qPilotLineBundleExtended J)).

## Base judgment

Base = Spec O_K, where K = GaussianField. The bundle is an arithmetic
(Arakelov) line bundle given by a fractional ideal / divisor on Spec O_K.
It is NOT a line bundle on a modular curve X(5), X_1(5), or on the source
elliptic curve.

Evidence:
- qPilotIdeal is a product of four Gaussian prime ideals; no level structure,
  no modular curve, no q-expansion.
- qPilotLineBundle is a FractionalIdeal over O_K.
- S2736 log volume is a norm/degree, not log of a q-expansion or of a modular
  form coefficient.

## Consequence for theta/Klein sections

A modular-curve theta/Klein section (a section of a line bundle on X(5) or
X_1(5)) cannot be pulled back directly to qPilotLineBundle: their bases differ
(Spec O_K vs modular curve). A comparison requires:

1. a modular curve X over O_K or Q, with level-5 structure;
2. a map from Spec O_K (or a finite extension) to X;
3. a theta/Klein line bundle on X and its pullback along the map;
4. an identification of that pullback with qPilotLineBundle (or a
   divisor-class equality).

None of these is in the tree. The existing source-curve theta bundle
(SourceCurveThetaLineBundleActual) lives on the affine Weierstrass curve over
S.arithmetic.F, not on Spec O_K, and its theta global section is an exact
missing obligation (ThetaFunctionLineBundleActual, seven items).

## What is missing for an arithmetic model

- Modular curve/level structure (X(5) or X_1(5)) and a point/component over O_K;
- theta/Klein line bundle on the modular curve;
- q-expansion/level map and its compatibility with the Gaussian arithmetic;
- a divisor/line-bundle comparison with qPilotIdeal;
- integrality/rationality of the pulled section (would follow from O_K-points).

## Verdict

qPilotLineBundle is an O_K fractional-ideal line bundle (Spec O_K base), not a
modular-curve theta bundle. Theta/Klein sections require a new arithmetic model
(map Spec O_K -> modular curve + theta bundle comparison); this is a GAP, not a
formalization shortcut.
