# Normalized positive hull log-volume: paper formula check

Date: 2026-10-29. Analysis only; no compilation.

## 1. Paper definition of -|log Theta|

IUT III, Corollary 3.12, statement (:10152-10181):

  -|log(Theta)| is the **procession-normalized mono-analytic log-volume**
  [Remark 3.1.1(ii),(iii),(iv); Proposition 3.9(i),(ii); Theorem 3.11(i)(a)]
  of the **holomorphic hull** [Remark 3.9.5(i)] of the union of the possible
  images of a Theta-pilot object [Definition 3.8(i)] in the multiradial
  representation, subject to (Ind1), (Ind2), (Ind3).

The procession normalization is the average over j in F_l^x:

  -|log Theta| = (1/|F_l^x|) * sum_{j in F_l^x}
                    (normalized log-volume of the j-th possible-image hull).

This is not, in general, literally the logarithm of one global Haar volume:
Remark 3.1.1(iii), :5372-5383, explicitly warns that weighted sums of
log-volumes do not generally arise as a positive real multiple of the logarithm
of a measure/volume.

## 2. Packet normalization and the local Haar ratio

Proposition 3.9(i), :6724-6778, defines the local log-volumes mu_log with
**packet-normalization**:

  mu_log(O) = 0

for the local holomorphic integral structures O (the ring-of-integers/
log-shell structure). In the nonarchimedean case multiplication by p_v adds
-log(p_v); in the archimedean case multiplication by e adds 1.

Equivalently, if mu is the additive Haar measure whose integral structure O has
measure one, then on a measurable region H:

  mu_log(H) = log(mu(H) / mu(O)) = log mu(H)   because mu(O)=1.

If the chosen Haar measure is not normalized with mu(O)=1, the correct formula is

  mu_log(H) = log(mu(H)) - log(mu(O))
            = log(mu(H) / mu(O)).

Thus:

- **Under normalized Haar with mu(O)=1:**
    -|log Theta| = log(mu(H)) = log(mu(H)/mu(O)).
- **Without that normalization:**
    -|log Theta| = log(mu(H)/mu(O)) plus the relevant weight normalization.
- **In the paper's weighted/procession normalization:**
    -|log Theta| is a weighted average of local mu_log values, not the logarithm
    of a single global Haar volume unless the actual normalized weights are
    represented by the chosen global Haar measure.

## 3. What the current Lean objects provide

Actual objects already available:

- GlobalIQAmbient C3 j and globalIQHaar/globalIQLogVolume
  (GlobalIQHullInterfaceActual);
- actual lambda*O scaled regions and least hull
  (C3LogShellTensorHolomorphicHullActual), but on C3LogShellTensorBlock, not the
  global IQ ambient;
- actual paper-hull Haar candidate paperThetaPilotHullVolume/logVolume on the
  F_l^x value carrier (PaperThetaPilotHullLogVolumeActual);
- actual normalized local weights and F_l^x average
  (ProcessionNormalizationWeightsActual.localNormalizedWeight,
  processionAverage);
- actual positive point/hull volume candidate from sign-corrected
  sourceLocalLogDegree (SourceHullVolumeSignCorrectedActual).

Not yet available / not proved:

1. An actual global IQ hull H inside GlobalIQAmbient C3 j, with
   imageSet subset H, compactness, and H subset lambda*O unit region.
2. An actual global Haar measure on GlobalIQAmbient C3 j normalized so that the
   actual unit region O has measure one (the constructible globalIQHaar is not
   proved to have this normalization).
3. The actual packet-normalized weighted log-volume mu_log on that ambient,
   with the normalized weights of Remark 3.1.1(ii), not merely uniform
   procession weights.
4. The identification of the paper hull volume with the global Haar ratio
   mu(H)/mu(O); this is exactly where the old sourceSetVolume fails, since it
   is ENNReal.ofReal(sourceLocalLogDegree)=0 for negative theta log.
5. The Ind1/Ind2/Ind3 union-of-possible-images hull and its invariance.

## 4. Exact proposed formula and precise conditions

The strongest correct scalar formula that can be stated without faking is

  -|log Theta|
    = (1/|F_l^x|) * sum_{j in F_l^x}
        mu_log^{norm}( H_j ),

where:

- H_j is the actual holomorphic hull of the union of the possible images at
  label j, subject to the paper's indeterminacies;
- mu_log^{norm} is the packet-normalized log-volume with normalized weights
  [K_v:(F_mod)_v]^{-1} (Remark 3.1.1(ii));
- the average is over the actual F_l^x labels.

Equivalently, if one has an actual global Haar measure mu_norm on the ambient
with mu_norm(O)=1 and if the weighted mu_log is represented by that Haar measure,
then

  -|log Theta| = log mu_norm(H)
               = log(mu_norm(H)/mu_norm(O)).

The second equality is the unit-region-ratio formula. It is valid only under the
normalization mu_norm(O)=1 and the weight-representation hypothesis; the paper's
weighted mu_log is not generally a Haar logarithm (Remark 3.1.1(iii)).

## 5. Answer to the formula question

- Under a genuinely normalized Haar measure with unit region O of measure one,
  log(mu(H)/mu(O)) and log(mu(H)) coincide.
- Without that normalization, the correct expression is
  log(mu(H)/mu(O)).
- At the paper level, -|log Theta| is the **procession/F_l^x average of the
  normalized weighted local log-volumes**, not automatically log of one global
  Haar hull volume. A construction that defines it as a raw real log of an
  unnormalized Haar volume is not the paper scalar.
- Therefore the required actual object is the normalized weighted hull
  log-volume (with an actual unit region of measure one), not the old
  ENNReal.ofReal-truncated sourceSetVolume and not a bare log of an arbitrary
  Haar measure.

## 6. Consequence for the Lean targets

PositiveHullVsQPilotCorrectedActual can only be a candidate comparison until the
following actual objects are supplied:

- global IQ hull H in GlobalIQAmbient C3 j with actual image subset/compactness;
- normalized Haar/weighted mu_log with unit region measure one;
- the paper F_l^x weighted average over the possible-image hulls;
- the actual Ind1/Ind2/Ind3 union.

The sign-corrected positivePointLogVolume is the right direction for removing
the ENNReal.ofReal zero truncation, but it still measures the value-monoid
log-degree, not the paper's normalized Haar hull volume.

## 7. Minimal scalar target (correction)

The final xi-f comparison consumes only two real scalars, not a full global IQ
hull interface.  The minimal target is therefore:

  normalizedPositiveHullScalar : Real,
  normalizedPositiveHullScalar
    = (1/|F_l^x|) * sum_{j in F_l^x}
        (normalized positive hull log-volume at j),

together with the actual native q-pilot scalar

  nativeGlobalQPilotNormalizedLogMagnitude.

The inequality/ray membership is then stated directly on these two reals.
No IQHullLogVolumeInterface, no carrier equivalence, and no unit-region
normalization equality should be introduced for this target; those are stronger
statements than the final comparison consumes and are not established by the
present source data.

The actual sign-corrected positiveHullLogVolume of
SourceHullVolumeSignCorrectedActual is the right scalar-side input direction,
but its F_l^x normalized weighted average is the exact remaining scalar object.
PositiveHullVsQPilotCorrectedActual already uses only scalar data and does not
import or construct the full IQ hull interface.
