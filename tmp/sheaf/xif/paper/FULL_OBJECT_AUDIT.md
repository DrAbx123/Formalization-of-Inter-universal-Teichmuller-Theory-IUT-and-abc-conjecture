# Full object semantic audit (current B path)

Status legend: OK = statement matches paper/construction; FIX = object
statement or carrier is wrong; GAP = exact missing source object; MODEL =
intentional model replacement not yet proved equal to source.

## 1. Paper notation (from rendered pages)

- q_v with ONE underline under q: q-parameter.
- q_v with TWO underlines under q: 2l-th root of the q-parameter.
- v has one underline in both symbols; the disambiguator is q.
- Paper theta: (double-underlined q_v)^(j^2).
- mu_{2l} acts by multiplying theta values by roots of unity (Fig. 3.4).
- Cor. 3.12 averages over j in F_l^x; zero label is the q-pilot label.

## 2. Severe semantic errors found

### E1. SignedLabel -> theta is not injective

`SignedLabel l = {j : Int // -l* <= j <= l*}` includes both j and -j.
`gaussExponent j = j^2` and `theta_neg` show theta(j) = theta(-j).  Thus
`paperThetaImagePoint : SignedLabel -> Block` and every `j |-> q^(j^2)` map is
2-to-1 on nonzero labels.  Paper labels are the quotient `|F_l| = F_l/{+-1}`
(or the nonnegative representatives 0,...,l*).  Using all SignedLabel as the
index is a multi-to-one semantic deviation.  It does not change a set range or
a symmetric average, but it is wrong as an object-level map and wrong for any
sum/cardinality/weight that is not symmetric.  FIX: introduce a quotient/nonnegative
ThetaLabel carrier and make the theta image map injective.

### E2. qParameter -> qRoot is 2l-to-1

The 2l-th root of q_v is not canonical: there are 2l roots.  A map
`qParameter |-> chosen qRoot` is not injective; only the mu_{2l}-orbit of the
root is well-defined.  Files that treat one chosen root as the paper theta
point without the mu_{2l} orbit are semantically wrong.  The orbit-union hull
(PaperC3RootThetaHullActual) is the right direction; single-point comparisons
need the orbit or an explicit choice/indeterminacy.

### E3. Stale LTorsion -> Fin 6 label

`NativeTorsionGapsActual`, `NativeTorsionGapsIntegration`, and possibly
`NativeTorsionFieldsActual/Complete/Proof` still have
`Multiplicative (LTorsion l) -> Fin 6`, which is multi-to-one (`l^2` to 6).
The new six-slot carrier uses rootsOfUnity 6 with a bijective zeta^k |-> k
label.  Old files must be deprecated/updated; do not feed them into the path.

### E4. Exponent double-square

`PaperC3ThetaValuesActual` had `(gaussExponent j).toNat ^ 2`, i.e. (j^2)^2 =
j^4.  Fixed to `(gaussExponent j).toNat` and recompiled EXIT=0.  This was a
real constant error.

### E5. Completion qUnit^(j^2) is not paper theta

`PaperC3TensorBlockActual`, `PaperLambdaOHull*`, `PaperMuTwoLTensorActionActual`
use `paperThetaImagePoint = qUnit^(j^2)` in the completion block.  When qUnit
is the q-parameter (single-underline q_v), this is the q-parameter power, not
paper theta.  Paper theta uses the double-underlined root.  These files may be
used only as q-parameter comparison artifacts, never as the paper Theta hull.

### E6. PaperC3SourceData q is arbitrary and theta packet is from another q

`PaperC3SourceDataActual.paperC3Q` uses Classical.choice of q-candidate and
pairs it with `sourceTheater.thetaPacket`; no proof that the two q's agree.
FIX: derive qUnit/thetaPacket from the same source qVFamily and derive theta
from the same q.

## 3. Object register (high-level)

### Theta/root objects
- PaperC3ThetaRootActual: OK root units in algebraic closure; single root point
  is only a representative, orbit must be used.
- PaperC3ThetaValuesActual: FIXED exponent, names now qParameter; FIX label
  domain (E1) and not paper theta.
- PaperC3RootThetaHullActual: direction OK (mu_{2l} orbit hull), but still no
  tensor lift/measure; GAP RootThetaHullLogComparison.
- PaperC3ThetaRootTensorPacketActual: root carrier actual; GAP map to
  completion tensor block.
- PaperC3PrimitiveMu2lRootActual: OK primitive root if compiled.
- PaperMuTwoLTensorActionActual: action on qParameter image; needs retarget to
  root-valued theta/orbit (E5).

### Tensor/hull objects
- PaperC3TensorBlockActual: actual completion tensor block; names paperTheta*
  are misleading (E5); nonzero/nonzero-label set still based on SignedLabel.
- PaperLambdaOHull*: lambda-O hull on completion block with qUnit image; not
  paper root hull (E5); hull=O zero-label argument invalid for paper (zero
  label excluded).
- PaperMuLogUnitRegionActual: actual lambda*O unit region and Haar; OK for
  normalization, but raw vs normalized distinction must be kept.
- PaperBadPlaceTensorGeometryActual: per-b product carrier/hull/mu_log; the
  root coefficient c_norm/(2l) matches the root normalization; still qVFam
  normalized model, not the full paper multiradial object.

### Source model
- PaperSourceGeometryActual: completion-valued value carrier MODEL replacement;
  actual coercion but no proof it equals frozen FPrimeStrip.Mon.
- PaperC3TensorGeometryActual: nondegenerate V-indexed tensor geometry MODEL;
  indexEquiv refl only inside the new model.
- S12CompletionGeometryBridgeActual: partial bridge; reverse GAP q/theta data.
- PaperC3SourceDataActual: E6.

### Source assembly
- NativeSourceTorsionGapsActualConstruction: OK new six-slot gaps.
- NativeTorsionGapsActual/Integration/Fields*: E3 stale.
- NativeSourceAssemblyExactSequenceActual: exactness OK; splitting section GAP.
- NativeSourceAssemblyD7CuspActual: cuspCount actual; cuspHyp realization is
  still Prop; D7 local group is minimal global identity, not per-place actual.
- NativeSplitMultiplicativeAtLiftActual: split GAP CanonicalTateSplitReduction.
- PaperPlaceFamilyInjectivityActual: conditional, not unconditional injective.

### S21/S22
- S21DegreeNormAlignment: actual factor 1/card; completion norm bridge GAP.
- S21c/S21d: actual qUnit/correction; field comparison orientation GAP.
- S22DependentProductActual: product Haar actual; unit region positive, finite
  only under ProperSpace GAP.

## 4. Required fixes before any paper-level claim

1. Replace `SignedLabel` Theta index by quotient/nonnegative `ThetaLabel`; make
   theta image map injective (E1).
2. Treat qRoot only up to mu_{2l} orbit; no single-root paper point (E2).
3. Remove/deprecate stale LTorsion->Fin6 files (E3).
4. Keep completion qUnit^(j^2) separate from paper root theta (E5).
5. Fix PaperC3SourceData q/theta consistency (E6).
6. Build root-valued tensor carrier, hull, normalized mu_log, then compare with
   q-pilot; do not substitute completion qUnit hull.

## 5. Method

Declarations were extracted by scanning all `.lean` files in
`tmp/sheaf/xif/paper`; the severe-pattern scan is in `FULL_OBJECT_SCAN.md`.
Page-level notation was verified by rendering IUT I p.71, IUT II p.2, IUT III
p.173 and counting underline segments under q/v with PyMuPDF; transcription in
`D:\lean\tmp\paper_pages\annotated.txt`.

## S29. rootExtensionProductThetaHull is definitionally the unit ball (trivial log)

`PaperRootExtensionThetaHullActual` defines

  rootExtensionProductThetaHull := rootExtensionProductUnitBall.

The normalized log is taken relative to the same unit ball, so
`rootExtensionProductThetaHullLog_eq_zero` is definitional.  This is NOT the
paper Theta hull; it is the full unit ball.  The actual paper object should be
the lambda-O/scaling hull of the finite root image (or a closure/minimal scaled
region), whose normalized log need not be zero.  The current file only records
image ⊆ unit ball and a Dirac image-count measure.  Do not use the zero as
`-|log Theta|`.

## S30. Final target currently has explicit corrections

The paper-normalized comparison is packaged with three actual correction terms
(`normRatioCorrection`, `-halfNormRatioCorrection`,
`thetaHullCoefficientCorrection`).  It is not yet the unconditional
correction-free paper comparison.  The corrections are explicit and bounded,
not silently dropped.  The final target must either prove them zero or carry
them as actual source conditions.

## Weakness audit (user: target must not be too weak)

W1. `rootExtensionProductThetaHull := unitBall`, log 0.  This is the largest
possible hull and makes the Theta side trivially zero.  It is too weak and is
NOT the paper holomorphic hull.

W2. Final comparison currently carries three corrections.  A target of the
form `paperTheta <= paperQ + correction` is an intermediate inequality, not
the paper xi-f comparison.  The corrections must be proved zero (or the final
target must explicitly require the actual vanishing), not carried as a weakened
conclusion.

W3. Source conditions such as `NormRatioOneSourceCondition`,
`HalfRootInCompletion`, `QVFamNormInstanceGap`, and root-hull scaling formula are
being used as conditional hypotheses.  A paper-level theorem cannot simply
take them as assumptions unless the paper source actually supplies them; they
must be constructed or shown to be the paper's genuine source fields.

W4. Dirac counting measures are not Haar/mu_log.  They may record image counts
but cannot enter the log-volume comparison.

W5. `rootExtensionProductThetaHullLog = 0` is definitional; it must not be
reported as `-|log Theta|` or as a bound on it.

Required strengthened target:

  actual paper holomorphic hull of the union of possible Theta images under
  (Ind1),(Ind2),(Ind3), with genuine product Haar mu_log, has
  -|log Theta| >= -|log q|

with no correction terms and no extra source hypotheses beyond the paper input.
