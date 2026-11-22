# Five paper-object gaps: existing work and supplement plan

## 1. Root stack / mu_2l orbit carrier

Existing actual:
* S356RootStackActionGroupoidActual: groupoid of candidate roots with
  mu_{2l} morphisms; rootStackGroupoid, rootObj.
* S392RootStackSectionMonoidActual: SectionCarrier = RootObj -> Multiplicative Int,
  rootDelta injection, qSection/rootSection, mu2lAction.

Not paper-faithful: SectionCarrier is a function model, not paper O^triangle;
completion/root sections are only value-level.  S356 itself records
RootStackMonoidSectionCarrier as exact missing.

Supplement: prove the S392 carrier is the paper root-stack section monoid
(or construct actual O^triangle multiplication), and prove
qSection_toCompletion / rootSection_pow are the paper q[1u]/q[2u]
sections, not arbitrary values.

## 2. Paper holomorphic hull / lambda-O region

Existing actual:
* PaperLambdaOHullActual: paperLambdaOHull, paperLambdaOScaledRegion.
* PaperLambdaOHullHaarActual: candidate scaled region Haar positive finite;
  PaperLambdaOHullCandidateGap (hull = a single scaled region) exact.
* LiteralIQHolomorphicHullActual: literal IQ hull on LiteralIQCarrier.

Not paper-faithful: candidate equality for the infinite intersection hull is
missing; the Haar/log is for a candidate region, not the actual hull.

Supplement: prove PaperLambdaOHullCandidateGap (or compute the intersection
measure by compactness/limit), then get actual hull Haar/mu_log.

## 3. Product Haar / root-stack Haar transport

Existing actual:
* PaperRootExtensionProductHaarActual: Haar on product of L_b = K(root_b);
  product unit ball positive/finite.
* RootThetaExtensionHullCarrierActual: extension root image/hull in AC product.

Not paper-faithful: Haar is on the chosen L_b product, not on the
mu_{2l}-root-stack; no invariant measure or transport map.

Supplement: construct actual root-stack (quotient/invariant) Haar and a
map to the L product with normalized-log equality; or replace the L product
by the root-stack carrier.  RootThetaToCompletionHullMapGap is one exact
transport obstruction.

## 4. PaperSignedHull ambient/procession equality

Existing actual:
* PaperSignedHullSignedActual: signed c3ThetaSignedProcession (classical q^(j^2)),
  conditional on hlog/hnormal.
* S654RootSignedHullSignCorrectionActual: corrected positive magnitude
  procession, but currently not compiled (depends on S645/qVFamP stale name).
* S645: sign-wrong (negative procession), haverage impossible.

Not paper-faithful: ambient is IQHullLogVolumeInterface (interface),
hnormal is explicit, and the root-normalized version needs sign fix +
actual C6 IQ interface.

Supplement: make S654 independent (use qVFamTensorP, no S645 import),
prove average_nonneg, then prove hnormal for the actual IQ interface and
RootThetaProcessionNormAlignment.

## 5. q[1u]/q[2u] paper-level bridge

Existing actual:
* TwoLthRootKummerActual: hodgeTwoLthRoot^(2l)=qVAlgClosedUnit.
* QVFamRootFactorCorrectionActual: q[2u] coefficient order/(2l),
  classical = 2l * root coefficient.
* S392RootStackSectionMonoidActual: candidate qSection/rootSection.

Not paper-faithful: completion 2l-root impossible (S342); root is in AC,
and no paper root-stack section equality to q[1u] is proved.

Supplement: prove S392 qSection/rootSection are the paper q[1u]/q[2u]
sections in the root stack, with rootSection^(2l)=qSection and
qSection_toCompletion=q[1u].  This is the missing q normalization bridge.
