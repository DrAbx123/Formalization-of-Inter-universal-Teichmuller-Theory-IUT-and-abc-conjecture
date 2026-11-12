# S1920: paper-level xi-f on the source-faithful `S1895PaperO`

Date: 2026-11-01.
File: `tmp/sheaf/xif/paper/S1920PaperFaithfulXiFActual.lean`.
Consumer check: `tmp/sheaf/xif/paper/_S1920Consumer.lean`.

## Target and consumer

S1895 proved that the S1880 paper route cannot carry the paper-level
F-times-mu identification: `S1880PaperO`'s strip is the concrete finite-local
strip (value monoid `LocalIntegralMonoid 5`, with the torsion element `-1`),
while the paper `(1,0)` core is `S1487Strip 1 0` (value monoid
`SourceHaarActualValueMonoid`, torsion-free), so no `FPrimeStripEquiv` exists
(`s1895FirstMissing_impossible`).  S1880's xi-f content therefore had to be
rebased onto `S1895PaperO`, the object whose four paper-level identifications
S1895 proves.

Consumer: the paper-level xi-f (Theta-link + `-|log q| <= -|log Theta|`) on the
source-faithful O object, i.e. on the same object that carries the actual S1679
O(-D) line bundle, the actual S1527/S1391 scalar, the canonical times-mu strip,
the one-column log-Kummer correspondence and the (1,0) label binding.

## Delivered declarations (all proved, EXIT=0)

Given `D : S1895PaperInput` (the paper Definition 3.1 input of S1895) and
`D' : OrigXiFPaperSignedHullData X D.l` (an actual paper signed-hull datum):

* `S1920PaperC3 D := S1527C3 D.l D.R ...` -- the actual S1391 L-carrier at the
  concrete Gaussian place above 5, re-indexed along the definitional identity
  `S1895PaperInput.I D = S1527Input D.l D.R ...`.  Facts:
  `s1920PaperC3_q` (`(C3).q = S1487Cand`),
  `s1920PaperC3_logVolume` (`OrigXiFPaperQPilotLogVolume C3 = -localLogMagnitude S1487Cand`),
  `s1920PaperC3_logVolume_eq_neg_abs` (`= -|log q|`),
  `s1920PaperC3_logVolume_eq_neg_order_mul_log_five` (`= -(order_C3 * log 5)`).
* `s1920_paper_thetaLink : OrigXiFThetaLinkActual (S1895PaperO D) D' (S1920PaperC3 D)`
  -- from `S1554_origXiFThetaLinkActual` at the same actual input; both exact
  fields are produced, none assumed.
* `s1920_paper_scalar_eq`, `s1920_paper_signedHull_le` -- the two fields,
  exposed separately.
* `s1920_paper_linkIdentification` -- the concrete `link_identification`,
  definitionally `OrigXiFThetaLinkIdentification (S1895PaperO D) D' (S1920PaperC3 D)`
  (`s1920_paper_linkIdentification_eq`); proved from
  `S1527_origXiFScalarExactField` and `S1554_signedHull_le`.
* `s1920_paper_qPilotLogVolume_eq_neg_abs` -- the object scalar is `-|log q|`.
* `s1920_paper_qPilotLogVolume_le_signedHull` -- the object scalar is at most
  `OrigXiFSignedThetaHullLogVolume D'`.
* `s1920_neg_abs_log_q_le_signedHull` -- **the requested inequality**
  `-|log q| <= OrigXiFSignedThetaHullLogVolume D'`, reusing S1880's scalar proof
  `s1880_xiF_inequality_abs` verbatim; `s1920_neg_abs_log_q_lt_signedHull` is the
  strict form (S1880).
* `s1920_paperC3_le_signedHull` -- the same comparison through the C3/S1554 route,
  as a cross-check of the two scalar presentations.
* `s1920_paper_xiF_ray` / `s1920_paper_xiF_ray_iff` / `s1920_paper_xiF_core` --
  the xi-f ray membership on `S1895PaperO` (via
  `OrigXiFThetaLinkActual.link_implies_inclusion` and the proved link
  identification), its equivalence with the signed-hull inequality, and the core
  conjunction `link_identification ∧ ray membership`.
* `S1920PaperIdentifications D` + `s1920_paperIdentifications` -- S1895's
  six-part conjunction (four paper identifications plus the two frozen
  scalar/line-bundle fields) re-packaged as a named proposition.
* `s1920_paperFaithful_xiF` -- the bundle: S1895 identifications, the
  Theta-link `link_identification`, the ray membership, the object scalar
  equality and the inequality, all on `S1895PaperO`.
* `s1920_paperFaithful_scalar` -- the scalar half alone.
* `s1920_s1880_bridge_impossible`, `s1920_s1880_no_stripEquiv` -- recall from
  S1895 that the S1880 carrier route stays impossible.

## Evidence

* Source: 20258 bytes, SHA256
  `AEA8A75395E2DB9DAADB5588D80F60E724D24522DE0C3992FC1162E98FCAF17F`.
* `lake env lean -j1` EXIT=0, no errors, no warnings, no `sorryAx`.
* `#print axioms` on all 17 main declarations = `propext`, `Classical.choice`,
  `Quot.sound` only.
* olean: `.lake/build/lib/lean/tmp/sheaf/xif/paper/S1920PaperFaithfulXiFActual.olean`,
  114104 bytes, SHA256
  `6CB770EEAAF65C973FECB0F2E3D7DF07EE4A68BF7497034F6CC8A9199C7AE099`
  (built with `lake env lean -o` into the Lake build tree; `lake build` does
  not accept `tmp.*` module targets).
* Consumer: `_S1920Consumer.lean` imports the olean and re-derives the scalar
  comparison, the ray membership and the link identification from
  `s1920_paperFaithful_xiF`; EXIT=0, axioms trio only.

## Reuse (nothing reproved)

* `s1880_xiF_inequality_abs`, `s1880_xiF_inequality_strict`,
  `s1880_abs_log_q_eq_magnitude` (S1880);
* `S1527C3_q`, `S1527C3_logVolume`, `S1527_origXiFScalarExactField` (S1527);
* `S1554_origXiFThetaLinkActual`, `S1554_signedHull_le`,
  `S1554_qPilotLogVolume_eq_neg_order_mul_log_five` (S1554);
* `S1895PaperO`, `s1895PaperO_qPilot_eq`, `s1895PaperO_identifications`,
  `s1895FirstMissing_impossible`, `s1895S1880_no_stripEquiv` (S1895);
* `OrigXiFThetaLinkIdentification_of_fields`, `OrigXiFThetaLinkRay_iff_le`,
  `OrigXiFPaperSignedHull`, `OrigXiFSignedThetaHullLogVolume` (tree).

## First missing / boundary

No missing object for this chain: the only inputs are the actual `D` and `D'`.
The paper Definition 3.1 clause supply `R` sits inside `S1895PaperInput`; it is
needed to *form* the input and its C3, but the xi-f scalar is
`-localLogMagnitude S1487Cand` and does not depend on `R`'s content (S1880
proved the analogous independence).  The S1880 carrier remains impossible
(cited above).  Not covered here: S1921 (q-pilot scalar equality) and the
S1927 frontier (full global log-Kummer / Frobenioid realization) recorded by
S1895.

## Axiom audit of the remaining declarations

`_S1920AxiomAudit.lean` (EXIT=0) additionally checks the five theorem
declarations not covered by the in-file probes -- `s1920PaperC3_q`,
`s1920PaperC3_logVolume_eq_neg_order_mul_log_five`,
`s1920_paper_linkIdentification_eq`, `s1920_paperIdentifications`,
`s1920_s1880_no_stripEquiv` -- all `propext`, `Classical.choice`,
`Quot.sound` only.  So all 22 theorem declarations of the module are
axiom-clean (`#print axioms`, no `sorryAx`).
