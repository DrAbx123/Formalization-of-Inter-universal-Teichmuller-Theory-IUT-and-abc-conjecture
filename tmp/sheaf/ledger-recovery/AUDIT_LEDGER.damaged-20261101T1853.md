# IUT audit ledger

This file records what was actually checked in this workspace. It is a scope
ledger, not a claim that IUT has been proved or refuted. Statuses mean:

- **proved**: Lean checked the statement without an IUT-specific premise being
  hidden in the proof;
- **interface**: Lean checked a theorem after a record/certificate containing
  the mathematical content was supplied;
- **claim only**: the code states the intended theorem or vocabulary, but does
  not prove its IUT-specific existence/construction;
- **not checked**: no local verification yet.

## 2026-08-06 C-layer boundary batch

The following bottom-up modules were added and checked in the production
aggregate:

- `Iut/Foundations/SourceTateStableGraph.lean` and
  `SourceTateStableGraphTransport.lean`: the one-component dual graph,
  compact graph with a marked open edge, and the concrete inclusion's proper,
  immersion, non-excision, injectivity, and non-surjectivity facts;
- `Iut/Foundations/SourceTateStableBoundary.lean`: a source-facing arithmetic
  boundary interface and comparison record, with no hidden realization field
  promoted to a theorem;
- `LeanFormal/IUT/Foundations/Geometry/GenericNodalReduction.lean` and
  `CanonicalNodalEquation.lean`: residue equation `y^2 + x*y = x^3`, tangent
  polynomial `T*(T+1)`, split roots, and normalization/recovery for the
  canonical `q = p` local carrier;
- `TateStableReductionBoundary.lean`, `CanonicalSourceTateBoundary.lean`, and
  `IUTI/InitialTheta/SplitReductionInput.lean`: assembly of the proved local
  boundary and the existing stable-reduction implication chain.

The aggregate `lake build LeanFormal` passed `3863/3863` with no diagnostics;
the complete log is `logs/lean/c-batch-final-20260806.log`.  The selected
axiom audit is `logs/lean/axiom-audit-final-20260806.log`: the only production
`sorryAx` remains the explicitly registered
`LeanFormal.IUT.theorem311_produces_stepXI_contract`.  This batch adds no
custom `axiom`, `opaque`, or `sorry` declaration.

The boundary check itself passed with `sorryAxLines = 1` in
`logs/lean/check-axiom-boundary-final-20260806.log`; the production
`axiom/opaque` scan reports `customAxiomDeclarations = 0` in
`logs/lean/custom-axiom-scan-final-20260806.log`.

This closes a concrete local Tate/stable-boundary subtarget, not C as a whole.
It does not identify an arbitrary number-field elliptic curve with the
canonical `q = p` curve, select the paper's required bad place, construct Tate
analytic uniformization or point-level Galois equivariance, or realize the
source tame anabelioid/theta-link data.  Consequently D/E remain interfaces at
their IUT-specific inputs.

## 2026-08-07 concrete local certificate batch

`LeanFormal/IUT/Foundations/Geometry/ConcreteSplitMultiplicativeCurve.lean`
and `ConcreteSplitCurvePadic.lean` now provide a second, independently
checked local carrier: the explicit equation `y^2 + x*y = x^3 + 5` over `Q`
and its actual base change to `Q_5`/`Z_5`.  The local file proves the exact
coefficients, nonzero discriminant, ellipticity, integrality, minimality,
multiplicative and split multiplicative reduction, nodal reduction equation,
split tangent polynomial (including monicity and degree), and normalization
recovery away from the node.  `ConcreteSplitCurveLocalCertificate` packages
these facts only after each field is populated by a proved theorem.

The production aggregate `lake build LeanFormal` passed `3865/3865` with no
warnings; the complete output is
`logs/lean/c-concrete-split-certificate-20260807.log`.  The endpoint audit is
`logs/lean/axiom-audit-concrete-split-20260807.log`: the new certificate uses
only `propext`, `Classical.choice`, and `Quot.sound`, and the sole production
`sorryAx` remains `LeanFormal.IUT.theorem311_produces_stepXI_contract`.
This batch still does not identify a general number-field curve with this
carrier, select the paper's bad place, construct Tate analytic
uniformization, or prove source-faithful initial-theta/Hodge-theater links.

## 2026-08-07 rational finite-place bridge batch

`LeanFormal/IUT/Foundations/Geometry/ConcreteSplitCurveFivePlace.lean`
constructs the finite place of `Q` corresponding to 5 from
`Rat.HeightOneSpectrum.primesEquiv`, rather than treating 5 as an informal
label.  Mathlib's actual continuous algebra equivalences between `Q_5` and
the selected adic completion, and between `Z_5` and its completion integers,
are used to prove that the global rational curve base-changes to the explicit
local equation and that split multiplicative reduction transports to the
completion carrier.  The bundled certificate has no `sorry`, `axiom`, or
`opaque` declaration.

The aggregate `lake build LeanFormal` passed `3866/3866` with no warnings;
the final transport log is `logs/lean/c-five-place-transport-20260807.log`,
and the endpoint axiom audit is
`logs/lean/axiom-audit-five-place-transport-20260807.log`.  A generic
dependent-type transport lemma now resolves Mathlib's chosen `maximalIdeal`
witness, so the global punctured curve's source-facing
`HasSplitMultiplicativeReductionAt` and stable-reduction predicates are
proved at the selected place.  Tate analytic point uniformization, Galois
equivariance, and source-faithful theta/Hodge links remain open.

## 2026-08-07 polymorphic quotient and Tate-boundary batch

The reusable algebra layer now has three deliberately polymorphic modules:
`Foundations/Algebra/CyclicQuotient.lean` abstracts the `g^Z` quotient over
any commutative group and proves representative, power, descent, and
surjectivity laws; `FiniteCyclicQuotient.lean` abstracts finite additive
quotients over any additive commutative group and specializes the integer
kernel certificate; `FiniteCyclicQuotientTransport.lean` transports such
quotients through a commuting carrier/label square.  These APIs are intended
for reuse by Kummer packets, prime strips, and theta links, so no separate
copy of the same quotient proof is introduced for each carrier.

`Foundations/Geometry/TatePointQuotientBoundary.lean` retains only the
source-faithful point comparison record, its injectivity/surjectivity and
Galois quotient naturality, and the constructor assembling it with the
coordinate comparison into `CurveIndexedTateUniformization`.  Redundant
q-unit wrapper lemmas were removed; the already proved deck quotient module is
used directly.  `IUTI/InitialTheta/TateComparisonBoundary.lean` and
`SourceLocalTateBoundary.lean` compose these records with dependent
finite-place/q data and expose finite-level transport projections.

The production aggregate `lake build LeanFormal` passed `3883` jobs with empty
stderr.  The final style-clean build logs are
`logs/lean/c-layer-polymorphic-batch-20260807-final2.stdout.log` and
`logs/lean/c-layer-polymorphic-batch-20260807-final2.stderr.log` (the preceding
full run is retained as `...final.stdout.log`).  The expanded
endpoint audit passed at
`logs/lean/axioms-20260807-071544/axiom_audit.stdout.log`; the strict boundary
rerun is `logs/lean/axioms-20260807-071608/axiom_audit.stdout.log` with exactly
one permitted `sorryAx`,
`LeanFormal.IUT.theorem311_produces_stepXI_contract`.  All new sampled
quotient, transport, and Tate-boundary declarations use only
`propext`, `Classical.choice`, and `Quot.sound`; the custom declaration scan
is `logs/lean/custom-axiom-20260807-polymorphic.log` and reports zero.

This batch proves reusable algebraic infrastructure and checks the exact
typed boundary.  It does not construct the analytic Tate point comparison or
source-faithful Initial-Theta existence, so it does not close C and cannot be
consumed as a completed input for D/E.

## 2026-08-07 concrete finite Theorem 3.11 model batch

`LeanFormal/IUT/IUTIII/Theorem311/ConcreteFiniteModel.lean` ports the useful
finite part of the public Stage-1 construction onto the project's own proved
C-stage carrier.  Its `ProcessionChoice` has two `ZMod l` translation
coordinates and one `Nat` upper-semi level.  The file proves the identity,
composition, inverse, cancellation, and mutual-commutation laws for the first
two actions; reflexive/transitive reachability for all three layers; and the
invariance/monotonicity of the concrete theta log-volume.  It also constructs
the singleton possible-image correspondence, proves its upper-semi law, and
reuses the actual finite Kummer quotient, compatible roots, q-deck action, and
positive theta-packet determinant/log-volume identities.

The standalone compile log is
`logs/lean/concrete-theorem311-finite-model-standalone-r4.log`; the production
build is `logs/lean/concrete-theorem311-finite-model-project-20260807.log`
(`3884/3884`, zero diagnostics).  The expanded endpoint audit is recorded in
`logs/lean/axioms-20260807-073811/axiom_audit.stdout.log` through
`logs/lean/concrete-theorem311-finite-model-axiom-boundary-20260807-r2.log`.
The new declarations use only the standard `propext`, `Classical.choice`, and
`Quot.sound` foundations; the permitted production `sorryAx` remains solely
`LeanFormal.IUT.theorem311_produces_stepXI_contract`.  The custom declaration
scan remains zero.

This is an explicitly labelled finite model boundary, not a proof of the
paper's arbitrary procession of D-prime-strips, distinct Hodge theaters,
source log-Kummer correspondence, or the full multiradial algorithm.  In
particular it does not discharge `(Ind1)`, `(Ind2)`, `(Ind3)` in the source
setting and does not remove the Step-XI contract boundary.  It is useful as a
reusable test carrier for those future source-faithful constructions without
duplicating quotient/action code.

## Source snapshot

The source page was saved as `tmp/motizuki-papers-japanese.html` on 2026-08-02.
The selected original papers were downloaded from that page into
`tmp/motizuki/`; SHA-256 hashes are kept here so that later re-checks use the
same documents:

| source | SHA-256 (prefix) |
|---|---|
| IUT I | `7360E3ED27C235B5...` |
| IUT II | `180BFA6AADDC4AE3...` |
| IUT III | `9A7EE3C77B1C7717...` |
| IUT IV | `5BF4B1E0A8C26865...` |
| Panoramic Overview | `EB42575F73D69D1F...` |
| Essential Logical Structure | `C0E63B629AA174AA...` |
| Explicit estimates | `4CACCE3F1085C4F5...` |

The relevant text was extracted with `pypdf` (the PDF skill workflow) into
`tmp/motizuki/iut-iii-full.txt`, `tmp/motizuki/iut-iii-proof-3-12.txt`, and
`tmp/motizuki/iut-iv-intro.txt`. The page numbers below are PDF page numbers
and also show the printed page in the extracted text.

On 2026-08-04 the source layer was made reproducible and page-delimited with
`tools/extract_pdf_pages_text.py`. Search-oriented `plain` text and
placement-oriented `layout` text now cover both complete source PDFs, with
a continuous IUT III Theorem 3.11-to-Corollary 3.12 working text
(pp. 153--186, including the intervening Remarks 3.11.1--3.11.4), the earlier
shorter theorem/proof extract, and the semi-graph foundations (pp. 11--12, 20,
37--40). The source workflow uses the text layer first and returns to a rendered
page only for extraction conflicts, blocked typing/proof directions, or final
source-credit review. Exact hashes, extraction limitations, manually confirmed
formula directions, and the initial upstream/source classification are in
`papers/motizuki_corpus/SOURCE_TEXT_AUDIT.md`. Machine-extracted glyphs remain
an index rather than mathematical evidence on their own.

## Complete author-site corpus and citation map

The author-site crawl now lives under `papers/motizuki_corpus/`. It fetched the
eight entry pages (`papers-japanese.html`, `top-japanese.html`, CV, students,
thoughts, news, research, and travel), found 263 unique PDF links, and saved
262 files with SHA-256 hashes. One external link,
`~yuichiro/absolute_anabelian_cuspidalizations.pdf`, returned a confirmed 404
and is retained as a missing row in `pdfs.csv`; it is not silently omitted.
The downloaded corpus is about 644 MB and includes papers, comments, LaTeX
versions, lecture notes, and dated talk/slide PDFs linked from the site.

The bundled PDF workflow extracted 262 PDFs into `papers/motizuki_corpus/text/`
(8197 pages, about 14.8 million characters). The citation pass produced:

- `citation_edges.tsv`: 478 resolved label-to-file candidate edges;
- `reference_snippets.tsv`: 1449 bibliography snippets for manual review;
- `unresolved_reference_labels.tsv`: 112 unresolved historical labels;
- `DEPENDENCY_LAYERS.md`: the source-backed bottom-up layer plan.

The edges are evidence for reading order, not a proof of mathematical
dependency. In particular, the Tan introduction explicitly says to treat
anabelian/Frobenioid theory as prior material, read `EtTh` Sections 1--2, then
IUT I/II, and read IUT III carefully; IUT IV Section 1 can be read alongside
IUT III. This is now the basis for the Lean directory order.

## What the original papers require

1. **IUT I-II (prerequisites):** initial Theta data, distinct Hodge-theater
   histories, prime strips, Hodge-Arakelov theta evaluation, Gaussian/LGP
   monoids, and the Kummer/coric infrastructure. No local Lean project here
   constructs these objects from an elliptic curve and its number field.
2. **IUT III, Theorem 3.11:** a multiradial output consisting of tensor packets
   of log-shells, splitting monoids, and labelled copies of `F_mod`, with
   `(Ind1)`, `(Ind2)`, `(Ind3)` and the stated Kummer/link compatibilities.
3. **IUT III, Corollary 3.12:** the disputed final passage is explicit in the
   proof, especially PDF pages 174--184 (printed pp. 174--184):
   `IPL` links the output to the q-pilot prime strip; `SHE` says the output is
   expressible in the fixed 1-column arithmetic holomorphic structure;
   `APT` justifies the algorithmic transport; the holomorphic hull and
   log-volume then yield `-|log(q)| in R_{<= -|log(Theta)|}`. This is the
   logical wall. It is not just a numerical `j^2` calculation.
4. **IUT IV:** its abstract theorem (PDF pp. 1--3) and the Section 1/2
   estimates use IUT III Corollary 3.12 (e.g. the explicit final step on PDF
   p. 31 and the discussion beginning p. 40). Thus an IUT IV numerical proof
   cannot close the earlier wall by itself.

The LANA interim report (`papers/LANA_report_202607.pdf`, extracted in
`tmp/pdfs/lana.txt`) independently describes the same remaining obligation:
the q-pilot-native construction must be compatible with the multiradial/
Kummer construction after Ind1--3; its abstract (PDF p. 1) says the proof has
not been reconstructed, and pp. 4--6 call this diagram-commutativity/
identity issue the ``wall``. This is a status report, not a verdict.

## Local Lean checks

### Minimal diagnostic model (this workspace)

| file | status | checked fact | limitation |
|---|---|---|---|
| `LeanFormal/IUTDispute.lean` | **proved** | In a same ordered space, monotonicity makes the comparison tautological; with `q < 0`, `factor > 1`, `theta = factor*q`, a tight-hull premise `q <= hull <= theta` is inconsistent; a slack witness satisfies the receiver/common-container shape while violating tightness. | This is an order-theoretic diagnostic. It does not define Hodge theaters, Kummer maps, or the source of the premises. |
| `LeanFormal/Archive/AnalysisExercise/Basic.lean` | **archived** (separate analysis exercise) | A real-analysis limit problem is fully checked and is unrelated to IUT. | It is outside the production entry point and must not be counted as IUT progress. |

The diagnostic therefore supports only: **the dispute is a missing/contested
identification or compatibility premise, not an arithmetic contradiction in the
abstract inequality.** It does not decide which side is mathematically right.

### Project hierarchy and proof boundary

The local project is now organized into deep, source-oriented modules rather
than one flat `IUT` directory. `LeanFormal/IUT/Project.lean` is the aggregate
entry point. The current hierarchy is:

- `Audit`: source hashes, status vocabulary, and obligation metadata;
- `Foundations/Arithmetic`, `Theta`, `Coordinates`, and `Volumes`: standard
  algebra, the square-exponent theta kernel and finite square-sum normalization, labelled real coordinates, and
  finite weighted-average lemmas;
- `IUTI/InitialTheta`, `IUTI/HodgeTheater`, `IUTII/Frobenioid`, and
  `IUTII/Kummer`:
  source obligations for the IUT I--II constructions;
- `Theorem311/Output` and `Theorem311/Indeterminacy/Ind1--Ind3`:
  Theorem 3.11 obligations plus the generic `Setoid`/`Quotient` transport
  kernel;
- `Corollary312/StepXI/IPL`, `SHE`, `APT`, and
  `HolomorphicHull/Volume`, `FiniteCertificateBridge`: the exact disputed wall;
- `ABCBridge/Statement`, `ABCBridge/UnprovedTarget`, and `ABCBridge/Bridge`: the standard ABC
  proposition, its explicit unfinished proof target, and the eventual bridge.

The following distinction is enforced in code:

| layer | current status | meaning |
|---|---|---|
| `Foundations/Arithmetic/FiniteLabels` | **proved** | `F_l = ZMod l`, prime/odd cardinality, sign involution, and the `{+/-1}` quotient are standard Mathlib constructions; the serial log and batch build contain no `sorryAx`. |
| `Foundations/Theta/GaussianKernel` | **proved** | Integer `j^2` symmetry, monoid special values, and the real logarithm lemma; this is only the algebraic kernel, not an etale theta function. |
| `Foundations/Theta/GaussianSquareSum` | **proved** | The finite `∑ j^2` closed form and the odd-label normalized factor `l(l+1)/12` are proved over `Real`; no theta function or IUT volume map is introduced. |
| `Foundations/Coordinates/RealLineTransport` | **proved** | Explicit positive-scale transports between copies of `Real`; equality is never silently identified across labels. `RealTransport.log_map` also proves the logarithmic additivity law for positive coordinates using Mathlib's `Real.log_mul`. |
| `IUTI/InitialTheta/ArithmeticData` | **interface with proved projections** | The IUT I arithmetic input is represented using Mathlib number fields, Galois/finite-dimensional field towers, `HasSqrtNegOne`, and Weierstrass elliptic curves with a puncture. The record is not an existence theorem and does not include the unconstructed reduction/anabelian/torsion data. |
| `Foundations/NumberField/FinitePlaceExtension` | **proved** | For a finite place above its contraction, the height-one prime is proved to lie over the lower prime; Mathlib's ramification theorem gives the valuation formula and uniform continuity on the dense valued fields. The induced map between actual adic completions is continuous and injective. Density and continuity extend the ramification formula to every completed element. The map restricts to an injective local homomorphism of completed valuation rings and induces an injective residue-field map. Tate uniformization is not inferred. |
| `Foundations/Geometry/ReductionBaseChange` | **proved** | Integral Weierstrass models map through commuting coefficient-ring/field squares. Integral equations with discriminant valuation one or unit `c4` are proved minimal. Good and multiplicative reduction are transported through the completion map; split multiplicative reduction is transported by the actual residue-field embedding and `Polynomial.Splits.map`. These are conditional preservation theorems, not proofs that the IUT input curve has the required reduction at any place. |
| `Foundations/Volumes/WeightedVolume` | **proved** | Finite weighted-average inequalities from ordinary ordered-field arithmetic. The file uses a minimal Mathlib import set; no local replacement for finite-sum machinery is introduced. |
| `IUTI/InitialTheta`, `IUTI/HodgeTheater`, `IUTII/Frobenioid`, `IUTII/Kummer` | **mixed: 50 proved units / 6 interface / 4 pending source obligations** | The project now contains real arithmetic, the Frobenioids I Theorem 5.2 model category, its Proposition 4.4 Hom-colimit birationalization and `O^times ~= B` naturality, the objectwise zero-divisor `O^triangle`/effective-rational-function equivalence, the finite-place MLF integral monoid and its sequential ind-topological reconstruction, the full Proposition 2.2 `D*` functor, generic universal-pro-object evaluation, torsion-cyclotomic and Kummer kernels, theta quotients, and prime-strip kernels. It still does not construct the paper's actual MLF/CAF Frobenioid and identify its categorical evaluation with the reconstructed local integral carrier, or construct complete initial theta data, Hodge theaters, theta-links, and log-links. The four source-specific obligations remain pending; work-weighted C-layer completion is conservatively approximately 59--61%, not the ratio of compiled files. |
| `IUTII/Frobenioid/PrimeStripArithmetic` | **proved arithmetic kernel** | Finite interval prime-index set, primality projection, and interval monotonicity are proved with Mathlib's finite-order API; this is not an IUT Frobenioid prime strip. |
| `IUTII/Frobenioid/PrimeStripDegree` | **proved arithmetic kernel** | A finite family of ordinary commutative value monoids with official `MonoidHom` degree maps into `Multiplicative ℝ`; local multiplication and finite global degree additivity are proved. The data are not claimed to be an etale/Frobenioid realization. |
| `IUTI/HodgeTheater/PrimeStripCore` | **proved source-data kernel / realization pending** | `DPrimeStrip` and `FPrimeStrip` use Mathlib groups, surjective `MonoidHom`s, `Subgroup.ker`, `MulAut` actions, and the proved degree kernel. Forgetful maps, geometric kernels, action laws, and global degree laws compile and are axiom-audited; no arithmetic-geometric existence theorem is asserted. |
| `IUTI/HodgeTheater/HodgeTheaterCore` | **interface with proved link algebra** | A source-facing theater carries explicit initial arithmetic data, a concrete F-prime-strip carrier, and a finite theta packet. Prime-strip equivalence, theta-q/scale alignment, symmetry, composition, and three-theater source-to-target transport are proved. Existence of the paper's theaters, histories, anabelian reconstruction, and Hodge-Arakelov compatibility remain pending. |
| `IUTI/HodgeTheater/LocalPrimePlaces` | **proved local carrier kernel / realization pending** | Rational-prime labels, finite prime-interval labels, `ℚ_[p]`, algebraic-closure absolute Galois groups, the induced action on local units, and a nontrivial local q-parameter use Mathlib definitions. The projection is intentionally the identity because the etale fundamental-group quotient is not yet constructed. |
| `IUTII/Kummer/TimesMuQuotient` | **proved algebraic quotient/action kernel / IUT identification pending** | For an actual commutative unit group, the quotient by the full torsion subgroup, its canonical map and kernel, descended automorphism action, equivariance, action laws, and torsion-freeness are proved. The `FPrimeStrip` bridge uses the canonical unit group `(F.Mon v)ˣ`; no ind-topology or group/Frobenioid Kummer comparison is asserted. |
| `IUTII/Kummer/TimesMuIsm` | **proved conditional Ism/orbit kernel / representative existence pending** | Open-subgroup fixed units, invariant images modulo torsion, the exact equivariant/image-preserving Ism subgroup, compatible isomorphisms, their Ism action, and uniqueness of the resulting orbit are constructed and proved. Lean constructs the identity representative for one action but does not assert that the paper's distinct group-theoretic and Frobenioid actions admit a compatible representative. |
| `IUTII/Kummer/LocalFieldRigidity` | **proved local-field `G_m` rigidity / broader Kummer faithfulness pending** | Residual-finiteness root rigidity, profiniteness of valuation-ring units, triviality of a local-field unit with roots of every positive degree, and injectivity from the standard multiplicative Kummer-kernel characterization are proved. Arbitrary-torus and semi-abelian Kummer faithfulness are not claimed. |
| `Iut/Foundations/ContinuousH1` | **proved continuous-cohomology kernel** | Continuous nonabelian `H^1`, restriction, open-subgroup germ representatives, coboundary equivalence, and the abelian germ group laws are constructed. This is an exact upstream port except for removal of one unused broad import; it does not supply an IUT arithmetic action. |
| `IUTII/Kummer/RationalRootSystem` | **proved compatible-root kernel** | A single compatible rational-power homomorphism is obtained by extending `Z -> B` across `Z -> Q` using injectivity of divisible abelian groups. Algebraically closed field units instantiate it; unrelated choices for each degree are not used. |
| `IUTII/Kummer/ContinuousKummerGerm` | **proved one-unit continuous Kummer germ / global and Frobenioid comparison pending** | For an open-subgroup-fixed unit, compatible rational roots produce a continuous crossed homomorphism into the genuine cyclotome `Hom(Q/Z,B)`, a local continuous `H^1` class, and a germ. Changing the root system is proved to be an explicit coboundary. A homomorphism on all units, local absolute Galois continuity, Frobenioid evaluation, and the group/Frobenioid comparison remain pending. |
| `IUTII/Kummer/CanonicalKummerMap` | **proved group-side Kummer homomorphism / local arithmetic instantiation pending** | Every element of a divisible commutative discrete coefficient group has an open stabilizer. On intersections of stabilizers, product root systems prove the germ multiplication law, and the canonical map `B ->* H1_germ` is constructed. The local absolute Galois action, Frobenioid evaluation, and the Definition 4.9 group/Frobenioid comparison remain pending. |
| `IUTII/Kummer/LocalGaloisKummerAction` | **proved discrete local Galois action / ind-topological and Frobenioid realization pending** | For `Gal(Qbar_p/Q_p)` with its Krull topology and an explicitly declared discrete topology on algebraic-closure units, the unit stabilizer is identified with the field stabilizer and proved open from integrality. This yields a genuine continuous action and local group-side Kummer homomorphism. It is not the source's ind-topological integral monoid or Frobenioid evaluation. |
| `IUTII/Frobenioid/LocalTorsionCyclotome` | **proved local torsion-cyclotomic/rootability construction** | Lean proves the multiplicative rational circle `Q/Z` equivalent to all roots of unity in an algebraic closure of a characteristic-zero field, composes this with the proved integral-unit torsion equivalence, and transports algebraic-closure divisibility to `RootableBy Nat` on the actual local Grothendieck groupification. No cyclotomic structure is accepted as a field or premise. |
| `IUTII/Frobenioid/LocalMLFTMPair` | **proved canonical mono-analytic MLF `TM` model / Frobenioid comparison pending** | The acting group is the actual Krull-topological `Gal(Qbar_p/Q_p)`, the augmentation is the continuous identity surjection, and the arithmetic monoid/action are the proved local integral model. Pullbacks of genuine Krull-open stabilizers are proved to fix their elements. Unit and `times-mu` actions feed the existing Ism kernel, but no distinct group/Frobenioid comparison is asserted. |
| `IUTII/Frobenioid/LocalGroupificationAction` | **proved discrete continuous groupification action** | The local integral-monoid action is extended through the Grothendieck-group universal property. Its stabilizer is pulled back from the genuine Krull-open stabilizer of the corresponding algebraic-closure unit. The unit embedding is proved injective and equivariant, and the groupification equivalence is proved equivariant with the actual algebraic-closure action. This is not a Frobenioid evaluation or the source's unit-valued Kummer comparison. |
| `IUTII/Frobenioid/LocalIntegralUnitKummer` | **proved integral-unit root realization / Frobenioid comparison pending** | Compatible rational roots in the actual local Grothendieck group are used to prove every Galois root ratio is torsion, lift it uniquely to an integral unit, and construct the resulting unit-valued `Q/Z` cyclotome, continuous crossed cocycle, and `H^1` germ. No Kummer comparison is assumed as data. |
| `IUTII/Frobenioid/LocalUnitKummerMap` | **proved canonical unit Kummer homomorphism / Frobenioid comparison pending** | Any two compatible-root choices are proved to differ by an explicit coboundary. Product root realizations prove multiplication of germs, yielding a genuine monoid homomorphism from local integral units. This still supplies only the group-side map. |
| `IUTII/Frobenioid/LocalUnitKummerInjectivity` | **proved mono-analytic injectivity / Definition 4.9 comparison pending** | A trivial germ yields roots of every positive degree fixed by one open subgroup. The fixed field is finite over `Q_p`; its integral-closure unit group is residually finite, using an explicit equivalence between the canonical valuation ring and `Z_p`. Hence the constructed mono-analytic integral-unit Kummer homomorphism is injective. Frobenioid-side evaluation and the group/Frobenioid comparison are not asserted. |
| `IUTII/Frobenioid/LocalMLFPrimeStripBridge` | **proved definitional compatibility / categorical Frobenioid evaluation pending** | The integral F-prime-strip value object was corrected from `(LocalIntegralMonoid p)^x` to `LocalIntegralMonoid p`, so the generic Kummer layer takes units exactly once. Its monoid, unit, and `times-mu` actions are then proved by `rfl` to be the canonical local MLF `TM` actions. This is not yet the universal-cover Frobenioid evaluation functor. |
| `IUTII/Frobenioid/LocalIntegralUnitEvaluationImage` | **proved exact arithmetic evaluation image / categorical-local identification pending** | The integral-unit evaluation has exactly the algebraic-closure units whose value and inverse are integral. The induced equivalence is proved compatible with the natural Galois action, descends through the full torsion quotient, and maps every open-subgroup invariant image exactly onto its counterpart, yielding a real carrier-level `Ism` orbit. The generic categorical `O^triangle(A)` now exists separately, but no theorem yet identifies it with this local carrier for an actual MLF Frobenioid or supplies the source's ind-topology. |
| `Iut/Foundations/SourceFrobenioidRationalMonoidTransport` | **proved restricted Frobenioids I Proposition 2.2(ii),(iv) transport kernel** | From the existing `FrobenioidPresentation.axioms`, Lean constructs contravariant pullback on the actual base-identity linear endomorphism monoids along linear arrows between isotropic objects, proves identity and composition on `(C^istr)^lin`, and constructs the injective isotropic-hull extension. The production file is byte-identical to `promachina/iut-lean@5e70fbe9`; no recognition/existence wrapper or new Frobenioid axiom is introduced. The extension to every arrow of `D*`/`D`, the universal-cover pro-object, and the IUT II Definition 4.9 evaluation remain separate obligations. |
| `Iut/Foundations/SourceFrobenioidIsotropicBase` | **proved Frobenioids I Proposition 2.2(i)** | Lean defines the paper's category `D*` with isotropic Frobenioid objects and base-category homs, then proves its tautological projection to `D` faithful and full. Essential surjectivity is constructed from Definition 1.3(i)(a) and an isotropic hull, yielding an actual `D* ≃ D`. The subsequent modules now extend `O^triangle` to all `D*` arrows and evaluate it on the standard pointed-Galois pro-presentation. |
| `Iut/Foundations/SourceFrobenioidCoAngularBaseChange` | **proved Proposition 2.2(ii) base-isomorphism transport** | From Definition 1.3(i)(b), isotropic hulls, and the proved Proposition 1.4/1.9 lemmas, Lean constructs an isotropic common midpoint with co-angular pre-steps over any prescribed base isomorphism. The resulting rational-monoid equivalence is proved independent of the common witness and satisfies identity, inverse, and composition laws; it is used by the completed arbitrary-base-arrow transport. |
| `Iut/Foundations/SourceFrobenioidBasePullbackLift` | **proved full Frobenioids I Proposition 2.2(ii) functor on `D*`** | Definition 1.3(i)(c) lifts every base arrow between isotropic objects to an actual pullback arrow after a source base isomorphism. Lean proves the lifted source isotropic, representative independence, source/target isomorphism naturality, the mixed pullback/pre-step squares, and identity and composition laws for arbitrary base arrows. These results package into the genuine contravariant functor `(D*)^op -> MonCat`; no recognition record or selected candidate is used. |
| `Iut/Foundations/SourceFrobenioidUniversalProEvaluation` | **proved generic IUT II Definition 4.9(i) categorical evaluation and action** | For a Galois structure and fiber functor on `D*`, Mathlib's pointed Galois objects give the cofiltered pro-representing system. Lean applies the proved `O^triangle` functor to the opposite system, takes its actual `MonCat` colimit, constructs the inverse-limit Galois action, and proves on every finite-level representative that the action is pullback along the inverse automorphism. An actual MLF/CAF Frobenioid, its Galois-category instance, the comparison with `LocalIntegralMonoid`, and the ind-topology remain pending. |
| `Iut/Foundations/SourceModelFrobenioid*` | **proved Frobenioids I Theorem 5.2 model chain** | The seven-file chain constructs the model category, divisor order, factorization and uniqueness, pre-step factorization, every Definition 1.3 axiom group, and the final `FrobenioidPresentation`. The input supplies only the rational-function additive group, divisor homomorphism, and naturality; the Frobenioid conclusion is not an input field. Six files are byte-identical to the fixed public snapshot and one has two explicit Lean 4.32.2 object annotations. |
| `SourceFrobenioidModelType`, `SourceModelFrobenioidBirational*`, `SourceModelFrobenioidColimit*`, and `SourceModelFrobenioidRationalNaturality` | **proved Frobenioids I Proposition 4.4/Theorem 5.2 birational chain** | The actual filtered Hom-colimit, fully faithful comparison with the concrete birational model, seven Definition 1.3 axiom groups, full Frobenioid presentation, rational-function natural isomorphism, unit restriction, and `DivB` compatibility are constructed. Eight files are content-identical to `promachina/iut-lean@0d52e0fd` after end-of-line normalization. The other three contain only Lean 4.32.2/linter migrations: unused simp arguments removed, Prop-valued `def`s changed to `theorem`s, and one explicit projection `change`; the propositions, hypotheses, and proof arguments are unchanged. This identifies the group-like birational `O^times`, not the integral monoid of IUT II Definition 4.9. |
| `Iut/Foundations/SourceModelFrobenioidZeroEvaluation` | **proved objectwise integral evaluation kernel / finite-stage comparison proved separately** | At the zero-divisor object of the actual model Frobenioid, Lean constructs a multiplicative equivalence between `O^triangle` and rational functions whose divisor lies in the effective monoid. Surjectivity is obtained from an explicit model arrow satisfying the original balance equation; no supplied recognition or existence field is used. Finite-stage divisor-effectivity versus local valuation-integrality is now proved in `SourceFiniteStageValuationDivisor`; the actual finite-stage ramification transitions, filtered-colimit evaluation comparison, Galois action, ind-topology, groupification, and Kummer compatibility remain pending. |
| `Iut/Foundations/SourceModelFrobenioidIntegralNaturality` | **proved natural integral-evaluation comparison for every model base arrow** | The zero-divisor section is constructed as a functor. Its transported `O^triangle` monoids and the effective rational-function submonoids are contravariant functors on the full base category, and Lean constructs a natural isomorphism between them. Effectivity under pullback follows from the original divisor naturality and `gpPullback_of`; no transition or recognition field is added. Specializing this generic theorem to the finite Galois stages still requires their genuine ramification-weighted divisor pullbacks. |
| `Iut/Foundations/SourceFiniteStageDivisorTransition` | **proved genuine finite-stage value-group and divisor transition system** | For every finite-stage inclusion, Mathlib's `ValuativeExtension.mapValueGroupWithZero` is conjugated through the independently chosen `ValueGroupWithZero ≃*o ℤᵐ⁰` normalizations. The resulting additive `ℤ` map is proved strictly monotone, equal to multiplication by a positive ramification index, and natural for units; the induced `ℕ` divisor pullbacks are injective and satisfy identity/composition. No compatibility of noncanonical stage normalizations is assumed. |
| `Iut/Foundations/SourceFiniteStageModelFrobenioid` | **proved finite-stage model Frobenioid input** | The opposite finite-stage category carries a universe-correct sharp, integral, saturated divisor monoid (`ULift ℕ`), ramification-weighted pullbacks, and the additive group of nonzero stage elements. The model `Input` and its `divisor_natural` field are constructed and proved from the transition theorem and the Grothendieck-group pullback calculation. This is the actual finite-stage carrier/input; the categorical universal-pro evaluation and its identification with `O^triangle` remain pending. |
| `Iut/Foundations/SourceFiniteStageModelEvaluation` | **proved finite-stage `O^triangle` identification, naturality, and reconstructed ind-colimit** | For the zero-divisor object of the finite-stage model, the generic effective rational-function submonoid is proved equal to the normalized-valuation nonnegative submonoid. An explicit multiplicative equivalence identifies the model `O^triangle` zero-object endomorphisms with the actual nonzero integral stage monoid, and its effective-side map is proved natural for every genuine stage transition. The stage integral `MonCat` filtered colimit is constructed and proved multiplicatively equivalent to the exhaustive `IndIntegralMonoid`. The proof uses the genuine Grothendieck-group equivalence, valuation/integrality theorem, actual `stageIntegralTransition`, and Mathlib filtered representative relation; it does not assert the categorical MLF/CAF `O^triangle` realization. |
| `Iut/Foundations/SourceMLFIntegralMonoid` and `IUTII/Frobenioid/MLFIntegralMonoidComparison` | **proved arithmetic monoid, groupification, and local comparison** | For an actual valued field, Lean uses the integral closure in its algebraic closure, removes zero, constructs the absolute Galois action, proves the fraction-field property, and identifies the Grothendieck group with algebraic-closure units. The existing `LocalIntegralMonoid p` is proved equivalent, including inclusion, groupification, and Galois action. This is an arithmetic carrier comparison, not yet a Frobenioid evaluation comparison. |
| `Iut/Foundations/SourceFinitePlaceMLFBase` | **proved finite-place local-field base / packaging only for the ind-colimit record** | The actual completion map `Q_p -> K_v`, continuity, scalar tower, finite dimensionality, nontrivial norm, characteristic zero, valuative relation, second countability, and rational local compactness are constructed from Mathlib and the existing finite-place extension theorem. `SourceFiniteIndTopologicalLocalModule` only packages a filtered topological-module cocone; existence for the required system is supplied by the following reconstruction, not assumed here. |
| `Iut/Foundations/SourceDefinition52LocalReconstruction` through `SourceDefinition52Sequential` | **proved IUT I Definition 5.2(v) finite-place reconstruction** | Finite Galois intermediate fields form the filtered stages; their module colimit is proved equivalent to the algebraic closure. Nonzero integral stage monoids exhaust the local integral monoid, transitions and the Krull action are continuous and equivariant, and a natural-number-indexed cofinal subsystem is constructed from countably many global-polynomial root witnesses. No candidate-existence record is used. The separate categorical identification with `O^triangle(A)` for an actual MLF/CAF Frobenioid remains pending. |
| `Iut/Foundations/SourceFiniteStageValuationDivisor` | **proved finite-stage valuation/divisor comparison** | Every finite Galois reconstruction stage is proved to be a nonarchimedean local field with value group `WithZero (Multiplicative Int)`. Lean constructs the normalized additive valuation, the genuine sharp saturated divisor monoid `Nat`, proves base-ring integrality iff the stage valuation is at most one by a minpoly/spectral-norm argument in both directions, and obtains a multiplicative equivalence between effective nonzero rational functions and `StageIntegralMonoid`. The stage integral monoid itself is not mislabeled as a sharp divisor monoid. |
| `Iut/Foundations/SourceTopologicalMonoidPresentation` | **data structure with proved morphism laws** | This is the exact minimal package extracted from the public Hodge-theater source: a monoid with topology and continuous multiplication, continuous monoid homomorphisms, composition, identity, and extensionality. It proves the packaging laws but asserts no IUT object existence. |
| `IUTII/Theta/FiniteThetaPacket` | **proved concrete lower packet / IUT identification pending** | A finite interval subtype supplies the standard Mathlib `Fintype`; the Gaussian packet is positive, nonzero, sign-symmetric, and has a proved finite log-volume identity. This is a lower numerical packet, not yet the paper's etale theta or Hodge-Arakelov object. |
| `IUTII/Theta/EtaleThetaQuotient` | **proved algebraic lower-central kernel / geometric realization pending** | The lower-central theta quotient, elliptic abelianization, exponent-`l` power quotients, canonical surjections, and central theta kernel are constructed with Mathlib commutator/normal-closure/QuotientGroup APIs. Profinite closedness, etale fundamental groups, and the rank-two arithmetic identification remain explicit obligations. |
| `IUTIII/Theorem311/*` | **claim only / interface vocabulary, with a proved generic kernel** | Theorem 3.11 output and Ind1--3 are tracked as obligations, not derived from number-field or elliptic-curve data. `Indeterminacy/QuotientTransport` proves representative-independent transport for arbitrary Setoids, but supplies no IUT-specific carriers or relations. |
| `IUTIII/Theorem311/Indeterminacy/OrbitTransport` | **proved group-action kernel** | Equivariant maps descend through Mathlib's official `MulAction.orbitRel` quotient, and a three-layer orbit transport has a representative formula. This is the Ind1/Ind2 mechanism, not the IUT-specific Galois/Kummer construction. |
| `IUTIII/Theorem311/Indeterminacy/UpperSemi` | **proved order kernel** | Set-valued upper-semi correspondences, singleton monotone maps, and composition are proved over standard preorders; this captures the logical direction of Ind3 without supplying the paper's log-Kummer correspondence. |
| `Iut/Foundations/SourceTemperedDeck*` | **proved tempered-deck kernel / arithmetic realization pending** | The literal deck groups, refinement transitions, locally-surjective universal-tree lifting, finite bounded lift fibers, cofiltered compatible sections, and every raw/literal deck projection are constructed and proved. The chain has no `sorryAx`; it does not construct stable reduction, Andre exactness, an arithmetic tempered tower, IPL/SHE/APT, or the Theorem 3.11 output. |
| `Iut/Foundations/SourceTemperedGaloisSplitter` through `SourceTemperedGeometricDomination` | **proved alternative construction kernel / paper-object identity pending** | Lean constructs a pointed Galois splitter, local component maps, universal sheet lift, corrected target points, branch naturality, and a literal domination morphism. These declarations are usable proved mathematics with no `sorryAx`. Their proof architecture targets *Semi-graphs of Anabelioids*, Proposition 3.6(ii), but exact definition-by-definition identity or a proved equivalence with every paper object has not yet been audited; they are not counted as IUT III Theorem 3.11, Ind1--3, IPL/SHE/APT, or Corollary 3.12. |
| `Iut/Foundations/SourceTemperedActionFactorization` through `SourceTemperedActionCoverEquivalence` | **proved 26-module action-cover classification kernel / paper-object identity pending** | The fixed `promachina@c7c06e23` chain constructs orbit factorization, component families, literal tempered covers, finite and componentwise associated quotients, normalized universal-cover refinements, the action-cover functor, and its full/faithful instances. All 26 modules compile with zero diagnostics and the sampled endpoints have no `sorryAx`. Thirteen files are byte-identical and thirteen contain only audited Lean 4.32.2 proof migrations. This remains a proposed construction of the *Semi-graphs of Anabelioids*, Proposition 3.6(ii), mechanism; exact definition-by-definition identity with the paper is pending, and none of IUT III Theorem 3.11, Ind1--3, IPL/SHE/APT, Corollary 3.12, or ABC is thereby proved. |
| `IUT_SUBTARGETS.md` | **research-target registry** | Separates proved Lean kernels, source-faithful IUT obligations, and external open-problem candidates; no candidate is counted as proved by the current project. |
| `IUTIII/Corollary312/StepXI/*` | **interface plus one marked `sorry`** | `cor312_of_constructed_stepXI` and the ordered corridor are proved from a supplied contract; `theorem311_produces_stepXI_contract` is the sole `sorryAx` reachable from the production entry point. `HolomorphicHull/Volume` additionally proves finite positive-packet determinant, tensor-product, rescaling, log-volume, and weighted-hull identities using the official `Matrix.det`, `Matrix.det_diagonal`, and `Finset` APIs. It does not construct the paper's holomorphic hull, local/global tensor normalization, or q-pilot objects. |
| `IUTIII/Corollary312/StepXI/FiniteCertificateBridge` | **interface** | `FiniteStepXILinkEvidence` makes `targetSigned`, IPL/SHE/APT evidence, and both comparison bounds explicit; from those supplied fields, Lean constructs a `StepXIContract` and proves the ordered conclusion. It does not prove any of the supplied source-facing fields. |
| `IUTIII/Corollary312/Routes` | **three claimed routes recorded / all pending** | The source-labelled Mochizuki 3.11.5 reorganization, Joshi's arithmetic-Teichmuller/Rosetta-Stone route, and Sarkisyan's explicitly claimed Erdos--Kac route are separate typed tags and audit obligations. No preprint result is imported as an axiom, and no route certificate is constructed. |
| `ABCBridge/Statement` | **proved statement layer** | `ABCConjecture` is the standard epsilon/constant radical proposition; the radical lemmas are checked against Mathlib. This is not a proof of the conjecture. |
| `ABCBridge/UnprovedTarget` | **pending metadata only** | The former unused `abc_conjecture_target := by sorry` declaration was removed. The file now records the unproved ABC target without creating a Lean theorem or a second `sorryAx`. |
| `Audit/Status.Obligation` | **proved audit metadata** | Obligations now carry optional `dependsOn`, `externalAxioms`, and named `sorryItems` lists; defaults preserve existing source metadata while key pending boundaries populate the lists explicitly. |
| `tools/check_no_custom_axioms.ps1` | **passed audit gate** | Scans production `LeanFormal/IUT` source for top-level `axiom`/`opaque` declarations; current result is zero. This is separate from the allowed, explicitly isolated `sorryAx` boundary. |
| `papers/motizuki_corpus/UPSTREAM_REUSE.md` | **provenance register** | Fixed commits and source surfaces for promachina, Takkun, LANA, com-junkawasaki, and PriestAmbrose are recorded with `proved`/`interface`/`diagnostic`/`external-claim` labels. It is a bibliography and reuse policy, not a mathematical intermediary layer. |

There is no production compatibility layer. The only files outside the
source-oriented dependency tree are under `Audit/Diagnostics`; they are
quarantined experiments and are not imported by `Project.lean`. This prevents
an old placeholder interface from silently becoming a dependency of the new
formalization.

### Reproducible verification record (2026-08-02)

| check | result | evidence |
|---|---|---|
| Original-source text reproducibility | **passed** | `logs/source-audit/run-20260804-020842/summary.json`; both source SHA-256 values match, both full pagewise extracts have all physical page markers, and the focused source extracts have 21/21 and 7/7 markers. The log explicitly sets `mathematicalProofClaim` to `false`. |
| Serial source-module audit | **27/27 exit code 0** | `logs/lean/serial-20260802-082127/summary.json`; every module was compiled with an explicit `.lake/build/lib/lean/...olean` output. |
| Production aggregate | **passed** | `logs/lean/run-20260802-083015.status.json`; `lake build LeanFormal`, `Build completed successfully (3027 jobs)`. |
| ABC without `sorry` | **expected failure** | `logs/lean/abc-20260802-082834/without-sorry.stderr.log`; unsolved `∃ K` goal, exit code 1. |
| ABC with `sorry` | **expected success** | `logs/lean/abc-20260802-082834/with-sorry.stdout.log`; exit code 0 and `sorryAx` in `#print axioms`. |
| Axiom sample | **passed audit** | `logs/lean/axioms-20260802-083444/axiom_audit.stdout.log`; foundational and conditional theorems have no `sorryAx`, while `theorem311_produces_stepXI_contract` explicitly depends on `sorryAx`. |
| Extended serial source-module audit | **28/28 exit code 0** | `logs/lean/serial-20260802-084418/summary.json`; includes the new `ABCBridge/Arithmetic/PrimitiveTriple.lean` module. |
| Current serial source-module audit | **29/29 exit code 0** | `logs/lean/serial-20260802-194319/summary.json`; includes `HolomorphicHull/Volume` and the current aggregate entry point. |
| Current serial source-module audit (quotient kernel) | **30/30 exit code 0** | `logs/lean/serial-20260802-200141/summary.json`; includes `Theorem311/Indeterminacy/QuotientTransport.lean`. |
| Current serial source-module audit (finite bridge) | **31/31 exit code 0** | `logs/lean/serial-20260802-201306/summary.json`; includes `StepXI/FiniteCertificateBridge.lean`. |
| Current logged aggregate | **passed** | `logs/lean/run-20260802-200751.status.json`; `lake build LeanFormal` completed successfully with 3034 jobs. |
| Current logged aggregate (explicit bridge) | **passed** | `logs/lean/run-20260802-201110.status.json`; `lake build LeanFormal` completed successfully after adding `FiniteCertificateBridge`. |
| Automated production axiom boundary | **passed** | `tools/check_axiom_boundary_logged.ps1` ran successfully; nested audit is `logs/lean/axioms-20260802-202110/`, and exactly one sampled production declaration has `sorryAx`: `theorem311_produces_stepXI_contract`. |
| Extended aggregate | **passed** | `lake build LeanFormal` reported `Build completed successfully (3028 jobs)` after adding the primitive-triple module. |
| Extended axiom sample | **passed audit** | `logs/lean/axioms-20260802-084337/axiom_audit.stdout.log`; `IsABCTriple.pairwise_coprime` has no `sorryAx`. |

## 2026-11-01 S1894: D5 large-image input on the actual curve E'/F' (S1720)



## S1977: the levelwise realification functional of the actual p-adic log-shell (2026-11-01)

tmp/sheaf/xif/paper/S1977LevelwiseRealificationActual.lean, EXIT=0, no
sorry/admit/axiom; source 605 lines, 28443 bytes, SHA256
20E5BDE82228449B755E71A857ABBF79836D2CC8AD6307CA8F75B04B39BA8C20; olean 680032
bytes, SHA256 E047138549BA45DA1EAC68E13F43507B06B15AAA7534BA11F17AA2ED0E0644CA;
axioms only propext/Classical.choice/Quot.sound. Import: S1961 only. Consumer
_S1977Consumer.lean EXIT=0 against the built olean.

Question: S1961 leaves the levelwise equality
realBridge '' actualLogShell = reduced logShell open and names as remaining
object "an additive real-valued functional on Completion (QPlace v) compatible
with the norm-log readout".  Result: that object provably does not exist.

- no_additive_realification: there is no L : Completion (QPlace v) ->+ R with
  L x = realBridge v x for all x in the actual log-shell.  Proof with the
  uniformizer pi: the shell is an AddSubgroup containing pi, pi+pi, (pi+pi)+(pi+pi);
  additivity forces log ‖2‖ = log ‖pi‖ and log ‖2‖ = log ‖2 pi‖ =
  log ‖2‖ + log ‖pi‖, hence log ‖pi‖ = 0, contradicting ‖pi‖ < 1.
- LevelwiseRealificationFunctional v (the proposed object) is empty
  (levelwiseRealificationFunctional_not_nonempty).
- levelwise_equality_false: realBridgeImage v != paperLogShell v, because the
  bridge image is bounded above (the shell is compact hence bounded) while the
  reduced shell is unbounded above (p*^{-1}-scaled positive multiples of the
  norm-log of pi^{-1}).  Hence no function at all can do it
  (no_levelwise_realification_function).
- The units-side variant is degenerate:
  additive_functional_trivial_on_preLogShell (integral units have norm 1).

What is constructed: the norm-log functional on the multiplicative group,
additiveNormLog : Additive (Completion (QPlace v))^x ->+ R and
levelwiseNormLog, together with the levelwise set identities
paperPreLogShell v = range additiveNormLog and
paperLogShell v = p*^{-1} * range additiveNormLog; and
completionUnits_norm_eq_one / realBridge_image_completionUnits showing the actual
unit group's norm-log image is {0}.  The sharp statement remains S1961's
s1977_span_bridge_sharp (Submodule.span Q of the two sides).

Exact first missing: not a functional but an identification O_v^x ~ K_v^x
compatible with the norm-log readout (uniformizer splitting); impossible since
the left readout is identically zero.  Consequence for the paper route: the
local p-adic/real bridge is Q-span/volume level only; no local levelwise
additive realification exists.  No fake functional, no arbitrary choice.
