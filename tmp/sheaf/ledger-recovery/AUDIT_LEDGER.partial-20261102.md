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
## 2026-11-02 S2072: correction to S2071-follow-up inventory; actual affine quotient exists

- CORRECTION (history preserved): the 2026-11-02 S2071 follow-up line "No construction in tree/Mathlib: no finite group quotient of finite etale covers, no proof quotient is finite etale" is false as stated. The tree already has a 0-sorry affine finite-etale quotient development (all compiled, axioms trio): FiniteEtaleFixedPointsGeneral.fixedPointSubalgebra_finiteEtale (A^G finite etale over R for finite G, rank decomposition + localizations), AffineBaseFiniteEtaleQuotients.quotientCoverOfDiagram / quotientProjectionOfDiagram / quotientProjectionOfDiagram_invariant / actionCoconeOfDiagram, AffineOverlapQuotientTransportProof.affineTargetUniversal, FiniteEtaleQuotientGluedCover.finiteEtaleCoverCarrier_isAffine. What is genuinely missing is the packaging of the affine universal property into IsColimit (actionCoconeOfDiagram F).cocone over the full subcategory FiniteEtaleCover (Spec R), plus (for non-affine S) the affine-chart gluing/descent already frozen as GlobalQuotientUniq.GlobalQuotientCoconeResidual.
- Mathlib 4.32.2: no scheme quotient by finite group action (Mathlib/AlgebraicGeometry has no Scheme.quotient/IsQuotient/group-action quotient). vendor/promachina: no scheme quotient either; SourceTemperoidQuotient/SourceAnabelioid* are anabelioid/graph-level quotients, not scheme or finite-etale-cover quotients.
- S2072HasQuotientsActual.lean, SHA 3ECDA410..., 12101 B, EXIT=0; olean 82328 B SHA 3021E0F6...; axioms trio on all declarations. Content: cocone_singleObj_inv (actual); affineActionQuotientCover/affineActionQuotientProjection/affineActionCocone from the actual affine construction with invariant projection; frozen exact residual AffineQuotientColimitPackaging R := forall G [Group G] [Finite G] (F), IsColimit (actionCoconeOfDiagram F).cocone; affineHasColimitsOfShape_of_packaging; curveScheme_eq_spec; curveHasQuotientsOfPackaging; curvePreGaloisRemainingFieldsOfPackaging : CurvePreGaloisCategoryRemainingFields (curveScheme K) from the residual; schemeHasQuotientsOfPackaging; curveQuotientsOf_trivialActions (trivial-action colimit unconditional, non-vacuous check). No sorry/axiom/Nonempty.
- Required API to close the residual (all pieces already in tree): FiniteEtaleCover.forgetOver faithful + ObjectProperty.hom_ext + Over.OverMorphism.ext for cover-morphism equality; finiteEtaleCoverCarrier_isAffine for every cocone point; coverSectionsAlgHom naturality/action lemmas (AffineBaseFiniteEtaleQuotients.coverSectionsAlgHom_map_eq/comp) to turn cover-level invariance into algebra-map invariance; affineTargetUniversal or affineFixedPointQuotient_universal_spec to build desc.
- Attempted full IsColimit proof (scratch only, not deliverable) confirmed the desc/fac/uniq skeleton is reachable but the full-subcategory/Over/Spec.preimage transport is not yet assembled; exact open obligation is the residual above, not a missing quotient object.

## 2026-11-02 qside D6: cone2 + liftCone_compat + liftNatIso actual

- S2082 cone2: SHA 03145C5E..., olean 141696; axioms trio; includes S2082At_commutes_app' at U and S2082lift_fst/snd_obj rfl lemmas.
- S2083: SHA DA5E907B..., olean 214912; axioms trio; general vcomp_toA/B_naturality_apply + liftCone_compat.
- S2084: SHA 38F1BDBC..., olean 121832; axioms trio; liftConeHomForward, liftConeIso, liftNatIso for arbitrary S2074GeneralCone.
- Remaining generalLiftSite: liftNatIso_hom_fst/liftNatIso_hom_snd (S1985 analogues), then liftSite with naturality_id/comp (long copy of S1985 adapted c.W) -> liftToA/liftToB -> full TwoPullbackWitness -> S2058IsoCommaTwoPullback -> ToA. No pasting touched; no sorry in accepted files.

## 2026-11-02 S2072: affine quotient actual; exact residual AffineQuotientColimitPackaging

- Inventory correction: tree already has 0-sorry affine finite-etale quotient development compiled, axioms trio: FiniteEtaleFixedPointsGeneral.fixedPointSubalgebra_finiteEtale; AffineBaseFiniteEtaleQuotients.quotientCoverOfDiagram/quotientProjectionOfDiagram/quotientProjectionOfDiagram_invariant/actionCoconeOfDiagram; AffineOverlapQuotientTransportProof.affineTargetUniversal; FiniteEtaleQuotientGluedCover.finiteEtaleCoverCarrier_isAffine. Mathlib/vendor no scheme quotient.
- S2072HasQuotientsActual.lean, SHA 3ECDA410..., 207 lines, EXIT=0; olean 82328 B SHA 3021E0F6...; axioms trio.
- Content: cocone_singleObj_inv; actual affineActionQuotientCover/Projection/Cocone; frozen residual AffineQuotientColimitPackaging R := forall G [Group G] [Finite G] F, IsColimit (actionCoconeOfDiagram F).cocone; affineHasColimitsOfShape_of_packaging; curveScheme_eq_spec; curveHasQuotientsOfPackaging; curvePreGaloisRemainingFieldsOfPackaging; schemeHasQuotientsOfPackaging; curveQuotientsOf_trivialActions (residual not vacuous).
- Exact first missing for curve card: AffineQuotientColimitPackaging (curveCoordinateRing K), i.e. desc/fac/uniq for every action diagram. Quotient object NOT missing. Required API: FiniteEtaleCover.forgetOver faithful + ObjectProperty.hom_ext + Over.OverMorphism.ext; finiteEtaleCoverCarrier_isAffine for cocone point; coverSectionsAlgHom + coverSectionsAlgHom_map_eq/comp; affineTargetUniversal/affineFixedPointQuotient_universal_spec. Full-subcategory/Over/Spec.preimage transport is blocker; no fake.

## 2026-11-02 S2076: S2058IsoCommaTwoPullback COMPLETE

- S2076IsoCommaTwoPullbackActual.lean, 987 lines/47 decls, SHA BC100FA1..., EXIT=0; olean 1885800 B; axioms trio; consumer EXIT=0.
- S2076S2058IsoCommaTwoPullback : S2058D6FiniteEtaleActual.S2058IsoCommaTwoPullback (last missing D6(c) input). S2076IsoCommaTwoPullback : S2074IsoCommaTwoPullbackStatement. S2076Witness : TwoPullbackWitness for iso-comma square of any cospan of actual cover maps, all 7 fields.
- Constructed: gLiftNat/gLiftApp/gLiftNatConeA/B/gCone1/gCone2_commutes_app/gLiftCone_compat/gLiftConeHomForward/coneHom_isIso/gLiftConeIso/gLiftNat (preimageIso under full faithfulness)/gLiftNat_hom_fst/snd; gLiftSite with naturality_naturality/id/comp; gLiftToA/gLiftToB + site naturality; gTwoCellAt/gLiftTwoCell/gLiftTwoCell_toA/_toB; gTwoCell_ext from S1836IsoComma_hom_ext; S2076Cone/ConeMorphism for fixed apex.
- No consumer yet of S2058IsoCommaTwoPullback in tree; S2071 supplies pasting; remaining D6(c) is assembly of S2044ToAFiniteEtaleField, not math gap. Our probe confirms S2076S2058IsoCommaTwoPullback/S2076Witness axioms trio.

## 2026-11-02 S2086: ToA assembly reduced to witness base-change

- S2086ToAAssemblyActual.lean, SHA 3B8FB1BA..., 78 lines, EXIT=0; olean 163120 B; axioms trio.
- S2086ToAOfWitnessBaseChange (h : S2086WitnessBaseChangeStatement) : S2044ToAFiniteEtaleField. Uses S2076S2058IsoCommaTwoPullback via B.finiteEtale presentation. S2071PastingStatement not used (pasting, not witness base-change).
- Exact missing S2086WitnessBaseChangeStatement: for every ptA : schemeRep T -> A.source.fiber and B-presentation PB : EtaleStackBaseChangePresentation B.map T (((ptA ≫ f.map) ≫ C.map)), produce EtaleStackBaseChangePresentation of toA f g at ptA whose projection IsFinite ∧ Etale. Requires geometric base-change/cone construction over iso-comma square: construct cone from ptA and B base-change point, apply S2076Witness.lift/liftToA, identify C-side comparison with C.source point. D6(c) closes once this proved. No fake.

## 2026-11-02 S2087: S2086 witness base-change obstruction; need g.map finite etale

- S2087ToAObstructionActual.lean, SHA 8C1384A9..., EXIT=0; olean 9864.
- S2086WitnessBaseChangeStatement cannot be constructed from S2076Witness+B.finiteEtale: to build cone over iso-comma square from ptA one needs a point of B.source.fiber over C.source point ptA ≫ f.map. Only B.finiteEtale : EtaleStackFiniteEtaleMorphism B.map targets orbicurve stack S1726Orbicurve.stack, NOT C.source.fiber. No presentation of g.map (B.source -> C.source) in tree.
- Exact additional input: S2087GMapFiniteEtaleField and S2087CospanGMapFiniteEtaleField (every cover map g : B -> C representably finite etale), equivalent to direct finite-etale proof for structureMap = toA ≫ A.map. If g.map is not finite etale in general, S2044 factorization is insufficient; correct remaining target is direct structureMap finite-etale proof. No fake certificate.

## 2026-11-02 S2088: scheme cancellation actual; g.map finite etale reduces to stack cancellation

- S2088GMapCancellationActual.lean, SHA 0FAB3E9D..., 53 lines, EXIT=0; olean 25976; axioms trio.
- S2088_scheme_finiteEtale_cancel: Mathlib Etale.of_comp + IsFinite.of_comp: if f≫g finite etale and g finite etale (with LocallyOfFiniteType/FormallyUnramified/IsSeparated from finite etale) then f finite etale.
- S2088GMapFiniteEtaleOfStackCancellation (hcancel : S2088StackCancellation) : S2087GMapFiniteEtaleField, using B.finiteEtale, C.finiteEtale, S2058IsoInvarianceFiniteEtale with g.commutes.symm.
- Exact remaining S2088StackCancellation: forall stacks X Y Z (f:X.Hom Y)(g:Y.Hom Z), finiteEtale (vcomp f g) -> finiteEtale g -> finiteEtale f. Proof: present f at ptY via presentation of g at ptY≫g and presentation of f≫g at resulting Z-point, then cancel scheme morphisms with S2088_scheme_finiteEtale_cancel. D6(c) closes once proved. No fake.

## 2026-11-02 S2089: stack cancellation reduced to presentation construction

- S2089StackCancellationActual.lean, SHA C5E04AB9..., 54 lines, EXIT=0; olean 23976; axioms trio.
- S2089StackPresentationStatement (construct presentation of f at ptY from finiteEtale (f≫g) and finiteEtale g) + S2089StackPropertyStatement (projection finite etale) together give S2088StackCancellation. S2088 scheme cancellation actual.
- Exact remaining D6(c): (1) construct EtaleStackBaseChangePresentation f T ptY by base-changing triangle along ptY via hg.baseChange T (ptY≫g) and hf.baseChange at resulting Z-point, comparing the two presentations (formal pasting of presentation squares); (2) property follows by S2088_scheme_finiteEtale_cancel on the two scheme projections once comparison built. No fake.

## 2026-11-02 S2090: stack cancellation route false; direct g.map finite etale route

- S2090StackCancellationObstructionActual.lean, SHA EE941E1A..., 39 lines, EXIT=0; olean 12632.
- S2089StackPresentationStatement not derivable via cancellation: constructing f presentation from hg.baseChange and hf.baseChange gives Iso (vcomp (vcomp xsrc f) g) (vcomp proj (vcomp ptY g)); to get Iso (vcomp xsrc f) (vcomp proj ptY) needs postcomposition cancellation Iso (a≫g) (b≫g) -> Iso a b, FALSE for arbitrary stack g (Cat constant functor loses info). S2090PostcompCancellation no inhabitant.
- Consequence: exact remaining D6(c) input is S2087GMapFiniteEtaleField (representable finite etaleness of cover-map morphisms) or direct structureMap = toA ≫ A.map finite-etale proof. Not derivable from S2076/S2089. S2088 scheme cancellation remains actual.
- Direct route to try: for g : cover map B C, g.map is a scheme morphism over base; (g.map) ≫ C.structureMap = B.structureMap by Over.w; both B/C structure maps finite etale; apply S2088_scheme_finiteEtale_cancel with f := g.map, h := C.structureMap (need LocallyOfFiniteType/FormallyUnramified/IsSeparated from finite etale). This may prove S2087GMapFiniteEtaleField without stack presentations.

## 2026-11-02 S2091: scheme cancellation special; g.map is stack morphism

- S2091SchemeDirectActual.lean, SHA 21E06ED9..., 34 lines, EXIT=0; olean 14616; axioms trio.
- S2091_scheme_finiteEtale_cancel_special: [IsFinite (f≫h)] [Etale (f≫h)] [IsFinite h] [Etale h] -> IsFinite f ∧ Etale f, derived from S2088_scheme_finiteEtale_cancel.
- CAVEAT: g.map : B.source.Hom C.source is a morphism of STACKS, not a scheme morphism. Pointwise application requires EtaleStackBaseChangePresentation of g.map at each point of C.source, i.e. representability data not present. S2091 does NOT directly give S2087GMapFiniteEtaleField; exact remaining stack input still S2087GMapFiniteEtaleField (or stack representability theorem for morphisms between finite-etale stacks / direct structureMap finite-etale proof). No fake.

## 2026-11-02 S2090: evaluatedUnitSubgroup ≃* Integers units actual; S2046 M1 closed

- S2090EvaluatedUnitsBridgeActual.lean, SHA A374A7B7..., EXIT=0; olean 236808 B SHA 021D231B...; 8 probes trio; no sorry.
- padicValuativeRel_le_one_iff_norm; isIntegral_of_norm_le_one (spectralNorm/spectralValue_le_one_iff -> minpoly coefficients norm<=1 -> lifts to Z_p integral ring -> monic polynomial aeval=0); isIntegral_iff_norm_le_one; isIntegral_iff_mem_integers; mem_evaluatedUnitSubgroup_iff; evaluatedUnitsEquivIntegersUnits : evaluatedUnitSubgroup p ≃* (Integers (AlgClosure Q_[p]))^x with apply_coe/symm_apply rules.
- Consumers: S2046EvaluatedUnitsToIntegersRequired_actual inhabits old first-missing; S2046EvaluatedUnitsToIntegersRequired_nonempty; S2046LocalUnitsEquivOtriUnits : (Otri p)^x ≃* LocalOFieldUnits p unconditional; S2090OtriUnitsEquivIntegersUnits.
- Our probe confirms evaluatedUnitsEquivIntegersUnits and S2046LocalUnitsEquivOtriUnits axioms trio. S2046 M1 closed; old S2046M1LocalUnitsActual bad (sorryAx) not imported. Remaining S2046: M4 H²=Zhat, Gv-action on PsiCns units, PsiCns->PsiGau evaluation.

## 2026-11-02 S2086 (revision): ToA assembly; exact 2-categorical missing isolated

- S2086ToAAssemblyActual.lean rewritten, SHA 21025F73EBBDB0C65808B1BD97946A33757BD61607F3AC88B66897B6448BBD32, 288 lines, EXIT=0; olean 66720 B SHA D6A5EEF59C614E3F0F45267A9344A25442D94E3E5CD4BEF9FB54B99027A66ABC; axioms trio; consumer EXIT=0; S2087/S2088/S2089 recompiled EXIT=0 against the new olean.
- Builds S2086Cone/S2086Lift/S2086LiftToA/S2086ToASquare from S2076Witness and a presentation of g.map at ptA; S2086ToAPresentation has every field except isPullback.
- S2086CospanGMapFiniteEtale (the S2087 field) + S2086BaseChangePullback hg imply S2044ToAFiniteEtaleField (S2086ToAOfInputs), hence S2043FirstMissingFiniteEtale via S2069 (S2086D6FiniteEtaleOfInputs); bundled as S2086FirstMissing.
- Exact 2-categorical missing S2086BaseChangePullback hg: the explicit square (S2086Lift, Pg.projectionMap, toA, ptA) must be a TwoPullbackWitness, i.e. T x_A (A x_C B) = T x_C B. It is not a vertical/horizontal S2058 pasting: the iso-comma square and the g-presentation share B -> C at different apices, with two triangle 2-cells. S2076 supplies only the recorded weak seven-field witness; S1827/S1843/S1844/S1850/S1852 show the weak fields do not imply cone-comparison essential surjectivity. Hence S2086BaseChangePullback is not derived from S2076 + S2071 and is recorded as a Type, no fake.
- S2086StackCancellation -> S2086CospanGMapFiniteEtale (same statement as S2088) is recorded conditionally; S2090's obstruction shows the S2089 presentation route is false, so the primary remaining geometric input is still S2087GMapFiniteEtaleField.
- The earlier S2086 entry (S2086WitnessBaseChangeStatement/S2086ToAOfWitnessBaseChange, lines 414-418) is superseded in precision but kept as history; those declaration names are no longer present.

## 2026-11-02 S2092: D6(c) reduced to stack theorem for morphisms of finite-etale stacks

- S2092FiniteEtaleStackMorphismActual.lean, SHA 81F79648..., 41 lines, EXIT=0; olean 17672; axioms trio.
- S2092GMapFiniteEtaleOfMorphismOfFiniteEtaleStacks: S2092MorphismOfFiniteEtaleStacks -> S2087GMapFiniteEtaleField by m=g.map, x=B.map, y=C.map, g.commutes.
- Exact first missing S2092MorphismOfFiniteEtaleStacks: forall (m:X.Hom Y)(y:Y.Hom Z)(x:X.Hom Z), Iso (vcomp m y) x -> finiteEtale x -> finiteEtale y -> finiteEtale m. B/C presentations alone fail: base-changing via C.finiteEtale/B.finiteEtale compares C.source points only after composing with C.map; comparing them before C.map is exactly missing representability/descent step. Stack theorem (morphism between finite-etale stacks over base is representably finite etale) is precise remaining D6(c) input. No fake.

## 2026-11-02 S2086 revision: ToA needs g.map finite etale + base-change/butterfly pullback

- S2086ToAAssemblyActual.lean rewritten, SHA 21025F73..., 288 lines, EXIT=0; olean 66720 B SHA D6A5EEF5...; consumer EXIT=0; S2087/S2088/S2089 recompile EXIT=0; axioms trio.
- Built S2086ToAPresentation except isPullback: S2086PointC, S2086Cone, S2086LiftToA, S2086ToASquare, S2086ToAPresentation; S2086ToAOfInputs hg h : S2044ToAFiniteEtaleField; S2086D6FiniteEtaleOfInputs; S2086FirstMissing := Sigma hg : S2086CospanGMapFiniteEtale, S2086BaseChangePullback hg; S2086D6FiniteEtaleOfFirstMissing.
- Exact missing: (1) S2086CospanGMapFiniteEtale = forall A B C f g, EtaleStackFiniteEtaleMorphism g.map (= S2087GMapFiniteEtaleField cospan form); B.finiteEtale target orbicurve stack cannot give g.map presentation at ptA≫f.map. (2) S2086BaseChangePullback hg = for each ptA the explicit square (S2086Lift, Pg.projectionMap.transformation, toA f g, ptA, S2086LiftToA) is TwoPullbackWitness, i.e. T x_A (A x_C B) = T x_C B butterfly/base-change identification.
- Why S2076+S2071 insufficient: S2076 gives weak seven-field TwoPullbackWitness, not cone-comparison essential surjectivity/full 2-universal property; S1827/S1843/S1844/S1850/S1852 show weak fields do not imply full; S2071 pasting only handles two squares sharing fixed 1-cell, not pullback-of-pullback/butterfly. So S2086BaseChangePullback not derivable from S2076+S2071; exact missing.
- Old S2086WitnessBaseChangeStatement/S2086ToAOfWitnessBaseChange removed; ledger 414-418 retained historical. Report S2042 needs update.

## 2026-11-02 S2089: FiniteAbelianSubextension proved; maxAbelian = L^ab unconditional

- S2089FiniteAbelianSubextensionActual.lean, SHA D7B07BFA..., EXIT=0; olean 344544 B SHA 6F77B9AD...; 9 probes trio; no sorry.
- finiteAbelianSubextension (U) : S2056MaxAbelianBridge.FiniteAbelianSubextension U; maximalAbelianExtension_le_maxAbelian; maxAbelian_eq_maximalAbelianExtension : PadicField.maxAbelian (localField p U) (AlgClosure Qp) = maximalAbelianExtension p U; mem_maximalAbelianExtension_iff; maximalAbelianExtension_eq_iSup; maxAbelianEquivMaximalAbelianExtension; galoisGroupEquiv : Gal(maxAbelian/E) ≃* Gal(maximalAbelianExtension/E).
- Proof: L0=E(x) finite; L=normalClosure finite Galois; M=maximalAbelianExtension Galois via fixingSubgroup + commutatorClosed_normal + InfiniteGalois.normal_iff_isGalois; L<=M; IsAbelianGalois E M from galoisGroupMaximalAbelian_commGroup; IsAbelianGalois E L by of_algHom inclusion.
- Our probe confirms maxAbelian_eq_maximalAbelianExtension/galoisGroupEquiv axioms trio. M2a bridge now unconditional; next retype PadicField.artin to (localField p U)^x ->* Gal(L^ab/L), restrict to unitProfiniteCompletion, localArtinTorsion/LocalArtinSourceData.

## 2026-11-02 S2094: exact full-2-universal inputs for butterfly

- S2094FullUniversalInputsActual.lean, SHA 8A7BC969..., 50 lines, EXIT=0; olean 17840.
- S2094BigSquareEssSurj : forall f g, S1827EssSurjOf (iso-comma square) (S2076Witness). S2094GPresentationConeEssSurj : forall used Pg, S1852ConeEssSurj Pg. Both Prop, no inhabitant.
- Why exact: S2076 gives weak TwoPullbackWitness, not S1827EssSurjOf full 2-universal property; EtaleStackBaseChangePresentation.isPullback is only weak, not S1852ConeEssSurj. Butterfly pasting of these two full properties yields S2086BaseChangePullback.
- Next: prove S1827EssSurjOf for S2076Witness (via gTwoCell_ext + lift constructions) and S1852ConeEssSurj for Pg (full base-change universal property), then paste. No fake weak witness.

## 2026-11-02 S2046 M4 conditional port using S2090 canonical M1

- S2046M4ConditionalActual.lean, SHA E25C343F..., EXIT=0; olean SHA 8DB873B9...; axioms trio.
- Built S2046M2LocalArtinRequired/S2046M3H2Required/S2046M4KummerNormalizationRequired exact props; S2046M4NormalizationOfKummer; S2046M4OtriUnitsEquivNormalization; S2046M4LocalUnitsEquivNormalization : LocalOFieldUnits p ≃* units of normalization inverse image; S2046M4_sufficient; S2046ZhatNonnegEqNatMonoid exact comparison.
- Missing exact: M2 local Artin, M3 H^2=Zhat, M4 normalization/Kummer image (S2036), zhatNatMonoid=zhatNonneg, G_v-action on PsiCns units, PsiCns->PsiGau evaluation. No fake.

## 2026-11-02 S2095: lift uniqueness reduction for BigSquareEssSurj

- S2095BigLiftUniqActual.lean, SHA 43B33D2E..., 45 lines, EXIT=0; olean 24176; axioms trio.
- S2095BigLiftUniq = for every cone c over iso-comma square and h : W -> sitePseudofunctor with isos of two projections to c, Nonempty (Iso h ((S2076Witness).lift W c)). S2095BigEssSurj_of_liftUniq : S2095BigLiftUniq -> S2094BigSquareEssSurj.
- Exact next: prove S2095BigLiftUniq via S1893LiftUniq/fibre comparison + gTwoCell_ext (site-level lift uniqueness); then S1852ConeEssSurj Pg; paste -> S2086BaseChangePullback. No fake weak witness.

## 2026-11-02 S2096: S2095BigLiftUniq blocked on site-level naturality

- No new accepted file; last accepted remains S2095 (SHA 43B33D2E...).
- Exact missing: (1) a natural iso between h.app U and gLiftApp c U across site objects, built from projection isos eX/eY, compatible with S1890IsoCommaMap; (2) naturality_naturality/id/comp coherence after whiskering by toA/toB, closed by gTwoCell_ext; (3) S1852ConeEssSurj Pg. S1893LiftUniq gives only fibre-level uniqueness, not site-level naturality.
- Suggested next: implement fibre-level iso via S1893LiftIsoOfConeIso as S2096FibreIso, then site naturality; do not modify accepted S1893/S2076; add new lemma in new file. No fake.

## 2026-11-02 S2046 M2 port via S2089; D6 S2096 blocked on site naturality

- S2046M2S2089Port.lean, SHA 4AF83FBD..., EXIT=0; olean SHA 4DBE7F04...; axioms trio.
- S2046ArtinToMaxAbelian := PadicField.artin; S2046ArtinToMaximalAbelian via S2089.galoisGroupEquiv; S2046ArtinToTopological via S2027.galoisGroupMaximalAbelian.symm.
- S2046M2TorsionRequired U : mu p U ≃* torsion(TopologicalAbelianization(localGaloisGroup p U)); S2046M2CarrierRequired U : torsion(Abelianization U) ≃* torsion(TopologicalAbelianization(...)); S2046LocalArtinSourceDataOf hartin hcarrier : LocalArtinSourceData p; S2046M2_sufficient.
- Exact missing: torsion Artin equivalence (S2027 localArtinTorsionTopological), M2c abstract/profinite carrier comparison (S2027 profiniteTorsionComparison). No fake. Next M3 H2=Zhat, M4.
- S2096: S2095BigLiftUniq blocked on site-level naturality API; no new accepted file; last S2095. Missing (1) natural iso h.app U ≅ gLiftApp c U across site objects compatible with S1890IsoCommaMap; (2) naturality_naturality/id/comp coherence after whiskering toA/toB closed by gTwoCell_ext; (3) S1852ConeEssSurj Pg. S1893LiftUniq only fibre-level. Suggested fibre-level iso first; do not modify accepted S1893/S2076; add new file.

## 2026-11-02 S2093: D9 stack exact decomposition; corrected exact target

- S2093D9StackActual.lean, SHA A31B624C..., 481 lines, EXIT=0; olean 227744 B SHA 9F7ED7AD...; 23 probes trio; no sorry/Shrink/ULift/PUnit.
- S2093LargeSheafStackMissing K definitionally S2050LargeSheafStackMissing K / S2029SheafStack K; unfolds to IsStack of S2029SheafPrestack.
- Exact decomposition IsStack <-> S2093SheafPrestack K / S2093SheafEffectiveDescent K; prestack half = forall S M N, Presheaf.IsSheaf (J.over S) (F.presheafHom M N).
- Reduction to actual etale covering families: S2093EtalePrecoverage K = Scheme.etalePrecoverage.comap (Over.forget (Spec K)), generates etaleTopology; S2093LargeSheafStackMissing K <-> S2093SheafStackOnEtaleFamilies K.
- Old CFData decomposition: Nonempty S2050LargeCFData l A <-> Nonempty (S2050LargeEtaleStackOverField (S1732A l).F) / Nonempty (S1964HonestCFQuotient l A). Corrected exact target S2093LargeCFDataExact l A with stack fixed to natural sheaf prestack; equivalence to S2050LargeSheafStackMissing / HonestCFQuotient; maps to old CFData and S1964QuotientStructure.
- Old small target equivalence; S2093SmallStackTransport K exact transport input; pure S2093SmallModelTransport.
- First missing: Proposal B S2050LargeSheafStackMissing (S1732A l).F + S1964HonestCFQuotient; stack half = S2093SheafPrestack/EffectiveDescent, equivalently effective descent for actual etale families. Proposal A S2093SmallStackTransport K. IsStack not proved; Mathlib no IsStack instance for category-valued pseudofunctors; stack-of-sheaves absent. Next prestack half: compare Pseudofunctor.presheafHom (overMapPullback j.hom) with SheafHom.sheafHom on slice site (overPullback j), using Over.iteratedSliceBackward_forget / iteratedSliceEquivOverMapIso; missing naturality in j. Effective descent remains. No fake.

## 2026-11-02 S2100: S2094GPresentationConeEssSurj REFUTED

- S2100GPresentationConeEssSurjActual.lean, SHA 2430B429..., EXIT=0; olean 39848 B SHA 51D124D0...; axioms trio.
- Counterexample: A=B=C=S1850DoubledCover; f=g=S1641CoverMapId (identity cover map, underlying map = 1); T=S1726AffineOver, ptA=S1733BasePoint; Pg=S1850Doubled ... legal EtaleStackBaseChangePresentation; S1852Doubled_not_coneEssSurj gives not S1852ConeEssSurj Pg. Hence S2100NotGPresentationConeEssSurj : not S2094GPresentationConeEssSurj.
- Conclusion: missing is not presentation descent/pasting API; the universal input is false at identity cover map. S2094 second input quantification too wide. Correct fix: S2100StrongGPresentationInput (strong presentation per chosen g.map) or StrongEtaleStackFiniteEtaleMorphism for cover map; S2100ConeEssSurj_of_strongGPresentationInput / of_strongFiniteEtale. S2086 should strengthen hg to strong finite-etale or explicitly pass strong presentation; do not keep false universal input. S2094BigSquareEssSurj still separate.

## 2026-11-02 S2087 affine quotient packaging DONE; S2095 direct structureMap; S2100 D9 prestack

- S2087AffineQuotientPackagingActual.lean, SHA 10E9C083..., 407 lines, EXIT=0; olean 553472 B SHA ED562C0C...; 7 probes trio; consumer EXIT=0.
- Proved affineActionCocone_isColimit F for every CommRing R, finite G, F : SingleObj G ⤚ FiniteEtaleCover (Spec R); affineQuotientColimitPackaging R : AffineQuotientColimitPackaging R; s2073AffineActionCoconeIsColimit R; affineHasColimitsOfShape; curveAffineQuotientColimitPackaging K; curveHasQuotients K; curveS2073HasQuotients K; curvePreGaloisRemainingFields K : CurvePreGaloisCategoryRemainingFields (curveScheme K) [UNCONDITIONAL].
- Proof: phi=coverSectionsAlgHom; invariance -> fixed; affineFixedPointQuotient_lift_algHom -> descPsi; desc via descSchemeMap/descPsi + isoSpec.inv; fac/uniq via forgetOver faithful/ObjectProperty.hom_ext/Over.OverMorphism.ext/Spec.preimage. No sorry/axiom/Nonempty. Curve M1 CLOSED.
- S2095DirectStructureMapActual.lean, SHA 493FE060..., 446 lines, EXIT=0; olean 122520 B SHA 7E523B9A...; 13 probes trio.
- Path B: S2095ToBCone/Lift/LiftToB/ToBPresentation constructed from left leg certificate; S2095D6FiniteEtale_of_toB: finiteEtale (toB f g) -> S2043FirstMissingFiniteEtale; projection finite etale free via S2048. Only field missing: S2095ToBButterfly (explicit TwoPullbackWitness butterfly). Path A dead: comparison needs postcomposition cancellation along C.map (S2095PostcompCancellation -> S2090, false in general); candidate apex T x_base C x_base B not T x_C B; hasProperty free, so S2088/S2091 not issue. Structural finding: toA impossible without g.map certificate; toB only needs f.map. D6(c) = one iso-comma projection representably finite etale + butterfly.
- S2100D9PrestackNaturalityActual.lean, SHA 4FBFCFD4..., EXIT=0; olean 63640; axioms trio. S2100SlicePullbackIso actual via sheafPushforwardContinuousComp/Over.iteratedSliceBackward_forget/sheafPushforwardContinuousIso. Exact missing S2100PrestackNaturalityIso (naturality in T/j); S2100SheafPrestack_of_naturality -> S2093SheafPrestack. Effective descent still missing.

## 2026-11-02 S2092: paper O^tri carrier + paper q_v actual; exact missing completion root

- S2092PaperOtriActual.lean, SHA 20A7371B..., 450 lines, EXIT=0; olean 578736 B SHA AB350CA9...; 13 probes trio; consumer EXIT=0.
- Source correction: IUT I §0 lines 250-271 O^tri = multiplicative monoid of nonzero integral elements of local field; Example 3.2(iv) lines 3701-3726 q_v^{1/2l} in O^tri(T_Xv) ≅ O^tri_{K_v}. S346/S357 speculative orbifold carrier not paper object; S342 excludes F-side qVFamily root.
- Constructed: paperOtriSubmonoid/paperOtri at sectionKPlace; paperQV := sectionQ actual; q_v in O^tri, nonzero, norm<1 non-unit; source attachment paperQV=completionMap shadowQ; order law; paperOUnits=(Integers K_v)^x; paperOUnitsMu=rootsOfUnity(2l); paperOUnitsToOtri injective; paperRootRatio_mem_mu; paperClosureRoot (root always exists in AlgClosure K_v, any two differ by 2l-th root of unity); paperOtriAttachment.
- Exact missing: IUT I Example 3.2(iv) q_v^{1/2l} in O^tri(T_Xv) ≅ O^tri_{K_v}, S1413 SectionTwoLRoot. paperOtriRootMissing_iff; any root forces l | eSource (paperOtriRoot_forces_l_dvd_of_coprime) and 2l | ord(q_v). Tree has clauseC.torsion23_rational/kernel_field_identification but no Tate parametrisation q_v^{1/2}, q_v^{1/l}, no K-side Tate point comparison (S1413SectionTateUniformization/S1515 points). F-side completion root impossible. No fake/all-units/qVFamily.

## 2026-11-02 S2103: strong-presentation assembly

- S2103StrongAssemblyActual.lean, SHA 9DED2F85..., 68 lines, EXIT=0; olean 31136; axioms trio.
- S2103StrongCospanGMapFiniteEtale (strong finite-etale structure on every g.map); S2103StrongBaseChangePullback hg (butterfly pullback for selected strong presentations); S2103ToAOfStrongInputs hg h : S2044ToAFiniteEtaleField; S2103D6FiniteEtaleOfStrongInputs hg h : D6(c) every cospan. Weak S2094 input/S2086 assembly superseded by S2100 refutation.
- Remaining: (1) S2103StrongCospanGMapFiniteEtale (strong certificates for g.map; NOTE S2087 curve M1 is affine quotient packaging, NOT this); (2) S2103StrongBaseChangePullback/S2095ToBButterfly; (3) S2094BigSquareEssSurj separately.

## 2026-11-02 M2a-core VERIFIED: localReciprocityIsomorphism actual

- Reciprocity closure rebuilt: lake build Reciprocity.ProfiniteCompletion completed successfully (8715 jobs).
- Our probe now passes: S2093ArtinM2aBridge.localReciprocityIsomorphism :
  unitProfiniteCompletion p U ≃* Gal(maximalAbelianExtension p U / localField p U); artinRetyped :
  (localField p U)^x →* Gal(maximalAbelianExtension p U / localField p U). Axioms trio.
- M2a-core CLOSED. Remaining M2a-torsion: torsion(unitProfiniteCompletion) ≃ mu / torsion(TopologicalAbelianization); M2c abstract/profinite carrier comparison; M2b Brauer.ArtinTransfer not ported.

## 2026-11-02 S2099: BigSquareEssSurj not proved; exact twist first missing

- S2099BigSquareEssSurjActual.lean, SHA 08625209..., 301 lines, EXIT=0; olean 311608 B SHA 5112514B...; axioms trio.
- S2099BigSquareEssSurj iff S2094BigSquareEssSurj iff S2095BigLiftUniq (rfl).
- S2099TwistAt fibre-level twist equation; S2099TwistAt_iff_comma: exactly comma-morphism condition; S2099TwistAt_canonical non-vacuous; S2099SiteFirstMissing Prop; S2099CompatibleLift; S2099BigSquareEssSurj_of_compatibleLift.
- Correction: S1893LiftUniq requires cone isomorphism (projection isos + comma compatibility), not projection-only; projection-only version false. The compatibility is S2099TwistAt, not in S2076Witness. S1827EssSurjNotFromWitness same insufficiency. First missing = (a) S2099SiteFirstMissing twist for all data, (b) site-level naturality of fibre comparison; (a)+(b) give S2095BigLiftUniq/BigSquareEssSurj. No inhabitant/fake.
- Consequence: do not plan S2094BigSquareEssSurj from S2076Witness + fibre comparison; any route must supply compatibility of projection 2-cells (genuine cone morphism) or different geometric theorem.

## 2026-11-02 S2089CurveCardM3: M1/M2 closed; CardV only M3 five fields

- S2089CurveCardM3Actual.lean, SHA C643576D..., 35 lines, EXIT=0; olean yes; axioms trio.
- S2087 curve M1 closed (affineQuotientColimitPackaging etc); S2081/S2074 M2 closed; S2089 cardV_of_remaining: RemainingTypeLevel -> Nonempty CardV.
- M3 remaining exact RemainingTypeLevel: preservesPullbacks (WalkingCospan), preservesFiniteCoproducts, preservesEpis, preservesQuotientsByFiniteGroups (forall finite A), reflectsIsos. preservesTerminalObjects already proved by S2088. FintypeCat lift via certificate_of_remaining. Also CurvePiOneData.tempered/comparison/proj_surjective/geometric_nontrivial; CardV geometricPiOne/geometricConnectedness parameters.

## 2026-11-02 S2088 M3 certificate status exact

- S2088FiberFunctorCertificateActual.lean, SHA E70B1285..., 461 lines, EXIT=0; olean yes; axioms trio.
- preservesTerminalObjects actual; certificate_of_remaining transfers.
- Five exact missing: (1) preservesPullbacks WalkingCospan: need scheme pullback geometric fiber = Type pullback; existing finiteEtaleCoverPullbackCover/ConeInCover/IsLimitInCover, missing image cone is Type limit (pullback.lift/lift_fst/lift_snd/hom_ext). (2) preservesFiniteCoproducts: need one-point scheme morphism to binary scheme coproduct factors through summand; Mathlib has Scheme.coprodMk/isCompl_range_inl_inr/IsOpenImmersion.lift but no factorization lemma. (3) preservesEpis: need finite etale cover epimorphism = surjective on geometric fiber; field-side S1747/S1810 EpiSurjective, scheme-side none. (4) preservesQuotientsByFiniteGroups: need geometric fiber of quotient cover = quotient of fibers, scheme quotient fiber description, Ω not sep closed. (5) reflectsIsos: need finite etale morphism bijective on geometric fiber => iso; needs finite etale fiber cardinality locally constant/connected base degree one. M1 closed but preservation missing. No fake.

## 2026-11-02 S2040 paper O^tri attachment filled from S2092

- S2040PaperOtriFromS2092Actual.lean, SHA E44F9E41..., EXIT=0; olean yes; axioms trio.
- s2040PaperOtriAttachmentActual T b : S2040PaperOtriAttachmentRequired T b with Otri:=paperOtri, qv:=paperQV, OUnits:=paperOUnits, OUnitsMu:=paperOUnitsMu, qv_root_attachment:=paperOtriRootMissing, OUnitsMu_attachment:=pow (2l)=1, norm_law:=norm(paperQV)<1.
- Proved s2040PaperOtriAttachmentActual_OUnitsMu_pow and _norm_law. Root attachment remains paperOtriRootMissing / S1413 SectionTwoLRootRequired (paper completion root q_v^{1/2l} in O^tri_{K_v}); S342 excludes qVFamily root; no all-units/orbifold carrier.
- S2040: paper O^tri/q_v/O^×/O^×μ actual; root missing; layer (2) actual S2060, layer (3) unconditional S2065, layer (1) exact split/degree/unramified. S2057 finite root-stack actual; old algebraic-closure LGP not paper O^tri. Paper hull/four q-pilot/link comparison remain.

## 2026-11-02 S2096 stack morphism reduction; S2104 canonical butterfly twist

- S2096StackMorphismActual.lean, SHA EBC0F7E7..., 553 lines, EXIT=0; olean 155992 B SHA EF20105F...; axioms trio.
- Proved scheme section finite etale; 2-Yoneda compositional HomOfVcomp/HomOfSchemeRepresentableMap; vertex cone/lift beta/vertex square/VertexMap_comp; S2096VertexPresentation (all fields except isPullback); S2096VertexProjection_isFiniteEtale; S2096MorphismOfFiniteEtaleStacks_of_presentationField; chain to S2087GMapFiniteEtaleField/S2086CospanGMapFiniteEtale; S2096D6FiniteEtale field -> S2086BaseChangePullback -> S2043FirstMissingFiniteEtale.
- Exact missing: M1 S2096UnpastingStatement (vertex square two-pullback; needs full cone ess surj/1-cell uniqueness; weak witness lacks); M2 S2096BaseChangeStatement (base change presentation along finite etale s:T->A); transport iso-invariance under point iso (S2058 only map leg). No inhabitant. S2092 not obtained unconditional; D6 chain conditional.
- S2104ButterflyTwistActual.lean, SHA F4C11F0E..., 53 lines, EXIT=0; olean 26912; axioms trio. Instantiates S2099TwistAt_canonical at c=S2095ToBCone, h=witness lift, alpha=liftToX, beta=liftToY: canonical twist/comma compatibility exists in actual S2095 path-B butterfly. Global S2099SiteFirstMissing too strong; not asserted. Useful for packaging S2095ToBButterfly, not S2094BigSquareEssSurj.

## 2026-11-02 S2097: butterfly base-change reduced to right-cancel + pasted transport

- S2097BaseChangeButterflyActual.lean, SHA C0CAFD0B..., 340 lines, EXIT=0; olean 289560 B SHA 3BC74BD2...; axioms trio.
- No unconditional S2086BaseChangePullback. Exact missing S2097RightCancelStatement: forall D:S2058Pasting, w2:S1827EssSurjOf D.square2 -> wP:S1827EssSurjOf D.squareP -> D.square1.TwoPullbackWitness. S2071 only gives forward pasting, not reverse; butterfly squares share B->C at different apex with two triangle 2-cells. S1827/S1843/S1852 record weak does not imply full.
- Constructed S2097LiftToB, S2097Pasting per Pg, S2097SwapWitness, S2097BaseChangePullback_of_rightCancel, S2097BaseChangePullback_of_twoFullInputs. Honest gap: S2097TwoFullInputs.pastedTransport (pasted square weak+full data via square iso) not formalized; technical bookkeeping with whiskerRight/bicategory coherence; not missing math. After right-cancel + transport, S2086BaseChangePullback unconditional.

## 2026-11-02 S2102 M2a-torsion VERIFIED

- S2102TorsionArtinActual.lean, SHA AB0FEFF3..., 252 lines, EXIT=0; olean 290528 B SHA FB5923BD...; 12 probes trio.
- s2046M2TorsionRequired_actual/holds; localArtinTorsion_holds; localArtinTorsionTopological_holds; localArtinTorsionEquiv : mu p U ≃* torsion Gal(maximalAbelianExtension p U/localField p U).
- Construction: PadicField.galAbEquiv Gal(K^ab/K) ≃* O_K^× x Multiplicative ZHat; S2089 galoisGroupEquiv; zhat_nsmul_eq_zero (Brauer.ZHat torsion-free), zhat_isOfFinOrder_eq_one, nrm_coe_eq_one_of_isOfFinOrder + torsionUnitGroupEquivMu (torsion O_K^× ≃ mu p U), torsionProdOfRightTorsionFree; compose S2027 galoisGroupMaximalAbelian.
- Finite-layer reciprocity/norm present in Artin/ArtinInertia; GaloisStructure olean rebuilt. No first missing for M2Torsion/localArtinTorsion. S2098M2aCoreActual draft is bad (absurd bug), do not use.
- Our probe confirms localArtinTorsion_holds/localArtinTorsionTopological_holds/localArtinTorsionEquiv axioms trio. M2a CLOSED (core+torsion). Remaining M2c carrier comparison; M2b Brauer.ArtinTransfer.


## 2026-11-02 S2098: M2a-core 与 M2a-torsion 实际 inhabit；剩余仅 (M2c)/(M2b)

- S2098M2aCoreActual.lean, SHA 2BAD79C1..., 437 行, EXIT=0; olean 468328 B SHA 0C5131F2...; axioms trio (19 probes). Consumer _S2098Consumer.lean EXIT=0.
- S2099 之后的新事实：LANA port 已有 `PadicField.artinCompletionEquiv : Kˣ-hat ≃ₜ* Gal(K^ab/K)`（Reciprocity/ProfiniteCompletion.lean，消费 PadicField.existence + denseRange_artin）与 `PadicField.galAbEquiv : Gal(K^ab/K) ≃ₜ* 𝒪ˣ × Ẑ`（Reciprocity/GaloisStructure.lean）。故 S2027 的 (M2a-core) 与 (M2a-torsion) 不再 missing：
  - unitProfiniteCompletionEquivGal U = artinCompletionEquiv.trans (S2089 galoisGroupEquiv)；unitProfiniteCompletionEquivGal_eta 证明它在 Lˣ→Lˣ-hat 上是 artinMaximalAbelian；localReciprocityIsomorphism_holds 给出 S2027 命题的 inhabitant。
  - localArtinTorsionEquiv : mu U ≃* torsion Gal(L^ab/L)，由 galAbEquiv + 新引理 zhat_nsmul_eq_zero（Ẑ 加法无挠）、zhat_isOfFinOrder_eq_one、torsionProdOfRightTorsionFree、nrm_coe_eq_one_of_isOfFinOrder、torsionUnitGroupEquivMu 组成。S2027 记录的“需要 Lˣ ≅ μ × pro-p × Z”可以用 Gal 侧分解绕过。
- 仍缺（exact, 按依赖序）：(M2c) ∀U Nonempty (torsion (Abelianization ↥U) ≃* torsion (TopologicalAbelianization (localGaloisGroup U))) —— abelianizationToTopological 只有 surjective；(M2b) transfer_compat（rec_H ∘ N = V ∘ rec_K）。LocalArtinSourceData 由 (M2c) 构造（artin 字段无条件），LocalReciprocityData/muQZComparison/muHatComparison 由 (M2c)+(M2b) 得到；无 fake。
- 构建注记：Reciprocity.GaloisStructure 原先无 olean；lake build 重建 8717 jobs 成功。其间 Reciprocity.ArtinContinuous 在并发 Lean 进程下 std::bad_alloc 失败一次，单独重跑成功（资源问题）。


## 2026-11-02 S2098 M2a-core independent; LocalArtinSourceData only M2c/M2b

- S2098M2aCoreActual.lean, SHA 2BAD79C1..., 437 lines, EXIT=0; olean 468328 B SHA 0C5131F2...; 19 probes trio; consumer EXIT=0.
- artinMaximalAbelian, artinMaximalAbelian_apply, artinMaximalAbelian_eq_one_iff; unitProfiniteCompletionEquivGal, _eta; localReciprocityIsomorphism_holds; localArtinTorsionEquiv; localArtinTorsion_holds; localArtinSourceArtin; localArtinSourceCarrierMissing := forall U, profiniteTorsionComparison p U (M2c); localArtinSourceDataOfComparison; localReciprocityTransferCompatibility (M2b); localReciprocityData_of_source; localReciprocityOnTorsion_of_source; muQZComparison_of_source/muHatComparison_of_source.
- LANA port has PadicField.artinCompletionEquiv and galAbEquiv (GaloisStructure rebuilt); M2a-core/torsion no longer gaps. Exact remaining: M2c carrier comparison; M2b transfer compatibility. S2093/S2102 independently consistent.

## 2026-11-02 S2104: M2a-torsion on the completion carrier actual

- S2104TorsionCompletionActual.lean, SHA 711306827BB0BDD3C9494BDAFDFB0C0E5791A792E4E522A4DDB928E907C7D022, 123 lines, EXIT=0; olean 52544 B SHA 54C2F82ECA4FACB3E4B4AB36FA4A6DFC826EDEC9839C4CC6067FE67DC3151259; 5 probes axioms trio; independent consumer _s2104_consumer.lean EXIT=0 exact target.
- unitProfiniteCompletionCommGroup : CommGroup (unitProfiniteCompletion p U), via MonoidHom.commGroupOfInjective on S2093 localReciprocityIsomorphism (target Gal commutative). This supplies the CommGroup instance flagged missing in the S2093 report; the underlying group structure is the existing one, only mul_comm is added.
- torsionCompletionEquivMu : CommGroup.torsion (unitProfiniteCompletion p U) ≃* mu p U = torsionMulEquiv localReciprocityIsomorphism trans (S2102 localArtinTorsionEquiv).symm. TorsionCompletionIso (exact S2093 missing type) inhabited; muEquivTorsionCompletion; topological form re-exported.
- No new structure theorem/API missing: torsion(K^×-hat)=mu(K) follows from PadicField.artinCompletionEquiv + galAbEquiv decomposition (Zhat torsion-free, torsion O_K^×=mu) in S2102. M2c carrier comparison and M2b Brauer.ArtinTransfer remain outside.

## 2026-11-02 S2104TorsionCompletion: M2a-torsion completion actual

- S2104TorsionCompletionActual.lean, SHA 71130682..., 123 lines, EXIT=0; olean 52544 B SHA 54C2F82E...; 5 probes trio; consumer EXIT=0.
- unitProfiniteCompletionCommGroup : CommGroup(unitProfiniteCompletion) via MonoidHom.commGroupOfInjective on S2093.localReciprocityIsomorphism.toMonoidHom; underlying Group unchanged.
- torsionCompletionEquivMu : CommGroup.torsion(unitProfiniteCompletion) ≃* mu p U := torsionMulEquiv localReciprocityIsomorphism trans (localArtinTorsionEquiv).symm; TorsionCompletionIso inhabited; torsionCompletionIso_holds; muEquivTorsionCompletion; torsionTopologicalEquivMu_holds.
- No structure theorem missing; S2102 derives from galAbEquiv/ZHat torsion-free/torsion O_K^×=mu. M2c/M2b remain.

## 2026-11-02 S2103D9Prestack: prestack half reduced to SlicePushNaturality

- S2103D9PrestackActual.lean, SHA 81721672..., 286 lines, EXIT=0; olean 211328 B SHA 3D516281...; axioms trio.
- Proved generic site (C,J), category A, S:C, M N: slicePush X = iteratedSliceBackward sheafPushforward, Full+Faithful from dense-subsite; presheafHom_obj_eq rfl; sliceComparison bijective; SlicePushNaturality M N; naturality_iff_exists_natIso; slicePushNaturality_iff_pullHom; isSheaf_of_naturality; isPrestack_of_naturality; S2103FirstMissing K; S2093SheafPrestack_of_firstMissing/presheafHom form.
- NOT PROVED: SlicePushNaturality. Exact first missing: (a) no backward-form naturality iso iteratedSliceBackward Y2 ⋙ Over.map q ≅ Over.map q.left ⋙ iteratedSliceBackward Y1 (only forward refl); (b) no lemma identifying overMapPullbackComp with iterated-slice naturality isos (item 5 RHS). IsDenseSubsite.sheafEquiv not instantiable (needs limit shape); Full/Faithful available. overMapPullbackComp.hom.app M unpacks to whiskerRight (NatTrans.op (Over.mapComp f g).symm.inv) M.1; need Over ext + proof irrelevance normalization of mapComp' eqToHom transports. No fake.

## 2026-11-02 S2046 M2c canonical reduction surface

- S2046M2cCanonicalReduction.lean, SHA E6B0CBE9..., EXIT=0; olean SHA 9A66DDCB...; definitions only, no theorem axioms.
- Built S2046M2cCanonicalMap = torsionMap(abelianizationToTopological); exact Required props; commutator-closed sufficient condition and exact implication target.
- Missing: injectivity/canonicalTorsionComparison; no counterexample yet. M2a closed via S2102/S2104. No fake.

## 2026-11-02 S2108 pastedTransport completed; CAUTION false hG still in TwoFullInputs

- S2108PastedTransportActual.lean, SHA 24356507..., 348 lines, EXIT=0; olean 164672 B SHA?; 10 probes trio; consumer EXIT=0.
- Proved S2108LiftTwoCellToY (arbitrary bicategory), S2108IsoWitnessY/EssSurjY, S2108SwapEssSurj, S2108SwappedWitness, S2108PastedWitness, S2108PastedFull, S2108PastedTransport (exact field function), S2108TwoFullInputs (hBig : S2094BigSquareEssSurj) (hG : S2094GPresentationConeEssSurj), S2108BaseChangePullback_of_rightCancel (hRC hBig hG hg): S2086BaseChangePullback hg.
- CAUTION: S2108TwoFullInputs still takes hG : S2094GPresentationConeEssSurj, which S2100 REFUTED. Thus this path is vacuous unless hG is replaced by S2100StrongGPresentationInput / strong finite-etale presentations (S2103). The message claiming only hRC remains is too optimistic; D6(c) still needs strong-presentation replacement + S2094BigSquareEssSurj + right-cancel.
- Do not count S2108 as eliminating the false input; adapt to strong presentation.

## 2026-11-02 S2091H2Zhat: H²(G_v, μ̂^Z) = Ẑ ported; S2036 (M3) = cochain-model comparison

- S2091H2ZhatActual.lean, SHA 7EEBB9A9672D12F3922574C9D40C4AB0AD3A5808F3B66CB812E568B5A7188336, 227 lines, EXIT=0; olean 123960 B SHA CB1D195CF19F5E96F76BDFBB43D6F11B3CCB361A240F6D9BD8B8AA3592B42715; axioms: propext, Classical.choice, Quot.sound (zhatMulEquivBrauer only propext, Quot.sound). Report: tmp/sheaf/xif/paper/S2091H2ZhatActual.md.
- Ported the import closure of LocalClassFieldTheory.Brauer.H2ZHat from tmp/local-cft-port/local-class-field-theory-main: 74 modules (66 LocalClassFieldTheory + 8 ContinuousKummerTheory), all compiled EXIT=0 (67 in this session, 7 already present), oleans in D:\lean\.lake\build\lib\lean under their upstream module names; records tmp/local-cft-port/_s2091_final.tsv, compiler logs _s2091_logs/. Sources untouched; only flag added is -DmaxHeartbeats=4000000 (Reciprocity/LevelNeukirch.lean:82 exceeds the default 200000). Upstream tree scanned: no sorry/admit/axiom. Side effect: LocalClassFieldTheory.Reciprocity.* (PadicField.artin etc.) and Brauer.* oleans are now importable from the project.
- h2ZHatOneEquiv_of_port : Brauer.H2ZHatOne Q_p (AlgebraicClosure Q_p) ≃* Multiplicative Zhat (port PadicField.h2ZHatOneEquiv at the project's actual local field; h2ZHatOneEquiv_of_port_apply records that the n-th component is h2MuEquiv of the n-th projection). brEquivQZ : Br(Q_p) ≃* Q/Z (port PadicField.invEquiv). h2MuEquiv_actual : H²(Q_p, μ_n) ≃* Z/n. gv_eq_absoluteGalois : Gv p = (AlgebraicClosure Q_p ≃ₐ[Q_p] AlgebraicClosure Q_p) (rfl); zhatMulEquivBrauer : S2036 Zhat ≃* Brauer.ZHat (the two Ẑ types are definitionally equal).
- PsiCnsH2Normalization_iff_limitComparison : S2036's PsiCnsH2Normalization p ↔ PsiCnsH2LimitComparison p := Nonempty (PsiCnsH2 p ≃* Brauer.H2ZHatOne Q_p (AlgebraicClosure Q_p)). Both directions proved; the conditional reduction PsiCnsH2Normalization_of_limitComparison is the forward one. The unconditional inhabitant is NOT obtained and is not claimed.
- Exact first missing (three unformalized steps): (G1) PsiCnsCyclotome p = Hom(Q/Z,(O^tri)^x) with its pointwise compact topology ≅ lim_n μ_n as topological G_v-modules (project has Hom(Q/Z,μ) ≅ Q/Z and torsion units ≅ Q/Z, not the equivariant limit); (G2) continuous-cochain H² into the compact cyclotome vs levelwise locally-constant H² plus the inverse limit (Z²_cont(G,lim μ_n) ≅ lim Z²(G,μ_n) and the coboundary lift); (G3) lim¹_n H¹(G_v,μ_n) = 0 (each H¹ finite). Neither mathlib, the project nor the port formalizes any of the three.
- Cor110bLayersMissing_of_M2_of_comparison_of_M4 assembles (M2) + comparison + (M4) into S2036's Cor110bLayersMissing.
- Next executable step: abstract theorem ContH2 G (lim M_n) ≃* lim_n ContH2 G M_n for G profinite and M_n finite discrete, starting with "continuous map from a compact totally disconnected space to a discrete space is locally constant" (absent from mathlib).


## 2026-11-02 S2091: H2=Zhat port and conditional M3 reduction

- S2091H2ZhatActual.lean, SHA 7EEBB9A9..., 227 lines, EXIT=0 (-DmaxHeartbeats=4000000); olean 123960 B SHA CB1D195C...; all theorems axioms trio.
- LCFT Brauer/H2 port: Brauer/H2ZHat.lean h2ZHatOneEquiv : H2ZHatOne K Ω ≃* Ẑ; Brauer/KummerH2 h2MuEquiv; Invariant invEquiv Br(K)≃Q/Z; CorBr; ArtinPairing; ContH2; ClassFieldAxiom proved. 74-module import closure compiled (68 this session; 6 CK reused). No sorry/axiom. Side effect: Reciprocity.*/Brauer.*/ClassFieldAxiom.*/PadicField.* oleans importable.
- Deliverable: zhatMulEquivBrauer : Multiplicative Zhat ≃* Multiplicative Brauer.ZHat; gv_eq_absoluteGalois; brEquivQZ; h2MuEquiv_actual; h2ZHatOneEquiv_of_port; PsiCnsH2LimitComparison p := Nonempty(PsiCnsH2 p ≃* Brauer.H2ZHatOne Qp Ω); PsiCnsH2Normalization_of_limitComparison; limitComparison_of_PsiCnsH2Normalization; PsiCnsH2Normalization_iff_limitComparison; Cor110bLayersMissing_of_M2_of_comparison_of_M4.
- Exact missing for unconditional M3: (G1) PsiCnsCyclotome p = Hom(Q/Z,(O^tri)^x) compact topology ≅ lim μ_n as topological G_v-modules (project has Hom(Q/Z,μ)≅Q/Z, torsion units≅Q/Z, not equivariant limit); (G2) S2036 uses all continuous cochains G×G -> compact cyclotome, port uses levelwise locally-constant cochains into finite μ_n; need Z2_cont(G,lim μ_n) ≅ lim Z2(G,μ_n) and coboundary lift; (G3) lim1 H1(G_v,μ_n)=0. Next: abstract ContH2 G (lim M_n) ≃* lim ContH2 G M_n; sub-lemma continuous map compact totally disconnected -> discrete is locally constant absent from mathlib. Target accepted NO for unconditional M3.

## 2026-11-02 S2109 strong-input butterfly (replaces false hG)

- S2109StrongButterflyActual.lean, SHA D14CB121..., 66 lines, EXIT=0; olean 60792; axioms trio.
- S2109StrongPastedFull hg := S2094BigSquareEssSurj + pasted-square full data for strong presentations ((hg...).baseChange...).toWeak. S2109StrongBaseChangePullbackOfInputs hRC hg h : S2103StrongBaseChangePullback hg via S2097 right-cancel. S2109D6FiniteEtaleOfStrongInputs hRC hg h : D6(c). No refuted S2094GPresentationConeEssSurj.
- Remaining: S2109StrongCospanGMapFiniteEtale (strong g.map certificate); S2109StrongPastedFull (big-square full + strong pasted transport); S2097RightCancelStatement. No fake.

## 2026-11-02 S2105 M2b Brauer port DONE: PadicField.artin_transfer actual

- Brauer.ArtinTransfer EXIT=0; source tmp/local-cft-port/Brauer/ArtinTransfer.lean SHA F7D422B1...; olean 1,099,768 B SHA 68F95A3F...; axioms trio.
- Copied all 23 Brauer files; import-prefix adaptation only (38 lines); non-import lines text-identical; no sorry/admit/axiom. ArtinTransfer closure 16/16; all 23/23 oleans. lakefile registers Brauer lib.
- PadicField.artin_transfer (K' : IntermediateField K Ω) (a : K^x) (g : Gal(Ω/K)) (hg : restrictNormalHom (maxAbelian K Ω) g = artin a) : artin p K' Ω (Units.map (algebraMap K K') a) = ver p K' g. PadicField.exists_lift_artin supplies g. Probe trio for artin_transfer/transfer_eq_prod_kappa/corChar/uSum/corLocChar/corBr_carryClass/pairing_corLocChar/ver/corBr/invEquiv_corBr.
- Downstream M2b bridge/consumer not done; need localReciprocityTransferCompatibility from artin_transfer.

## 2026-11-02 S2107 RightCancel reduced to canonical lift 2-cell

- S2107RightCancelActual.lean, SHA 876DA2BC..., EXIT=0; olean 393912 B; axioms trio.
- Proved S2107Sq1TwoCellExt, S2107ExtCone/ExtLift/ExtLiftToX/ExtLiftToY2, S2107ExtLiftToY (lift/liftToX/liftToY/twoCell_ext not missing), S2107CanonicalLiftTwoCell, S2107WitnessOfCanonicalTwoCell, S2107RightCancelStatement_of_canonicalTwoCell; S2107Sq1PositiveFields equivalence; S2107ImageCone/ConeComparisonFull reference.
- Exact first missing: for every cone morphism m over square1, 2-cell sigma: ExtLift s -> ExtLift t with sigma whisker D.toX1 = liftToX s ; m.toX ; (liftToX t)^-1 and sigma whisker D.toY1 = liftToY s ; m.toY ; (liftToY t)^-1. wP gives sigma0 satisfying first + D.toY1;D.toY2 composite; individual D.toY1 equation missing. Sources: (a) projection twist compatibility S2099/S2104, (b) upper-square cone comparison 2-cell fullness (S1801 TwoCellSurjTo; S1843). S1827EssSurjOf only object-level. No counterexample; no fake.

## 2026-11-02 S2110 status: canonical lift 2-cell needs upper-square 2-cell fullness

- No new accepted artifact; last S2109 SHA D14CB121..., EXIT=0, axioms trio.
- S2107CanonicalLiftTwoCell not proved. S2104 gives canonical twist for actual butterfly cone, but sigma0=wP.liftTwoCell(E m) only satisfies _toX and after D.toY1;D.toY2; missing individual D.toY1 projection equation.
- Exact first missing: upper-square cone comparison full on 2-cells (S1801 TwoCellSurjTo for D.square2 with w2), or derive toY1 equation for wP.liftTwoCell(E m) from canonical twist. No fake.

## 2026-11-02 S2046 M3/M4 port via S2091

- S2046M3M4S2091Port.lean, SHA 08C9A29E..., EXIT=0; olean SHA 7D2D04D0...; axioms trio.
- S2046H2ZHatEquiv:=h2ZHatOneEquiv_of_port; S2046BrEquivQZ:=brEquivQZ; S2046M3LimitComparisonRequired:=PsiCnsH2LimitComparison; S2046M3EquivOfLimit; S2046M3Normalization_ofLimit; S2046M3_iff_limitComparison; S2046M4KummerNormalizationRequired; S2046M4LocalUnits_sufficient.
- Exact missing G1 PsiCnsCyclotome topological G_v-module comparison; G2 ContH2/limit commutation (aggregate PsiCnsH2LimitComparison); G3 lim1 H1=0; M4 PsiCnsKummerNormalization. M2c separate. No fake.

## 2026-11-02 S2110 strong two-full-inputs: S2108 pasted transport adapted to the strong input (false hG removed)

- S2110StrongTwoFullInputsActual.lean, 17,375 B, SHA256 F69A74C70FD86C1E60A8654507225CB23E0B0D46F93BD7F95CDE73FE0B2DA2EE, EXIT=0; olean 93,736 B SHA256 89FB37903ED7D34411970A3B9D10313C4DB7F63091E6F61A292388C13C812966; axioms propext/Classical.choice/Quot.sound; import-consumer _s2110consumer.lean EXIT=0.
- S2110StrongBaseChangePullback hG: strong-indexed analogue of S2086BaseChangePullback for S2100StrongGPresentationInput. S2110PastedSquareFull / S2110StrongPastedTransport: S2108's transport applied to a strong presentation's toWeak with coneEssSurj. S2110StrongTwoFullData + .ofInputs: honest replacement of S2097TwoFullInputs/S2108TwoFullInputs, no S2094GPresentationConeEssSurj. S2110BaseChangePullback_of_twoFullInputs: right-cancel step. S2110StrongGPresentationTwoFullInputs: hRC + hBig + strong input.
- Main: S2110StrongTwoFullInputs hRC hBig hg : S2086BaseChangePullback (S2110StrongCospanToWeak hg) for hg : S2103StrongCospanGMapFiniteEtale; S2110StrongCospanPullback : S2103StrongBaseChangePullback hg; consumers S2110ToAOfStrongInputs : S2044ToAFiniteEtaleField and S2110D6FiniteEtale : S2043FirstMissingFiniteEtale. This constructs the pasted data that S2109StrongPastedFull still leaves as a hypothesis.
- Remaining hypotheses: S2097RightCancelStatement and S2094BigSquareEssSurj. No claim for arbitrary weak hg. No sorry/new axiom; no existing Lean file changed.


## 2026-11-02 S2110 strong assembly; S2101 site naturality + projection compatibility

- S2110StrongTwoFullInputsActual.lean, SHA F69A74C7..., 362 lines, EXIT=0; olean 93736 B SHA 89FB3790...; 11 probes trio; consumer EXIT=0.
- Proved S2110PastedSquareFull/StrongPastedTransport (S2108 transport on strong Pg), S2110StrongTwoFullData/.ofInputs (fields bigSquare, strongPresentation, pastedTransport; no S2094GPresentationConeEssSurj anywhere), S2110BaseChangePullback_of_twoFullInputs, S2110StrongGPresentationTwoFullInputs, S2110StrongCospanToWeak/ToInput, S2110StrongTwoFullInputs (hRC hBig hg) : S2086BaseChangePullback (S2110StrongCospanToWeak hg); S2110StrongCospanPullback; S2110ToAOfStrongInputs; S2110D6FiniteEtale. Only remaining hypotheses S2097RightCancelStatement + S2094BigSquareEssSurj; false hG removed. Probe confirms axioms trio.
- S2101SiteNaturalityActual.lean, SHA E647EAC8..., 451 lines, EXIT=0; olean 597488 B SHA F8A8801D...; probes trio. Proved S2096FibreIsoOfConeIso, S2096ProjectionCompat/Compatibility (twist), S2096FibreIso, _hom_fst/_snd, S2096SiteIso, S2096LiftUniq_of_projectionCompat. Site naturality no longer missing once compatibility supplied; projection-only insufficient; S2095BigLiftUniq not derivable from projection isos alone. Same obstacle as S2099TwistAt; S2104 canonical twist gives actual butterfly compatibility. No fake; no modification S1893/S2076.

## 2026-11-02 S2109 M2c carrier comparison: exact reduction; first missing = closedness of the abstract commutator

- S2109M2cCarrierActual.lean (tmp/sheaf/xif/paper/), 17,616 B, SHA256 F0F760C664A5B08B95CEB6C7BB6FDAEA924B851564E7F90E24A5B4183BA12DDB, EXIT=0; olean 272,720 B SHA256 8CF55FC52D54F4ECD89B17D32E265DD88E9CE309B5981CABBC5895922F3CC320 at .lake/build/lib/lean/tmp/sheaf/xif/paper/; 14 #print axioms all = propext/Classical.choice/Quot.sound only; no sorry/admit/axiom (token appears only in docs).
- Proved unconditionally: general torsion calculus (torsionMap_injective_iff: injective <=> ker f torsion-free; torsionMap_surjective_iff: surjective <=> every target torsion lifts to a source torsion; torsionMap_bijective_iff); abelianizationFromTopological + the two inverse laws, abelianizationToTopological_bijective_of_commutatorClosed, canonicalTorsionComparison_of_commutatorClosed, carrierComparison_of_commutatorClosed (exact M2c type CommGroup.torsion (Abelianization ↥U) ≃* CommGroup.torsion (TopologicalAbelianization (localGaloisGroup p U))), carrierComparison_of_torsionCriteria, profiniteTorsionComparison_of_commutatorClosed, localArtinSourceDataOfCommutatorClosed (S2027 LocalArtinSourceData with M2a from S2102 and carrier supplied).
- Exact first missing, recorded never assumed: M2cFirstMissing p := forall U, (commutator (localGaloisGroup p U)).topologicalClosure = commutator (localGaloisGroup p U), i.e. closedness of the abstract commutator [U,U]. Absent from Mathlib v4.32.2, S2027, S2017, S2093, S2102 and the LANA port (grep confirmed). It is not a general fact: the abstract commutator is only a countable union of compact (closed) images, finite quotients see only the closure, and general compact groups fail this; so any proof must use G_L specifically (strong completeness a la Nikolov-Segal, not formalized).
- Consequence: M2a closed, but M2c does not follow from the tree; LocalArtinSourceData cannot be inhabited without CommutatorClosed or an equivalent torsion-lifting / kernel-torsion-free input. Alternative unblock (needs user target-lock decision, not done): restate S2011/S2024 levelwise statement on the profinite carrier, where S2102's localArtinTorsionTopological is unconditional. No fake; target type unchanged.


## 2026-11-02 S2109 M2c: conditional equivalence, exact first missing commutator closedness

- S2109M2cCarrierActual.lean, SHA F0F760C6..., 17616 B, EXIT=0; olean 272720 B SHA 8CF55FC5...; 14 probes trio.
- Proved torsionMap_injective_iff/surjective_iff/bijective_iff; abelianizationFromTopological and inverse laws; abelianizationToTopological_bijective_of_commutatorClosed; canonicalTorsionComparison_of_commutatorClosed; carrierComparison_of_commutatorClosed (exact M2c type); carrierComparison_of_torsionCriteria; profiniteTorsionComparison_of_commutatorClosed; localArtinSourceDataOfCommutatorClosed.
- Exact first missing M2cFirstMissing := forall U, (commutator (localGaloisGroup p U)).topologicalClosure = commutator (localGaloisGroup p U). Not in Mathlib/tree/LANA. Abstract commutator is countable union of compact images; general compact groups fail; proof needs G_L specifically/strong completeness (Nikolov-Segal) absent. Cannot derive from compactness/finite quotients. Alternative profinite-carrier restatement would bypass M2c but changes locked target; requires user instruction; not done.
- Keep abstract carrier target unchanged.

## 2026-11-02 S2116 commutator closedness: width criterion, exact reduction, two named deep inputs

- S2116CommutatorClosedActual.lean (tmp/sheaf/xif/paper/), 391 lines, SHA256 FDDBF32B008079445483126D9F6E59A58AE0A8C8628BFDD8D1CC9EFD24B4D918, EXIT=0 (lake env lean -j1 -R . -o); olean 365,472 B SHA256 90A688711E4C9ACF10A263394713D25D46F0F28B9E670CA16E066A1CA7FF4096 at .lake/build/lib/lean/tmp/sheaf/xif/paper/; 24 #print axioms all = propext/Classical.choice/Quot.sound only (commutatorWord: propext); no sorry/admit/axiom (token only in docs). Log: S2116Compile.log / S2116Axioms.log.
- Unconditional (general compact-group mechanism): commutatorWord (products of N commutators as image of (G x G)^N), continuous_commutatorWord, commutatorWord_mem_commutator, commutator_eq_closure_iUnion_commutatorWord (abstract commutator = subgroup generated by the countable union of the compact sets C_N: exact failure point for closedness), isClosed_commutator_of_boundedWidth and commutator_topologicalClosure_eq_of_boundedWidth (bounded commutator width => [G,G] closed), isClosed_commutator_of_isOpen (second criterion, not applicable to G_L: abelianization surjects onto Zhat).
- Unconditional at the M2c level: CommutatorWidthBoundedBy/CommutatorWidthBounded/CommutatorWidthInput; commutatorClosed_of_widthBounded; m2cFirstMissing_of_widthInput; commutatorClosed_of_injective (injectivity of abelianizationToTopological alone forces closedness) hence commutatorClosed_iff_bijective: closedness of [G_L,G_L] <=> bijectivity of the carrier map, so M2c's exact missing content is the missing injectivity of Abelianization U -> TopologicalAbelianization G_L; abelianizationEquivGaloisGroupMaximalAbelian (closedness => Abelianization U ≃* Gal(L^ab/L), the carrier S2098/S2102 identify with O^x x Zhat via PadicField.galAbEquiv).
- Payload from the width input (exact S2027/S2109 types, target unchanged): carrierComparison_forall_of_widthInput (CommGroup.torsion (Abelianization ↥U) ≃* CommGroup.torsion (TopologicalAbelianization (localGaloisGroup p U))), canonicalTorsionComparison_forall_of_widthInput, profiniteTorsionComparison_forall_of_widthInput, localArtinSourceDataOfWidthInput (artin from S2102, carrier supplied), localReciprocityOnTorsion_of_widthInput.
- Two deep inputs recorded as Props, never assumed: (1) TopologicallyFinitelyGenerated U (G_L topologically finitely generated; classical via finiteness of extensions of a p-adic field of given degree / Krasner, absent from Mathlib and the tree); (2) NikolovSegalCommutatorWidth (in every topologically finitely generated profinite group the abstract commutator subgroup is a bounded product of commutators; Nikolov-Segal Ann. Math. 165 (2007), pro-p case Jaikin-Zapirain Rev. Mat. Iberoam. 24 (2008)). m2cFirstMissing_of_nikolovSegal proves (1)+(2) => M2cFirstMissing => M2c. Literature wording not re-verified verbatim (network blocked this session); it enters only as a hypothesis, so no claim depends on it.
- Honest status: M2cFirstMissing NOT proved; no concrete U has CommutatorClosed. Closedness is not derivable from compactness/finite quotients; p-adic analytic structure exists only for the pro-p core (wild inertia), which is closed of infinite index, so it does not transfer; strong completeness is a different (finite-index) statement. No fake, no target change to the profinite carrier.


## 2026-11-02 S2116: M2c reduced to two named deep group-theory inputs

- S2116CommutatorClosedActual.lean, SHA FDDBF32B..., 455 lines, EXIT=0; olean 365472 B SHA 90A68871...; 23/24 probes trio, commutatorWord [propext]; no sorry.
- Proved: commutatorWord continuous compact image, commutator_eq_closure_iUnion_commutatorWord; isClosed_commutator_of_boundedWidth; commutator_topologicalClosure_eq_of_boundedWidth; isClosed_commutator_of_isOpen; commutatorClosed_of_injective; commutatorClosed_iff_bijective (CommatorClosed U <-> Bijective abelianizationToTopological); exact payload carrierComparison_forall_of_widthInput, canonicalTorsionComparison_forall_of_widthInput, profiniteTorsionComparison_forall_of_widthInput, localArtinSourceDataOfWidthInput, localReciprocityOnTorsion_of_widthInput; abelianizationEquivGaloisGroupMaximalAbelian.
- Two exact missing deep inputs: TopologicallyFinitelyGenerated U (exists finite s with closure s = top; Krasner/finite extensions missing) and NikolovSegalCommutatorWidth (every topologically finitely generated profinite group has bounded commutator width; Nikolov-Segal 2007/Jaikin-Zapirain 2008; not in tree/Mathlib). m2cFirstMissing_of_nikolovSegal: both -> M2cFirstMissing -> M2c.
- No unconditional M2c; target not changed to profinite carrier; no fake. Missing can be attacked via f.g. G_L + NS width; strong completeness not enough alone.

## 2026-11-02 S2115 upper 2-cell fullness actual; remaining pasted comparison twist

- S2115UpperTwoCellFullActual.lean, SHA 5F4242BA..., 578 lines, EXIT=0; olean 508808 B; axioms trio; consumer EXIT=0.
- Proved S2115ImageCone_commutes_app; S2115ImageConeTwistAt; S2115ProjectionCompat_of_twist; S2115UpperTwoCellFull (twist -> iso h (S2076Witness.lift c) with exact whiskerings via S2101); S2115ImageConeTwoCellFull (S1801-shape corollary).
- Literal S1801 TwoCellSurjTo is wrong target (forces every same-leg cone to be canonical image cone via S2115SameLegsTwist); not formalized refutation but honest boundary. S2104 canonical twist only special case h=witness lift.
- Exact first missing for right-cancel: S2115PastedComparisonTwist for D=S2097Pasting and every wP, every cone s over D.square1: alpha=S2107LiftToYIsoX, beta=S2107LiftToYIsoY satisfy cone-morphism equation (alpha whisker D.x2) ; sq2.commutes = imageCone.commutes ; (beta whisker D.y2). Proved consequences: implies twist and Nonempty Iso (wP.lift(E s);D.toY1) (S2076Witness.lift (S2107Sq2ConeOf D s)); not implied by 7 fields. Combined with S2094BigSquareEssSurj h2 gives S2107ExtLiftToY/lower witness. Next: prove for concrete wP=S2108PastedWitness using gamma + S2086Cone.commutes.

## 2026-11-02 S2106 M3: preservesPullbacks + preservesFiniteCoproducts actual; frozen remaining three FALSE

- S2106CurveM3Actual.lean, SHA 49863B62..., 596 lines, EXIT=0; olean 708032 B SHA 34D15960...; audit green; axioms trio.
- Proved preservesPullbacks_typeLevel (WalkingCospan) and preservesFiniteCoproducts_typeLevel for curveFiber K Omega x, all [Field Omega]; certificate layers certificate_preservesPullbacks_m3/certificate_preservesFiniteCoproducts_m3.
- CRITICAL: S2088 frozen RemainingTypeLevel last three (preservesEpis, preservesQuotientsByFiniteGroups, reflectsIsos) are FALSE for arbitrary [Field Omega]. Counterexample K=Omega=Q, x=(0,0) on y^2=x^3-x, K'=Q(sqrt2), Y=CurveBase Q x_SpecQ Spec K'; f:Y->CurveBaseQ finite etale surjective but F(Y)=empty, F(X)={x}; not preservesEpis. g=fold (X⊔Y)->X has F(g) bijective but not iso => not reflectsIsos. Z/2 Galois action quotient colimit X but F(colim)={x} vs empty=> not preservesQuotientsByFiniteGroups. Formal interfaces PreservesEpisCounterexample/ReflectsIsosCounterexample and not_..._of_counterexample machine-checked; concrete cover construction documented not formalized.
- Proved RemainingTypeLevelThree (frozen three fields), remainingTypeLevel_of_three, certificate_of_remaining_three, s2106_cardV_of_remaining_three (M1 via S2087, M2 via S2081). Target lock EXIT=0.
- Correct target should add [IsSepClosed Omega] (geometric point); then first gaps: (1) separably closed field nonzero finite etale algebra splits (Omega-point exists) + scheme epi=>surjective; (2) F(quotient)=quotient(F); (3) fiber cardinality locally constant => degree one finite etale iso. User decision required before changing target.

## 2026-11-02 S2112 final: Z^2 exchange actual; H^2 injectivity = CoboundaryLift

- S2112ContH2LimitActual.lean, SHA 1C3723DB..., 836 lines, EXIT=0; olean 1,993,472 B; 18 probes trio.
- Proved continuous_isLocallyConstant_of_discrete, compact_totallyDisconnected_isLocallyConstant, finite_range_of_compact_of_discrete (core already Mathlib; finite-quotient refinement absent not needed); limSubgroup/continuous_lim_iff; coefficient system/limitAction; oneCochainEquiv/twoCochainEquiv; deltaTwo_coord; mem_twoCocycle_iff_levels; twoCocycleExchange : Z^2_cont(G,lim A) ≃ lim_n Z^2_cont(G,A_n); degree-two comparison h2Comparison : H^2_cont(G,lim A) ->* lim H^2; h2Comparison_injective_iff : Injective h2Comparison <-> CoboundaryLift; coboundaryLift_of_bijective; bijective_of_coboundaryLift_of_surjective.
- Exact remaining: CoboundaryLift (levelwise coboundary => global coboundary) = concrete lim^1_n H^1(G,A_n)=0; true arithmetic case H^1(G_v,mu_n) finite; surjectivity standard but not formalized. Full abstract H^2 exchange not proved. No topological API missing; no fake.

## 2026-11-02 S2117: G_L top-fg reduced to G_Qp top-fg

- S2117TopFGActual.lean, SHA BEFA34EB..., 17887 B, EXIT=0; olean 397912 B SHA F5468D0D...; main 6 declarations axioms trio; no sorry.
- Proved topologicallyFinitelyGenerated_openSubgroup; topologicallyFinitelyGenerated_of_continuous_surjective; continuous_fixingSubgroupEquiv; continuous_localGaloisGroupEquiv; topologicallyFinitelyGenerated_of_padicAbsoluteGalois; topologicallyFinitelyGenerated_forall; m2cFirstMissing_of_padicTopFG_and_nikolovSegal (conditional).
- Exact first missing PadicAbsoluteGaloisTopologicallyFinitelyGenerated := exists finite s in Gal(Qbar_p/Q_p) with closure top. Not proved; Mathlib lacks local CFT/Demushkin/Jannsen-Wingberg. krasner_available proved from Mathlib; missing FinitelyManyExtensionsOfDegree(n)/FinitelyManyExtensionsOfLocalFieldOfDegree(L,n)/FinitelyManyOpenSubgroupsOfIndex(n); extension finiteness alone does not imply f.g. (profinite product C_{p_n}). Converse literal U=top -> G_Qp f.g. not formalized. No target change, no fake.

## 2026-11-02 S2113 M2b transfer: conditional reduction, exact missing

- S2113M2bTransferActual.lean, SHA D5CED7AA..., 22828 B, EXIT=0; olean 678088 B SHA F452A450...; axioms trio; no sorry.
- Proved artinTransfer_fixedField (PadicField.artin_transfer specialised to FH H h); localArtinTorsionEquiv_apply (M2a torsion equiv = Artin map on roots of unity); galoisGroupMaximalAbelian_mk; galoisGroupEquiv_restrictNormalHom; kappa_of; canonicalEquiv_apply; TransferBridge -> CanonicalTransferCompat; M2c + TransferBridge -> LocalReciprocityData/muQZComparison/muHatComparison; S2098 localReciprocityData_of_source under explicit hcanon.
- NOT proved: S2098 localReciprocityTransferCompatibility hc for arbitrary hc. Exact missing (A) TransferBridge: abstract Verlagerung transported by kappa equals Galois norm/Artin transfer on roots of unity; Mathlib MonoidHom.transfer has no naturality-under-iso. (B) VerCarrierComparison: PadicField.ver lands in Gal(maxAbelian(FH H h)/FH H h), not S2027 Gal(maximalAbelianExtension H/localField H); same subset different Algebra instances, no transport lemma. (C) hcanon: S2098 hc uses Nonempty.some arbitrary equivalence; need identification with canonical carrier.
- No fake; M2b still open.

## 2026-11-02 M2b(B) carrier transport exact missing

- S2103LocalArtinSourceDataM2c stays actual: localArtinSourceDataOfCarrier hC, M2a S2102, only M2c missing.
- M2b(B): to use PadicField.ver p (K' : IntermediateField (localField p K) Ω) need localField p H as intermediate field of localField p K. Correct construction found: Subfield.extendScalars (F := (FixedField p K).toSubfield) (E := (FixedField p H).toSubfield) fixedField_le; carrier FixedField p H, base localField p K.
- Exact first missing: FiniteDimensional (localField p K) ↥(K' h) and induced Algebra (localField p K) ↥(K' h) transport to instantiate PadicField.ver. Then galoisGroupEquiv H transports target Gal(maxAbelian (localField p H) Ω) to S2027 carrier; Algebra instance mismatch needs transport lemma.
- M2b(A): abstract verlagerungOpen vs artin_transfer naturality square still unproved; depends on M2c carrier and (B) ver carrier alignment. No fake.

## 2026-11-02 S2118 concrete pasted twist NOT proved; exact missing S2118PresentationTwist

- S2118PastedComparisonTwistActual.lean, SHA A410CAE1..., EXIT=0; olean 115360 B; axioms trio; no sorry.
- Proved S2118ConcreteWitnessTwist (target with wP=S2108PastedWitness), S2118ConcreteLift/LiftToX/LiftToY (rfl; lift=Pg.isPullback.lift of transported cone; comparisons=Pg.isPullback comparisons), S2118PresentationSquare, S2118Conv, S2118PresentationTwist (exact missing datum: twist of Pg.isPullback at transported cone), S2118ConcreteWitnessTwist_of_general, _implies_twist, _implies_liftIso.
- Missing S2118PresentationTwist is not derivable: TwoPullbackWitness has no equation relating liftToX/liftToY; S2099/S2104/S2115 argument applies verbatim at presentation square. Next: (a) add twist of isPullback as supplied field to EtaleStackBaseChangePresentation (honest geometric input, needs target/definition decision), or (b) formalize cone-category essential surjectivity -> twist for used presentations. No fake.

## 2026-11-02 S2114 canonical lift 2-cell exact equivalent to ToYEquation; missing ChosenComparisonCompat

- S2114CanonicalLiftTwoCellActual.lean, SHA B20B7F52..., EXIT=0; olean 379736 B; axioms trio (some [propext,Quot.sound]); no sorry.
- Proved Coherence.S2114PastedConeCompat; Coherence.S2114LowerLiftToACompat; S2114ExtConeHom; S2114PastedTwoCell/_toX/_toY2; S2114ToYEquation; S2114CanonicalLiftTwoCell_iff (Nonempty CanonicalLiftTwoCell <-> ToYEquation, via representable 2-cell subsingleton); S2114ToAWitness_of_canonicalLift/of_toYEquation; S2114UpperTwoCellSurjTo/From; S2114UpperCompatibleLift; S2114UpperTwist; S2114UpperTwistAt_iff_comma; S2114ChosenComparisonCompat (defined not proved).
- Exact missing S2114ToYEquation = single D.toY1 projection equation of sigma0; upper form S2114ChosenComparisonCompat (S2099/S1801 compatible lift at specific choice). S2104 canonical twist only gives canonical lift, cannot pin down Classical.choice S2107ExtLiftToY. Next: (a) add ChosenComparisonCompat/S2099CompatibleLift + choice uniqueness as explicit input; (b) remove Classical.choice via choice-free compatible comparison rebuild lower witness. No fake.

## 2026-11-02 S2114 canonical lift 2-cell; S2094 mod29 missing kernel recursion

- S2114CanonicalLiftTwoCellActual.lean, SHA B20B7F52..., EXIT=0; olean 379736 B; key probes trio (some [propext,Quot.sound]); no sorry.
- Proved Coherence.S2114PastedConeCompat; Coherence.S2114LowerLiftToACompat; S2114ExtConeHom; S2114PastedTwoCell/toX/toY2; S2114ToYEquation; S2114CanonicalLiftTwoCell_iff (Nonempty CanonicalLiftTwoCell <-> ToYEquation via representable 2-cell subsingleton); S2114ToAWitness_of_canonicalLift/of_toYEquation; S2114UpperTwoCellSurjTo/From; S2114UpperCompatibleLift; S2114UpperTwist; S2114UpperTwistAt_iff_comma; S2114ChosenComparisonCompat defined not proved.
- Exact missing S2114ToYEquation (single D.toY1 equation of sigma0); upper form S2114ChosenComparisonCompat (S2099/S1801 compatible lift at specific choice). S2104 canonical twist only canonical lift; cannot pin Classical.choice S2107ExtLiftToY. Next: choice-free compatible comparison or add chosen compat input. No fake.
- S2094Mod29IrreducibleActual.lean, SHA A59C8E26..., target s2094_f_irreducible has sorryAx (deliberate), missing. 20 polynomial certificates + Rabin criterion kernel-checked (cert_P1/R2/lin1/bez2/hfdeg axioms trio); final Frobenius chain elaboration complete in scratch _S2094gen_final4 but kernel deep recursion at final theorem; maxRecDepth 100000 deep recursion, 1000000 stack overflow. Needed kernel-friendly finite-field normalizer/Rabin gcd checker or split top-level lemmas; no native_decide, no fake axiom.

## 2026-11-02 S2120 cone-category ES + 2-cell fullness -> strong presentation twist (conditional)

- S2120PresentationTwistActual.lean, SHA256 2A778E5B4B45F77218E6D4118AE628D08D6EA88748223BA52064BF8442148D36, 23743 B, EXIT=0; olean 232512 B SHA256 8C2C2D5D5F5ACFA285EAEB28BF66BA4BCBD7E38C0917C6F5AEA324513569B64F; axioms trio; no sorry.
- Proved S2120StrongPresentationTwist (S2118 twist for StrongEtaleStackBaseChangePresentation, at Pg.toWeak/transported cone S2118Conv), S2120StrongPresentationTwist_of_S2118; S2120LiftConeMor (counit half of cone-comparison essential surjectivity at the recorded lift); S2120TwistAt_of_coneMor_and_twoCellFull and S2120Twist_of_liftConeMor_and_twoCellFull (cone morphism imageCone(lift c) -> c + S1801TwoCellSurjTo + representable-apex 2-cell subsingleton S1827SubsingletonModRep => twist); S2120PresentationLiftConeMor, S2120PresentationTwoCellFull, S2120FirstMissing; S2120StrongPresentationTwist_of_firstMissing; S2120PresentationLiftConeMor_of_strongTwist (necessity of the ES half); consumer S2120StrongPresentationTwist_for_strongTwoFullData (S2110StrongTwoFullData.strongPresentation).
- Exact missing S2120FirstMissing = (i) cone-category essential surjectivity at the recorded lift (a cone morphism from the image cone of w.lift c to c; not implied by the weak witness and not the content of S1852ConeEssSurj) AND (ii) cone-category 2-cell fullness S1801TwoCellSurjTo of Pg.toWeak.isPullback. S1852ConeEssSurj at the twist data is vacuous: its conclusion Nonempty (Iso (lift c) (lift c)) is unconditionally inhabited (S2120ConeEssSurj_twistData_trivial / _instance), so the strong field carries no comparison coherence. Twist is equivalent to (i) modulo (ii)+representability. Strong twist NOT proved unconditionally; no fake, no definition changed.


## 2026-11-02 S2120 strong-presentation twist conditional on cone morphism + 2-cell fullness

- S2120PresentationTwistActual.lean, SHA 2A778E5B..., 23743 B, EXIT=0; olean 232512 B SHA 8C2C2D5D...; axioms trio; consumer EXIT=0.
- Proved S2120StrongPresentationTwist (strong version of S2118PresentationTwist at Pg.toWeak), S2120StrongPresentationTwist_of_S2118; S2120LiftConeMor (counit half of cone-comparison ES at recorded lift); S1801TwoCellSurjTo (cone-category 2-cell fullness); S1827SubsingletonModRep; S2120TwistAt_of_coneMor_and_twoCellFull / S2120Twist_of_liftConeMor_and_twoCellFull; S2120PresentationLiftConeMor, S2120PresentationTwoCellFull, S2120FirstMissing := both; S2120StrongPresentationTwist_of_firstMissing; S2120PresentationLiftConeMor_of_strongTwist; consumer S2120StrongPresentationTwist_for_strongTwoFullData.
- KEY: S1852ConeEssSurj alone does not give twist; at twist data conclusion Nonempty Iso(lift c)(lift c) trivial; no comparison coherence. Exact missing S2120FirstMissing = (i) S2120PresentationLiftConeMor cone morphism imageCone(w.lift c)->c for transported cones; (ii) S2120PresentationTwoCellFull S1801TwoCellSurjTo of Pg.toWeak.isPullback. Neither in TwoPullbackWitness nor StrongEtaleStackBaseChangePresentation. Strong twist not unconditional; no fake.


## 2026-11-02 S2119 M2b(B) CLOSED: canonical extendScalars carrier + explicit transport

- S2119VerCarrierActual.lean (tmp/sheaf/xif/paper/), SHA256 1B2658757CF3E776805B50BC54C30A6C22B1A63574C1F3EF7C1B599121419DF6, 10297 B, EXIT=0; olean 451864 B SHA256 176D9FEDC05B33320F962BC4498548B190BE7A4FD2DF3E260DD33F3CB171FDA6 at .lake/build/lib/lean/tmp/sheaf/xif/paper/; all 10 #print axioms = propext/Classical.choice/Quot.sound; no sorry/admit/axiom. Consumer _S2119Consumer.lean EXIT=0.
- CORRECTION to the 2026-11-02 "M2b(B) carrier transport exact missing" entry: the missing FiniteDimensional/Algebra instance is not a mathematical gap. K' h := Subfield.extendScalars (F := (FixedField p K).toSubfield) (E := (FixedField p H).toSubfield) (fixedField_le p h) has carrier FixedField p H and base definitionally localField p K; K'_algebra is inferInstanceAs, and K'_finiteDimensional follows from Module.Finite.of_restrictScalars_finite ℚ_[p] (localField p K) using S2006's finite-dimensionality of the fixed field over ℚ_[p]. PadicField.ver p (K' h) typechecks; no finite-index/finrank formula needed (openness only witnesses the mathematical finiteness).
- Proved: K', K'_eq_FH (rfl), K'_algebra, K'_finiteDimensional, galK'EquivLocal (identity MulEquiv between Gal(maxAbelian(K')/K') and Gal(maxAbelian(localField H)/localField H); needed because AlgEquiv terms are not interchangeable at instances transparency despite defeq types), verCarrierComparison_K', verCarrierComparison (S2113's VerCarrierComparison, unconditionally), verS2027 (PadicField.ver transported by galK'EquivLocal and S2089's galoisGroupEquiv H to Gal(maximalAbelianExtension H/localField H)), verS2027_apply, artinTransfer_S2027 (S2113's artinTransfer_fixedField after the transport).
- Exact first missing after (B): (A) S2113's TransferBridge (abstract verlagerungOpen transported by kappa vs Galois norm/Artin transfer on roots of unity) remains unproved/unassumed; (C) S2098's Nonempty.some canonical-carrier choice remains. M2b(B) is closed; the previous ledger entry's (B) gap is superseded by this correction, not by changing the old text.

## 2026-11-02 S2119 M2b(B) CLOSED: ver carrier comparison actual

- S2119VerCarrierActual.lean, SHA 1B265875..., 10297 B, EXIT=0; olean 451864 B SHA 176D9FED...; 10 probes trio; consumer EXIT=0.
- K' h := Subfield.extendScalars (F := (FixedField p K).toSubfield) (E := (FixedField p H).toSubfield) (fixedField_le p h); carrier FixedField p H, base definitionally localField p K; K'_eq_FH rfl.
- K'_algebra canonical; K'_finiteDimensional via Module.Finite.of_restrictScalars_finite Qp using S2006 fixedFieldFiniteDimensional; PadicField.ver p (K' h) instantiates.
- galK'EquivLocal h: Gal(maxAbelian K' Ω/K') ≃* Gal(maxAbelian (localField p H) Ω/localField p H) identity on automorphisms; needed instance transport.
- verCarrierComparison_K' and verCarrierComparison (S2113 exact VerCarrierComparison) proved unconditionally; verS2027 h transports PadicField.ver; artinTransfer_S2027.
- Correction: prior "M2b(B) exact missing FiniteDimensional/Algebra" was not a real gap; (B) CLOSED. Remaining M2b: (A) TransferBridge abstract verlagerungOpen vs Galois norm/Artin transfer; (C) S2098 Nonempty.some canonical carrier choice. No fake.

## 2026-11-02 S2121 choice-free lower witness; remaining concrete twist + ToYEquation

- S2121ChoiceFreeLowerWitnessActual.lean, SHA 013304C7..., EXIT=0; olean 371984 B; axioms trio; no sorry.
- Proved S2121LiftUniq_of_projectionCompat_toA/_toB (exact projections); S2121ComparisonTwist (= S2118ConcreteWitnessTwist restriction); S2121ComparisonTwist_of_concrete; _implies_twist; S2121ReflTwist; S2121UpperComparison; S2121CanonicalComparison; S2121ChoiceFreeExtLiftToY; _toX/_toY; S2121ChoiceFreeCompat_holds (choice-free ChosenComparisonCompat, unconditional); S2121ToYEquation def; S2121RebuiltWitness (all fields except liftTwoCell_toY); S2121ToAWitness conditional.
- Remaining: (a) external S2118ConcreteWitnessTwist (= S2115PastedComparisonTwist at S2108PastedWitness; not derivable from 7 fields); (b) S2121ToYEquation not formalized: math from w2.twoCell_ext + S2114LowerLiftToACompat + pasted projection equations, but simp expansion S2107LiftToYIsoX tactic explosion >10min; need rfl-style right-associative expansion + Category.assoc only; (c) literal S2114ToYEquation/ChosenComparisonCompat involve Classical.choice comparison, not reachable from twist without identifying choice with compatible comparison/thinness. No fake.

## 2026-11-02 S2121 choice-free lower witness; S2123 presentation coherent cone morphism

- S2121ChoiceFreeLowerWitnessActual.lean, SHA 013304C7..., 566 lines, EXIT=0; olean 371984 B; axioms trio; no sorry.
- Proved S2121LiftUniq_of_projectionCompat_toA/_toB; S2121ComparisonTwist (+_of_concrete/_implies_twist); S2121ReflTwist; S2121UpperComparison; S2121CanonicalComparison; S2121ChoiceFreeExtLiftToY (+_toX/_toY); S2121ChoiceFreeCompat_holds (choice-free form of ChosenComparisonCompat, unconditional); S2121ToYEquation def; S2121RebuiltWitness; S2121ToAWitness conditional.
- Remaining: (a) S2118ConcreteWitnessTwist external; (b) S2121ToYEquation not formalized (math via w2.twoCell_ext + S2114LowerLiftToACompat + pasted projections; simp expansion tactic explosion, needs rfl right-assoc + Category.assoc); (c) literal S2114ToYEquation/ChosenComparisonCompat involve Classical.choice comparison, not reachable from twist without choice identification/thinness. No fake.
- S2123PresentationConeESActual.lean, SHA 391EEDF1..., 610 lines, EXIT=0; olean 316536 B SHA A9DCCC01...; 26 results axioms trio.
- Proved S2123LiftCoherentConeMor <-> twist; S2123LiftConeMor_of_coherent; S2123PresentationLiftConeMorCoherent <-> S2120StrongPresentationTwist; S2123PresentationLiftCoherent_of_firstMissing; S2123LiftTwoCellFull (fullness only at recorded lift); S2123TwistAt_of_coneMor_and_liftTwoCellFull; S2123PresentationConeCategoryAPI; S2123StrongPresentationTwist_of_coneCategoryAPI; S2123ConeMorphism_toY_eq; S2123LiftConeMorAt_iff_residual; S2123EssSurjAtLift_trivial/_of_essSurj/_unique; S2123PresentationStrongFieldAtLift.
- Exact first missing S2123PresentationLiftConeMorCoherent (= S2118PresentationTwist = S2120StrongPresentationTwist): recorded comparisons (liftToX,liftToY) are a cone morphism at S2118Conv. Strong field at recorded lift is trivially true and carries no comparison equation. S2115 fullness is iso-comma; S2104 twist is fibre-level at butterfly lift; neither at presentation square. No fake.

## 2026-11-02 S2122 mod29 split actual: target kernel_closed

- S2122Mod29SplitActual.lean, SHA E32424CC..., 1445 lines/64106 B, EXIT=0 112.92s; olean 40,384,080 B SHA 02ABAA13...; target s2094_f_irreducible : Irreducible f; probe axioms trio; no sorryAx in file.
- Splitting hpow1/hR0..hR9/hRpow/hpow2..hpow10 top-level works. True root cause not Frobenius chain but kernel unfolding 29^10 Nat.pow (linear in exponent) causing deep recursion; literal 420707233300201 fixes. h5 ring on X^20511149 replaced by abel. Fixes: hpow2_lit/hpow5_lit/hpow10_lit via norm_num; hdvd_lit/hdiv2_lit/hdiv5_lit literal; natCard_pow2/5/10; h2_lit/h5_lit abel. Final theorem small proof term.
- Standalone replacement candidate; redefines f/s2094_f_irreducible, cannot import with S2094Mod29IrreducibleActual (same names). Original S2094 still sorry; integration/replacement needed.


## 2026-11-02 S2126 mod29 integration: S2094 target accepted, sorryAx removed

- S2126Mod29IntegrationActual.lean, SHA256 7B9F5DA7B68800C4EE86545ABC5FF06CAB785E93B65C3B0C07213341A4BD460A, 1588 lines/64664 B, EXIT=0 115.22s; olean 40,385,112 B SHA256 F1079B7A265D165C1B7AB5FAEBF8A8AB82F8AE8D66A88B21CF63EBED30EB535B at .lake/build/lib/lean/tmp/sheaf/xif/paper/; file ends with #print axioms s2094_f_irreducible, output trio; no sorry/admit/native_decide/axiom token in source.
- Content = S2122Mod29SplitActual.lean (SHA256 E32424CC...) byte-for-byte after the first line, plus a 14-line module header; no mathematical change. Definitions, certificates, hpow/hR chain, irreducible_of_degree_ten and the target type `Irreducible f` are unchanged.
- S2094Mod29IrreducibleActual.lean (SHA256 C5592A60FC702A25D43E60AD4B5CE35D519F8B3952F7482E7C3B22D21223431C, 17 lines/621 B) replaced by a thin re-export: `import tmp.sheaf.xif.paper.S2126Mod29IntegrationActual` plus module doc; old sorry theorem removed. olean 2,776 B SHA256 0FB82E4D27ED710D725F3E43CA0F2B7BC5EA506368555F0F3700226AD23C4BF5, EXIT=0.
- Acceptance probe _S2126IntegrationProbe.lean (imports S2094): EXIT=0 47.24s; `s2094_f_irreducible : Irreducible f`; `example : Irreducible f := s2094_f_irreducible`; #print axioms s2094_f_irreducible = [propext, Classical.choice, Quot.sound]; irreducible_of_degree_ten same trio; no sorryAx.
- Pre-existing _S2094AxiomProbe.lean (imports S2094) re-run unchanged: EXIT=0 47.09s; cert_P1, cert_R2, cert_lin1, cert_bez2, hfdeg, s2094_f_irreducible all trio; no sorryAx.
- Consumer compatibility: the S2094 module path still resolves; f, P1..P10, R0..R9, Rfun, cert_*, hfdeg/hfmonic, hG2/hG5, h2_lit/h5_lit, irreducible_of_degree_ten, s2094_f_irreducible remain in scope with original names/types. S2122 stays historical scratch; S2126/S2094 and S2122 still cannot be co-imported (identical root names), by design.


## 2026-11-02 S2126: D5 mod29 target sorry-free via re-export

- S2126Mod29IntegrationActual.lean full mod-29 development (S2122 content byte-identical after line 1 + 14-line header), SHA 7B9F5DA7..., 1588 lines; olean 40,385,112 B SHA F1079B7A...
- S2094Mod29IrreducibleActual.lean replaced by 17-line thin re-export import S2126, SHA C5592A60..., 621 B; olean 2776 B SHA 0FB82E4D...; old sorry source removed.
- Our probe import S2094: #check s2094_f_irreducible : Irreducible f; #print axioms = [propext, Classical.choice, Quot.sound]. No sorryAx.
- Builds: S2126 EXIT=0 115s; S2094 EXIT=0 49s; integration probe and old acceptance probe EXIT=0, all declarations trio. No math change; S2122 unchanged historical scratch.
- Caveat: declaration attribution is S2126; S2094 re-exports. If comparator requires theorem text inside S2094, can do in-place variant.

## 2026-11-02 S2125 strong-presentation coherent lift cone morphism: target not proved; exact fibre 2-cell API

- S2125PresentationCoherentActual.lean, SHA256 EDA777BA84833E920ADA466FD6B38F11D80B4C1B1B792EBA3B4C55612144B9CB, 663 lines/33528 B, EXIT=0 23.36s; olean 335,888 B SHA256 0158549A70586836AA112563CF2CB5321D1FD7E297E3E3B55F8C7B68AC15953C at .lake/build/lib/lean/tmp/sheaf/xif/paper/; 24 axiom probes all [propext, Classical.choice, Quot.sound]; no sorryAx/error; consumer _s2125consumer.lean EXIT=0.
- Proved S2125ImageCone_commutes_app: the S2107 image-cone commutes cell at (U,x) is sq.commutes at ((u.app U).obj x) for an arbitrary square (general form of S2115's iso-comma computation); S2125TwistAt <-> S2125DisplayedTwistAt <-> S2125ConcreteTwistAt; S2125LiftToXCompatible_recorded_iff.
- Exact first missing S2123PresentationLiftConeMorCoherent = S2125PresentationConcreteTwist = S2125PresentationRecordedComparison_iff = S2120StrongPresentationTwist. Explicit component form (S2125PresentationConcreteTwistAt_iff_explicit, Iff.rfl): for every strong Pg, cone s, U,x in C.source.fiber(U), g.map(alpha_x) ; c0.commutes_x = Pg.commutes_{lift x} ; (ptA;f.map)(beta_x), where alpha=liftToX, beta=liftToY, c0=S2118Conv.
- Sufficient API S2125SufficientAPI: residual existence S2125PresentationRequiredTwoCellAPI (equiv S2120PresentationLiftConeMor) + S2123PresentationLiftTwoCellFull => target. Also S2125PresentationConcreteTwist_of_firstMissing/_of_coneCategoryAPI/_of_S2118/_of_strongTwist; consumer S2125StrongPresentationTwist_for_strongTwoFullData.
- Strong-field boundary strengthened: S2125StrongFieldOfLift, S2125EssSurjOf_iff_strongFieldOfLift and S2125PresentationConeEssSurj_iff_strongFieldOfLift are definitional: the strong field's statement mentions no recorded comparison, only the lift. S2125PresentationStrongFieldAtLift_eq_refl: the actual Pg.coneEssSurj output at the recorded lift is the identity iso; _indep: it does not depend on the comparison isos fed.
- Target NOT proved; no countermodel formalized. S2115 fullness is S2076Square iso-comma; S2104 twist is the butterfly-lift fibre twist; neither is the presentation square. No fake.

## 2026-11-02 S2125 presentation concrete twist exact missing

- S2125PresentationCoherentActual.lean, SHA EDA777BA..., 663 lines/33528 B, EXIT=0; olean 335888 B SHA 0158549A...; 24 probes trio; consumer EXIT=0.
- Proved S2125ImageCone_commutes_app (general square); S2125TwistAt <-> S2125DisplayedTwistAt <-> S2125ConcreteTwistAt; S2125PresentationConcreteTwist_iff_coherent (<-> S2123PresentationLiftConeMorCoherent); _iff_strongTwist (<-> S2120StrongPresentationTwist); explicit formula g.map(alpha_x) ; c0.commutes_x = Pg.commutes_(l x) ; (ptA;f.map)(beta_x), alpha=liftToX, beta=liftToY, c0=S2118Conv, l=Pg.toWeak.isPullback.lift W c0. S2125PresentationRecordedComparison_iff; S2125PresentationRequiredTwoCellAPI <-> S2120PresentationLiftConeMor; S2125SufficientAPI / S2125PresentationConcreteTwist_of_requiredAndFull; S2125StrongFieldOfLift/EssSurjOf_iff/ PresentationConeEssSurj_iff_strongFieldOfLift definitional; S2125PresentationStrongFieldAtLift_eq_refl/_indep; consumer S2125StrongPresentationTwist_for_strongTwoFullData.
- Target not proved, no countermodel. S2115 fullness in iso-comma, S2104 fibre twist at butterfly lift, neither presentation square. Need add S2125PresentationConcreteTwist as coherence field/geometric input or residual existence + S2123PresentationLiftTwoCellFull. No fake.

## 2026-11-02 S2124 ToYEquation reduced to two leg statements; fix identified

- S2124ToYEquationActual.lean, SHA 7DA40C6C..., 373 lines, EXIT=0; olean 156824 B; axioms trio; no sorry.
- Proved rfl-unfoldings S2124LiftToYIsoX_hom/_inv, S2124LiftToYIsoY_hom/_inv into S2058AssociatorIso/WhiskerLeftIso/WhiskerRightIso (right-associated, inverse left-associated + Category.assoc); S2124PastedToXi (Coherence.S2114LowerLiftToACompat at actual datum in S2058 language); S2124PastedToY2 + _toY2 with toY1; S2124ToYEquation_of_legs: upper twoCell_ext from two leg equations -> S2121ToYEquation; S2124RebuiltWitness/S2124ToAWitness (conditional on legs, and S2118ConcreteWitnessTwist-conditional forms).
- Exact first missing: S2124XiLegStatement / S2124ToY2LegStatement (conjunction S2124Legs). Mathematically pure associativity; Lean blocker: unfolding S2107LiftToYIsoX gives S2107ExtLiftToX with type Iso(vcomp (S2107ExtLift) D.square1.toX) s.toX, while S2058WhiskerRightIso stated with D.toX1; defeq only above instances transparency, simp fails "not type-correct under instances transparency". Fix: add S2124ExtLiftToX with type-correct at instances in S2124LiftToYIsoX_hom/_inv and S2124PastedToXi; then simp only [Category.assoc] should finish. No fake.

## 2026-11-02 CORRECTION: no acceptance-target changes; scope errors owned

- User challenge accepted: the two "decisions" (IsSepClosed Omega for M3; presentation coherence field for D6) are consequences of OUR formalization scope choices, not paper requirements, and must not be framed as requests to change the user's acceptance target.
- M3: frozen RemainingTypeLevel with arbitrary [Field Omega] is our over-general formalization; S2106 proves it FALSE (K=Omega=Q, K'=Q(sqrt2) counterexample). The paper's geometric point is separably closed. We do NOT substitute [IsSepClosed Omega] for the locked target. Status of the frozen target: REFUTED. A paper-faithful separably-closed auxiliary statement, if produced, is separate and cannot count as original target completion.
- D6: adding coherence to EtaleStackBaseChangePresentation would be an extra field/assumption, i.e. changing the object; not allowed. Keep existing definitions. S2125PresentationConcreteTwist remains exact MISSING; S2124/S2125/S2127 continue proving it from existing 2-cell API. If unprovable, D6(c) stays open/missing; no field addition, no fake.
- No target/acceptance change performed. Audit corrected accordingly.

## 2026-11-02 REVIEW UNDERSTANDING SEALED

- File: coord/REVIEW-UNDERSTANDING-2026-11-02.md
- SHA256: 4ab7a96dbe2fd0b5bcba882d76d36b99bcf780467d1ca20c91ef0345121eacc9
- This note is frozen: corrections only by new append-only entries/files referencing this hash; do not rewrite the note.
- Two review reports: coord/ROADMAP-2026-11-02-REVIEW.md and .claude/worktrees/roadmap-2026-11-review-cddd5f/coord/ROADMAP-2026-11-02-REVIEW.md. No ranking between them; they have different scopes/evidence bases.
- Key corrections recorded: D6 Batch 1 not closed (S2127 conditional, S2121ComparisonTwist + hg missing); M2b(A)/(C) and M2c; H2 surjectivity missing; D5 S2057Mod29FactorizationData; D9 S1964HonestCFQuotient; S2040 Oxmu/hull/logVolume semantics; ledger truncation; S2106 REFUTED-informal; S2108TwoFullInputs vacuous.

## 2026-11-02 NEW BATCH AFTER TWO REVIEWS

- Frozen record: coord/REVIEW-UNDERSTANDING-2026-11-02.md SHA256 4ab7a96dbe2fd0b5bcba882d76d36b99bcf780467d1ca20c91ef0345121eacc9 (read-only).
- New batch assigned after review corrections:
  - kummer: H2 Surjective h2Comparison + CoboundaryLift/lim1.
  - logdescent: M2b(A) TransferBridge (not M2c).
  - qside: S2127 compile acceptance + S1850Doubled probes for S2094BigSquareEssSurj/S2121ComparisonTwist; no coherence field.
  - multiradial: S2040 O^xmu quotient-vs-roots semantic comparison.
  - primespine: D9 S1964HonestCFQuotient witness / SlicePush first missing.
  - volumedet: D5 S2057Mod29FactorizationData integration with S2126.
  - transport: ledger recovery proposal only, no overwrite.
- Rule: no target change, no extra field, no false hG, no conditional as unconditional.
