# IUT xi-f Current Path Notes

Date: 2026-10-29.  Goal: active.  No paper-level completion claim.

## 1. Paper facts verified from IUT III corpus

Corollary 3.12 proof, Fig. 3.4, corpus lines 10310-10315:

  mu_{2l} acts on { q^(j^2) }_{j=1,...,l*} -> {1}.

Therefore:
- Theta values are q^(j^2), not q^(j^2/(2l)).
- 2l occurs only as the mu_{2l} roots-of-unity indeterminacy, not as an
  exponent denominator / root of q.
- Theta labels are nonzero j = 1,...,l*.  Zero label is the q-pilot
  identification (corpus lines 10347-10350), not a Theta possible image.
- Corollary 3.12 uses the procession-normalized mono-analytic log-volume
  averaged over j in F_l^x (corpus lines 10330-10331).

## 2. Constants decisions

- qVFamily T b is the actual clause-B local q_v (FinitePlaceQCandidate,
  valuation < 1).  Existing actual qVFam packet uses q_v^(j^2) directly.
- Correct Theta: q_v^(j^2), nonzero labels.
- Wrong path: taking a 2l-th root of q_v and using q_v^(j^2/(2l)).
  Files affected: PaperC3ThetaRootActual, PaperThetaRootObstructionActual,
  PaperKummerNumberFieldModelActual, PaperKummerLocalTensorActual.
  They may be re-used only as mu_{2l} root-of-unity indeterminacy structures,
  not as paper Theta values.
- Do not include zero label in paperPossibleThetaImageSet: it forces 1 in the
  image and (with lambda-O candidates) collapses the hull to O, giving hull
  log 0.  This is a semantic artifact.

## 3. Source model reconstruction (user-authorized B)

Completion-valued model:
- CompletionValueCarrier place = (CommonPrimeCompletion place)^x.
- valueToCompletion = Units.coeHom (actual coercion).
- completionValueDegree = Multiplicative.ofAdd (Real.log ||u||).

Nondegenerate tensor geometry:
- tensorIndex = V, tensorPlaceIndex = Unit,
- tensorPlaces v () = G.place v, tensorTuple () = ().
- per-b bad place product carrier: (b) -> qVFamTensorBlock T b.

These are actual constructions, but still model changes: no theorem identifies
the completion-unit value carrier with the frozen abstract FPrimeStrip.Mon v.

## 4. Actual green files (local EXIT=0, queued)

PaperSourceGeometryActual
PaperSourceGeometryQActual
PaperSourceGeometryKummerActual
PaperC3TensorGeometryActual
PaperCompletionTensorActual
PaperC3TensorBlockActual
PaperC3SourceDataActual
PaperC3ThetaUnitSourceActual
PaperC3ThetaRootActual (but wrong 2l-root interpretation; see above)
PaperThetaRootObstructionActual (same caveat)
PaperKummerLocalTensorActual (same caveat)
PaperBadPlaceProductCarrierActual
PaperBadPlaceTensorGeometryActual (product carrier + product hull/mu_log)
S22DependentProductActual (product Haar/mu_log)
S21DegreeNormAlignmentActual
S21bCompletionThetaNormBridgeActual
S21cActualQUnitBridgeActual
S21dSourceTheaterCorrectionActual
S12CompletionGeometryBridgeActual
PaperMuLogUnitRegionActual
PaperLambdaOHullActual
PaperLambdaOHullHaarActual
PaperLambdaOHullWitnessActual
PaperLambdaOHullReverseReductionActual
PaperLambdaOHullEqualityActual (= O, but used zero label; not paper)
PaperSixTorsionCarrierActual
NativeSourceTorsionGapsActualConstruction
NativeSourceAssemblyActualFields (partial)
NativeSourceAssemblyExactSequenceActual (except splitting)
NativeSourceAssemblyD7CuspActual (cuspCount actual; d7/cuspHyp missing)
PaperPlaceFamilyInjectivityActual (conditional)

## 5. Open gaps / simplifications (high severity first)

S1  value carrier replaced by completion units; not proved equal to source Mon.
S2  completionValueDegree vs source degree normalization unproved.
S3  PaperC3TensorGeometry is standalone, not SourcePilotRegionData.
S4  tensor shape V x Unit may not be paper C3 tensor shape.
S5  completion default norm vs tensor spectral norm not identified.
S6  q/theta/Kummer/Ind/ThetaLink still not fully connected.
S7  split / CanonicalTateSplitReduction unproved.
S8  old concrete C3 q=1/5 path is degenerate; do not use.
S9  some Haar/unit-region normalization remained raw vs normalized.
S10 label-sum / sourceSetVolume truncation / enclosure rejected.
S11 fixed: qUnit no longer Classical.choice in new geometry; old files may still contain choice.
S12 two new source models need bridge; S12CompletionGeometryBridge is partial.
S13 fixed: dependent-p product carrier instead of one varying-p tensor block.
S14 sourceTheater thetaPacket vs qVFamily packet mismatch; S21d correction factor
    constructed, field/place comparison still missing.
S15 fixed locally: lambda-O hull instead of closure; but zero-label artifact gives O.
S16 fixed: source theta UnitFamily from qUnit/thetaPacket, but qVFamily direct branch.
S17 conditional place injectivity; actual injection not proved.
S18 wrong 2l-root branch; paper uses q^(j^2) and mu_{2l} indeterminacy.
S19 root obstruction is about 2l root; not a paper theta object.
S20 Ind1/Ind3/Kummer actions to Block still missing; Ind2 union done.
S21 degree factor and norm bridge partial; correction factor constructed.
S22 product Haar/mu_log actual; product hull/global comparison in progress.
S23 fixed: six-torsion carrier rootsOfUnity 6 + zeta^k label.
S24 zero label in image; must exclude; hull=O is artifact.
S25 2l root error; see paper facts.
S26 sourceTheater theta packet different q; use sourceThetaPacketFromQ/qVFamily.
S27 degree/weight constants not identified with paper.
S28 raw Haar vs normalized mu_log must not be mixed.

## 6. Correct next construction order

1. Nonzero label theta image: theta_j = q_v^(j^2), j != 0.
2. mu_{2l} indeterminacy action as multiplication by roots of unity,
   not a root of q.
3. Actual lambda-O hull of the nonzero image; do not include 1 from zero label.
4. Actual candidate equality / Haar / normalized log for that hull.
5. Ind1/Ind3/Kummer possible-image actions on the same Block.
6. Global product over bad places and weighted normalized comparison.
7. Only then compare qPilotSigned with thetaHullSigned.

## 7. Build/audit status

- Key new files: local lean EXIT=0, oleans exist, queued.
- Full watchdog queue is not green (legacy failures remain).
- No sorry/axiom/True/PUnit in the new actual files.
- The goal is active; no paper-level completion.

## 8. Update: nonzero labels still integral

After excluding the zero label, `paperNonzeroThetaImageSet` uses j=1,...,l* and
values q_v^(j^2) (no 2l root).  Since q_v is a contraction, every such value has
norm <= 1, so the nonzero image is still contained in O.  Hence lambda = 1
remains a lambda-O candidate.  Excluding zero does **not** by itself rule out
the O candidate; it only removes the proof that every candidate must contain O.

The next candidate to test is lambda = tensor of q_v, because
q_v^(j^2) / q_v = q_v^(j^2-1) is in O for j >= 1, so lambda*O contains the whole
nonzero image.  The hull is the intersection over all candidates, so it can be
smaller than O; compute the q_v candidate and the reverse inclusion.

## 9. CORRECTION: the 2l root IS needed for paper Theta values

Previous note (section 8 / S25) said the 2l root was wrong.  That was based on
the Fig. 3.4 line alone.  Checking IUT I/II definitions resolves the notation:

IUT I, lines 3701-3716:
  q_v := the q-parameter of the elliptic curve E_v over K_v;
  q_v admits a 2l-th root;
  the underlined q_v (OCR often loses the underline) is DEFINED as
      q_v := q_v^(1/2l) in O^triangleright(T_{X_v}).

IUT II, lines 95-105:
  q_v denotes the q-parameter;
  let the underlined q_v be a 2l-th root of q_v;
  then the theta values are (underlined q_v)^(j^2).

Fig. 3.4: q^(j^2) is in the underlined/root normalization, with the separate
mu_{2l} indeterminacy.

Therefore for the actual `qVFamily T b` (which is the clause-B q-parameter,
not a root):

  theta_j = qVFamily.q ^ (j^2 / (2l)) = (2l-th root of qVFamily.q)^(j^2).

The root branch (`PaperC3ThetaRootActual`, `PaperThetaRootObstructionActual`,
`PaperKummerLocalTensorActual`) is the correct paper Theta branch, not a wrong
branch.  The no-root branch (`paperThetaValue = qUnit^(j^2)`) is the one that
must not be used as paper theta when qUnit is the q-parameter.

The zero label issue is separate: Cor. 3.12 averages over j in F_l^x
(corpus lines 10330-10331), so zero label is not part of the procession average;
Fig. I.1 of IUT II lists j=0,...,l*, but the Cor. 3.12 average excludes 0.

## 10. Page-level verification (rendered PDFs)

Rendered pages are in `D:\lean\tmp\paper_pages`.

- IUT I, printed p.71 (PDF page 71), I_pdfpage71.png:
  (iv) q_v := q-parameter of E_v; q_v admits a 2l-th root; the underlined q_v
  is DEFINED as q_v^(1/2l). Confirms q_v vs q̲_v.
- IUT II, printed p.2 (PDF page 2), II_pdfpage2.png:
  q_v denotes the q-parameter; let q̲_v be a 2l-th root of q_v; the theta
  values are q̲_v^(j^2), j=0,...,l* (Fig. I.1). Confirms the root is in theta.
- IUT III, printed p.173 (PDF page 173), III_pdfpage173.png:
  Fig. 3.4 has mu_{2l} acting on {q̲^(j^2)}_{j=1,...,l*}.
  Cor. 3.12 averages over j in F_l^x (zero label not in the average).

Conclusion: root normalization is correct for paper theta; Fig. 3.4 is in
root (underlined q) normalization; zero label is excluded from the Cor. 3.12
average.

## 11. Notation key (underlines matter)

Rendered pages show two different q symbols:

- q_v with ONE underline under q (and one under v): the q-parameter.
  IUT I p.71: "Write q_v for the q-parameter"; IUT II p.2: "q_v denotes the
  q-parameter".
- q_v with TWO underlines under q (and one under v): the 2l-th root of the
  q-parameter.  IUT II p.2: "Let q_v [double-underlined q] be a 2l-th root of
  q_v"; IUT I p.71: the double-underlined q is defined as q_v^{1/2l}.

The theta values are powers of the DOUBLE-UNDERLINED q:
  theta_j = (double-underlined q_v)^(j^2).
Fig. 3.4 in IUT III p.173 uses the double-underlined q.  OCR loses these
underlines, which caused the earlier q_v / q-root confusion.

So in Lean notation we should distinguish:
  qVFamily T b : q-parameter (single underline q)
  paper root theta : (2l-th root of qVFamily)^(j^2) (double underline q).

## 12. Machine-checked underline extraction

Script: PyMuPDF `get_text("rawdict")` character bboxes plus horizontal line
segments from `get_drawings()`; for each q/v character count horizontal lines
directly beneath it.  Output: `D:\lean\tmp\paper_pages\annotated.txt`.

Notation markers used in that file:
  q[1u] = q with ONE underline
  q[2u] = q with TWO underlines
  v[1u] = v with one underline

Verified lines:

IUT I p.71:
  `(iv) Write q[1u]v[1u] for the q[0u]-parameter ...`
  `q[1u]v[1u] admits a 2l-th root ...`
  `q[2u] / v[1u] = q[1u]^{1/2l} / v[1u]` (the defined root).
  `image of q[2u] v[1u] determines ...` (root is the divisor object).

IUT II p.2:
  `q[1u]v[1u] denotes the q[0u]-parameter ...`
  `Let q[2u] v[1u] be a 2l-th root of q[1u]v[1u].`
  theta image: `q[2u]^{j2} / v[1u]`.

IUT III p.173, Fig. 3.4:
  `q[2u]^{j2}` (theta values use the double-underlined q).

Conclusion: single-underlined q_v is the q-parameter; double-underlined q_v
is the 2l-th root; paper theta values are powers of the double-underlined q.
v carries one underline in both symbols, so the disambiguator is the number of
underlines under q (one vs two), not the v underline.

## 13. Lean semantic symbol types

New file `PaperSymbolTypesActual.lean` (EXIT=0) separates:

  PaperQParameter : single-underlined q_v unit
  PaperQRoot      : double-underlined q_v, carries base q-parameter
                    and pow_twoL : rootUnit^(2l)=unitToAlgClosed base.unit
  PaperThetaLabel : {j : SignedLabel // 0 < j.1}, injective labels j=1,...,l*

The theta label map is proven injective; qParameter and qRoot are not
definitionally equal and no silent coercion exists.  Old qUnit identifiers are
being migrated to this naming.
