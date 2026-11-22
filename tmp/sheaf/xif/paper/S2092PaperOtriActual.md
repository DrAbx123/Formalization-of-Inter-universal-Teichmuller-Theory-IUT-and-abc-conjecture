# S2092: paper O^⊿ carrier and paper q_v attachment at the paper's designated K-place

Date: 2026-11-02 (Asia/Shanghai).  File:
`tmp/sheaf/xif/paper/S2092PaperOtriActual.lean` (450 lines).
Consumer probe: `tmp/sheaf/xif/paper/_S2092Consumer.lean`.

## Verdict

**EXIT=0**, kernel-checked, no `sorry`/`axiom`.  The paper's `O^⊿` carrier and the
paper `q_v` are **constructed** at the paper's designated K-place, together with
the actual `O^× → O^⊿` embedding and the `O^×μ = μ_{2l}` subgroup.  The paper's
`q_v^{1/2l} ∈ O^⊿(T_{X_v}) ≅ O^⊿_{K_v}` (IUT I, Example 3.2(iv)) is **not**
constructed: it is recorded as the exact first missing
(`paperOtriRootMissing` = S1413's `SectionTwoLRoot`), equivalent to the
carrier-level root, with its arithmetic obstruction proved
(`l ∣ eSource`, `2l ∣ ord(q_v)`).  No fake carrier, no all-units, no qVFamily.

## Paper text (source reading correction)

IUT I, §0 (Fig. I1.2): `O^⊿` is the *multiplicative monoid of nonzero integral
elements* of the local field, and the F-prime-strip at v is modelled by
`G_v ↷ O^⊿_{F̄_v}`.

IUT I, Example 3.2(iv) (corpus lines 3701–3726): `q_v ∈ O^⊿(T_{X_v}) (≅ O^⊿_{K_v})`;
`q_v` admits a `2l`-th root `q_v^{1/2l} ∈ O^⊿(T_{X_v})`, determined up to a
`μ_{2l}(T_{X_v})`-multiple; the paper derives existence from Definition 3.1(b)
("the 2·3-torsion points of E_F are rational over F", hence q_v is a square in
K_v) together with Definition 3.1(c) ("K = F(E[l])", hence q_v is an l-th power
in K_v), plus [EtTh], Proposition 1.4, (ii) for the Θ_v(-q_v) evaluation.

This means the S346/S357 reading of the missing object as a separate speculative
"orbifold structural sheaf" carrier is not the paper's object: the paper's `O^⊿`
is the concrete monoid of nonzero integral elements of K_v (the S2032/S60 shape).
The S346 spec's `qSection_toCompletion` is a bare function (vacuous to inhabit);
the faithful monoid-hom version is proved impossible below.

## Constructed (all kernel-checked)

1. `paperOtriSubmonoid K` / `paperOtri T b`: the paper's `O^⊿` carrier
   `{x | ‖x‖ ≤ 1 ∧ x ≠ 0}` with its Monoid, at `sectionKPlace T b` (S1413's
   Definition 3.1(e) section lift), same shape as S2032's
   `localOFieldIntegralSubmonoid` and S60's `oBoundaryMonoid`.
2. `paperQV T b`: the paper `q_v` = S1413's actual `sectionQ` (the completion
   image of the clause-B source q-parameter under the source section), proved a
   nonzero integral **non-unit** (`‖q_v‖ < 1`, hence `q_v ∉ O^×`); source
   attachment `paperQV = completionMap (shadowQ)` (`paperQV_eq_completionMap`);
   order law `ord(q_v) = eSource · ord(q)` and `Nat.Coprime ord(q) l`.
3. `paperOUnits = (Integers K_v)^×`, `paperOUnitsMu = rootsOfUnity (2l)`
   (not all units), `paperOUnitsToOtri : paperOUnits →* paperOtri` proved
   injective, `paperOUnitsMu_pow`.
4. `paperRootRatio_mem_mu`: the ratio of any two `2l`-th roots of `q_v` in the
   completion is an integral unit lying in `O^×μ` — the paper's `μ_{2l}`
   indeterminacy law for the (missing) root.
5. `paperClosureRoot`: a `2l`-th root of `q_v` in `AlgebraicClosure K_v` always
   exists, and any two differ by a `2l`-th root of unity.  So the missing datum
   is the K_v-rationality of the root, not abstract existence.
6. `paperOtriAttachment`: the assembled record (carrier, q_v, O^× embedding,
   O^×μ exponent law); the root is deliberately not a field of it.
7. `no_completionMonoidEval_of_Fside_qVFamily`: no monoid evaluation into the
   F-side completion units sends a q-section (with a root section) to the
   F-side `qVUnit` (S342; S2057/S681 obstruction).  Hence the paper q_v is not
   the F-side repo `qVFamily`: it is the K-side base change `sectionQ`.
   `no_Fside_completionRoot` records S342's `¬ Nonempty (TwoLthRootData T b)`.

## Exact first missing, by paper citation

`paperOtriRootMissing T b :=` S1413's `SectionTwoLRoot`: a `2l`-th root of the
paper `q_v` **inside the completion K_v**, i.e. the paper's
`q_v^{1/2l} ∈ O^⊿(T_{X_v}) ≅ O^⊿_{K_v}` of **IUT I, Example 3.2(iv)**.

Proved about it:
* `paperOtriRootMissing_iff : paperOtriRootMissing ↔ paperOtriRootInCompletion`
  (the carrier-level root);
* `paperOtriRootInCompletion_iff_paperQV` (root of the constructed `paperQV`);
* `paperOtriRoot_forces_l_dvd_ramification` and `..._twoL_dvd_order`
  (S1413: any such root forces `l ∣ eSource` and `2l ∣ ord(q_v)`), and
  `paperOtriRoot_forces_l_dvd_of_coprime` deriving `l ∣ eSource` from the
  file's own order law `ord(q_v) = eSource · ord(q)` and clause-(c) coprimality.

The paper's derivation of this root is not formalized: the tree has
`T.clauseC.torsion23_rational` and `T.clauseC.kernel_field_identification`, but
no Tate-curve parametrisation of the torsion points (so `q_v^{1/2}` from the
rational 2-torsion and `q_v^{1/l}` from `E[l] ⊂ E(K)` are not constructed), and
no K-side Tate point comparison (`S1413SectionTateUniformization` / S1515's
remaining `points` field).  These are the two honest upstream gaps; the
"which paper definition/lemma" answer is **IUT I, Example 3.2(iv)**, with
Definition 3.1(b) and (c) as its two inputs and [EtTh] Prop. 1.4(ii) for the
Θ_v(-q_v) value.

## Evidence

* prerequisite: S1413's olean was built (source unchanged):
  `lake env lean -j1 -R D:\lean -o .lake/build/lib/lean/tmp/sheaf/xif/paper/S1413SourceKPlaceQComparisonActual.olean tmp/sheaf/xif/paper/S1413SourceKPlaceQComparisonActual.lean`
  EXIT=0, log `tmp/sheaf/xif/paper/_S2092_build_S1413.log`.
* source: `tmp/sheaf/xif/paper/S2092PaperOtriActual.lean`, 450 lines,
  20890 bytes, SHA256
  `20A7371BECCAEA1B929D7EA8C2A1570F33965C6414BAD5EE0F0572FF1D00CD88`.
* compile: `lake env lean -j1 -R D:\lean -o .lake/build/lib/lean/tmp/sheaf/xif/paper/S2092PaperOtriActual.olean tmp/sheaf/xif/paper/S2092PaperOtriActual.lean`,
  **EXIT=0**, no errors, no warnings (log `_S2092_build.log`).
* olean: `.lake/build/lib/lean/tmp/sheaf/xif/paper/S2092PaperOtriActual.olean`,
  578736 bytes, SHA256
  `AB350CA9983760119933E2A9A3AFEE07C6728571EDCD9EC57209414E02C71825`.
* axioms: all 13 probed declarations depend only on
  `[propext, Classical.choice, Quot.sound]`; no `sorryAx`.
* forbidden tokens: none (occurrences of sorry/axiom are in docstrings and
  `#print axioms` only).
* consumer: `tmp/sheaf/xif/paper/_S2092Consumer.lean`, EXIT=0, imports the
  module and uses `paperQV_eq_completionMap`, `paperOtriRootMissing_iff`.
* `statement_compiles`: yes.  `proof_body_checked`: yes.  `kernel_closed`:
  yes for the constructed declarations on the S1413/S342 imported chain (not a
  full Project build).  `target_accepted`: partial — the completion-level root
  (Example 3.2(iv)) is the missing object, by design.

## Not run

Full Project build, target comparator, independent review.