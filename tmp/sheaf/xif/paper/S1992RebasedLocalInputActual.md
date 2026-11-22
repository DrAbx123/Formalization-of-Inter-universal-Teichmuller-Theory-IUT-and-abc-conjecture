# S1992: the rebased local O^× input

Date: 2026-11-01 (Asia/Shanghai).  File:
`tmp/sheaf/xif/paper/S1992RebasedLocalInputActual.lean`.

## Verdict

**Constructed (EXIT=0, kernel-checked)**: S1978's missing rebased input is
reduced to a single explicit family datum, and S1978's missing rebased paper
q-pilot object is constructed from that datum with **all four paper-level
identifications instantiated by the actual S1895 paper propositions and proved**.
**Missing**: the family datum itself.  Its exact remaining content is identified
and the structural obstructions that any inhabitant must meet are proved; no
inhabitant is asserted.

## What S1978 left

S1978 built the actual local `O^×` carrier `(Integers (AlgebraicClosure Q_p))^×`,
its actual local Galois action, its nontrivial `O^×μ` quotient, the actual local
`O^×` F-prime-strip `localOFieldStrip` on the S1895 place type, and a reduced
paper object `localOFieldPaperO`.  It proved `no_localOFieldStrip_equiv_shear`
(no strip equivalence to the S1487 shear core), so the S1895 input cannot be
re-based by an equivalence; it recorded the input-level missing objects
`S1978RebasedPaperInput D` / `S1978RebasedPaperO D` without inhabitants.

## Constructed (checked)

1. **Theta packets are determined by `q`.**  `thetaPacket_eq_of_q_eq` and
   `hodgeTheater_eq_of_components`: a Hodge theater is determined by its
   arithmetic data, its prime-strip and its theta packet.
2. **The rebased family datum** `S1992RebasedLocalFamily D`: a
   `SourceHodgeTheaterFamily` over `PaperV = FinitePrimePlace 2 7`, an index
   equivalence with `Int × Int`, arithmetic alignment with the S1895 initial
   data, and the actual local strip at `(1,0)`.
   - `toInput` builds the rebased `OriginalInput` with the S1895 initial data;
   - `toRebasedInput` inhabits S1978's `S1978RebasedPaperInput D`;
   - `ofRebasedInput` recovers the datum from S1978's type;
   - `nonempty_iff_rebasedPaperInput`: the family datum and S1978's missing
     rebased input are the **same** missing object (mutual construction).
3. **The rebased paper q-pilot object.**  `S1992RebasedPaperObject D E` and
   `S1992RebasedPaperO D E : S1978RebasedPaperO D` for every datum `E`.  Its
   four identification slots are the actual S1895 props and all are proved:
   - `paper_strip_identification := S1895FTimesMuProp`, proved because the
     rebased `(1,0)` core *is* `localOFieldStrip` (identity full
     poly-isomorphism);
   - `paper_logKummer_identification := S1895FullLogKummerProp`, proved by the
     actual S1895 one-column correspondence of the rebased input;
   - `paper_lineBundle_identification := S1679PaperLineBundleIdentified`, the
     actual S1679 `O(-D)` carrier;
   - `paper_qPilot_log_identification := S1895ScalarProp`, proved from the
     actual S1487/S1527 evaluation `-localLogMagnitude S1487Cand` because the
     rebased input has the S1895 initial data.
   Also proved: strip anchors, the `(1,0)` label binding, and that the rebased
   strip is not the S1895 paper object's strip.
4. **Compatible local strips are forced.**  For any `S` with
   `φ : FPrimeStripEquiv localOFieldStrip S`:
   `linked_mon_equiv` (value monoid is the actual local `O^×` up to the link),
   `linked_degree_trivial` (degree trivial), and `linked_action_form` (the
   action is the transport of the actual local Galois action).
   `localOFieldUnitsDegree_apply_eq_one` proves the actual norm-log degree of
   every integral unit is `1` via `norm_unit_eq_one`.
5. **The family must really vary.**  In any family with common arithmetic data
   the prime-strip map is injective (`strip_injective_of_common_arithmetic`).
   Hence a family whose theaters all carry *exactly* `localOFieldStrip` has at
   most one index (`index_subsingleton_of_constant_local_strip`); a rebased
   family therefore contains two **distinct** compatible local strips
   (`not_constant_local`, `exists_distinct_strips`), indeed **infinitely
   many** of them (`infinite_strips`), and every member's strip is linked to
   the local strip (`other_strip_linked`).
6. **The shear family cannot be patched.**  `no_localOFieldStrip_equiv_shear_strip`
   for every lattice point, hence no `HodgeTheaterLink` joins a local-strip
   theater to a shear-strip theater
   (`no_hodgeTheaterLink_local_shear`); in particular the S1527/S1487 shear
   input's `(1,0)` theater has no link to the local strip
   (`no_link_from_local_to_shear_input`, `s1527Input_core_eq_shear`).
7. **The S1895 input is not already rebased** (`s1895Input_not_rebased`).

## The exact first missing

`S1992FirstMissing D := S1992RebasedLocalFamily D`, proved equivalent to
S1978's `S1978RebasedPaperInput D` (and to `Nonempty (S1978RebasedPaperO D)`
by `S1992FirstMissing_iff_rebasedPaperO`).

It is **not** a cosmetic restatement.  By item 5 the strip map must be injective
on `Int × Int`, so the datum must supply infinitely many pairwise **distinct**
F-prime-strips, each linked to the actual local `O^×` strip.  By item 4 every
such strip has the actual local `O^×` value monoid (up to the link) and the
trivial degree, and its action is the transport of the actual local Galois
action.  Consequently the whole remaining freedom is *per-place decoration
data*: triples of equivalences

  `(Pi_v ≃ Pi_v,  G_v ≃ G_v,  O^×_v ≃ O^×_v)`   at each `v : FinitePrimePlace 2 7`,

whose induced strip data `(proj, action)` are provably pairwise distinct.
Since the degree is provably trivial and the value monoid content is fixed, this
requires provable **non-identity automorphism data of the local absolute Galois
groups** (equivalently, of the local `O^×` carrier modulo the commutant of the
action).  No such automorphism is constructed in the tree: there is no
declaration of a `MulEquiv`/`MulAut` of `LocalAbsoluteGalois p` anywhere, and the
only `AlgEquiv` of a p-adic algebraic closure in the tree is
`AlgEquiv.refl`.  The natural S1487-style shear mechanism is unavailable
because the local projective group is the actual local absolute Galois group,
not `Multiplicative (Int × Int)`, and (item 6) the shear strips cannot be mixed
in at all.

So the first missing construction is exactly: *a nontrivial decorated family of
actual local strips* — the datum `S1992RebasedLocalFamily D` — and this file
records it as a structure with no inhabitant rather than faking it.

## What is *conditional* and what is unconditional

- Unconditional and proved: items 1, 2 (constructions), 3 (all slots, given a
  datum), 4, 5, 6, 7.
- Conditional: existence of the datum (hence of the rebased input and paper
  object).  `S1992FirstMissing_suffices` states the implication exactly.

No `sorry`, `admit`, `axiom`, `True`/`PUnit` slot, empty type, arbitrary
inhabitant or `Nonempty` gate is used.  The only occurrences of the words
"sorry"/"axiom" are in the module docstring and the `#print axioms` probe
headings.

## Evidence

- source: `tmp/sheaf/xif/paper/S1992RebasedLocalInputActual.lean`, 612 lines,
  SHA256 `DB6BC4A5203FF321312986FA72ACB30D39C83291F076A7A3AE21FD1F8E6BF214`.
- compile: `lake env lean -j1 -R D:\lean -o
  .lake/build/lib/lean/tmp/sheaf/xif/paper/S1992RebasedLocalInputActual.olean
  tmp/sheaf/xif/paper/S1992RebasedLocalInputActual.lean`, `@EXIT=0`;
  `tmp/sheaf/xif/paper/logs/S1992.compile.log` contains only the
  `#print axioms` output — no warnings, no errors, no `sorry`.
- olean: `.lake/build/lib/lean/tmp/sheaf/xif/paper/S1992RebasedLocalInputActual.olean`,
  355976 bytes, SHA256
  `871A31ED563E0BB2663A6A0FF8D15F8BD69BCC61F348D3638D7906EF70EEF4FF`.
- axioms: every probed declaration depends only on
  `[propext, Classical.choice, Quot.sound]`; no `sorryAx`.
- consumer: `tmp/sheaf/xif/paper/_S1992Consumer.lean`, EXIT=0, imports the
  olean and checks the equivalence with S1978's missing input, the paper object
  and its four identifications, the forced degree/monoid data, the
  non-constancy of the family, and the shear incompatibility.
- the concrete Gaussian field instances used in the statement layer are the
  same proved local instances as in S1895/S1527
  (`gaussianPolynomial_irreducible`); they are `local` and hence must be
  redeclared by consumers.

## Not run

Full Project build (only this file and its consumer were compiled), target
comparator, independent review.

## Scope

The carrier at a place `v` is the local model at the rational prime `v.1` (the
`Q_p`-model used by S1967/S1978), not the completion of the number field at the
place `QPlace v`.  The rebased family datum is stated for this `Q_p`-model strip.
