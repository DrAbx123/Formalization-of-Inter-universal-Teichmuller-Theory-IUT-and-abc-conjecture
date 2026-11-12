# S1887: the actual D9 cusp origin from the boundary residual, and the exact first missing

Status: **proof file compiled** (EXIT=0, no error, no warning, no `sorryAx`,
axioms trio only).  The D9 cusp `(Prop, proof)` pair and the origin map are
constructed from **exactly one** geometric datum (a boundary cusp of the K-core
orbicurve); the exact first missing type is named and proved equivalent to the
S1881 missing statement.  The unconditional D9 cusp pair is **not** closed: no
boundary cusp is constructed anywhere in the tree.

Consumer: S1881 D9 cusp pair / `S1881D9CuspMissing` / `S1881D9Supply` /
`S1881S1732SourceData` / S1732 Definition 3.1 assembly.  The package removes the
"boundary residual" half of the S1881 missing statement and leaves one exposed
geometric object with its exact field decomposition.

## Deliverable

| item | value |
|---|---|
| file | tmp/sheaf/xif/paper/S1887D9CuspActual.lean |
| lines | 624 |
| source bytes | 26061 |
| source SHA256 | A16BE338E7D23CCAD3258BDD7128D202B9314490F815BB6CCA1EB0925030E449 |
| compile | `lake env lean -j1 -o .lake/build/lib/lean/tmp/sheaf/xif/paper/S1887D9CuspActual.olean tmp/sheaf/xif/paper/S1887D9CuspActual.lean` |
| EXIT | 0 (no error, no warning) |
| olean | .lake/build/lib/lean/tmp/sheaf/xif/paper/S1887D9CuspActual.olean (414752 bytes, 2026-11-01T12:35:30) |
| olean SHA256 | 9E9E68D2484D6C773D04D11D3E2D105F6B7AD38BC7956C5656C0FC821082BEA5 |
| import probe | tmp/sheaf/xif/paper/_S1887ImportProbe.lean, EXIT=0, 49 declarations `#check`ed |
| probe SHA256 | 39D41E0C28D7F087A90FEDC8B7302880DB1F753752A05CB4E9ED92C5718F3DA7 |
| axioms | propext, Classical.choice, Quot.sound only (45 `#print axioms` checks, all public declarations) |
| sorry/admit/axiom in code | none (grep; the words appear only in the doc comment) |

## 1. Target locked

S1881's exact missing statement over a D9 orbicurve slot `S` is

    S1881D9CuspMissing l S  =  exists Q : TorsionRankOneQuotientData ..., Nonempty (S1881CuspBoundaryResidual l (X := S.cK) Q)

with

    S1881CuspBoundaryResidual ... Q   =  { originMap : {q // q != 0} -> OrbicurveBoundaryCusp X,
                                            cusp      : OrbicurveBoundaryCusp X,
                                            originMap distinguished = cusp }

and `S1881ActualRankOneQuotient l hI` / `S1881ActualRankOneQuotient_distinguished_nonzero`
already actual.  The theorem `S1881CuspOrigin_of_actualResidual` consumes a
residual; S1887 builds one from actual data and identifies the real remainder.

## 2. What is new and proved

1. **The residual is exactly a boundary cusp** (`S1887CuspBoundaryResidual_nonempty_iff`):

       Nonempty (S1881CuspBoundaryResidual l (X := X) Q)  <->  Nonempty (Iut.OrbicurveBoundaryCusp X)

   over any fixed rank-one quotient `Q`.  Forward: the `cusp` field.  Backward:
   the constant origin map at the given cusp (`S1887ResidualOfCusp`).  The frozen
   contract imposes no condition on the origin map except the distinguished-class
   equation (`S1887Residual_originMap_distinguished`), so the origin-map half of
   the D9 cusp datum carries **no content beyond the cusp**.  The paper's origin
   map (bad-place local generator ±1) is not encoded by this contract; it is the
   parked card `IUT-I.definition-3.1-D9-cusp-local-generator`.

2. **The actual origin** (`S1887ActualOrigin`): for every `hI` and every actual
   boundary cusp `c : Iut.OrbicurveBoundaryCusp X`,

       S1887ActualOrigin l hI c : TorsionQuotientBoundaryOrigin l (S1732A l) X

   with `rank_one_quotient = S1881ActualRankOneQuotient l hI` (definitional,
   `S1887ActualOrigin_rank_one_quotient`), `cusp = c`, constant origin map, and the
   distinguished-class equation by `rfl`.  Its three frozen compatibilities are
   proved, not assumed (`S1887ActualOrigin_spec`: origin equation, generator
   `quotientEquiv distinguished = 1`, distinguished class nonzero).  So the actual
   residual of the actual quotient exists as soon as a cusp does
   (`S1887D9CuspFirstMissing_residual`), which instantiates the hypothesis of
   `S1881CuspOrigin_of_actualResidual`.

3. **The whole D9 cusp origin slot is one cusp** (`S1887CuspOrigin_nonempty_iff_cusp`):

       Nonempty (TorsionQuotientBoundaryOrigin l (S1732A l) X)  <->  Nonempty (Iut.OrbicurveBoundaryCusp X)

   given `hI` (needed only for the backward direction).  No quotient, origin map
   or equation is left to be supplied.

4. **The D9 cusp pair** (`S1887D9CuspPairOfCusp`): from a boundary cusp `c` of
   `S.cK`, the pair `S1731D9CuspPair l` with

       prop  = ArithmeticCuspOriginCompatibility (S1887ActualOrigin l hI c)
       proof = arithmeticCuspOriginCompatibility_of_supply _

   (`S1887D9CuspPairOfCusp_prop`, `..._prop_spec`).  Through S1881's assembly this
   gives `S1887D9MissingOfCusp` (`S1731D9Missing`), `S1887D9Supply`
   (`D9CompatibilitySupply`) and `S1887S1732SourceData` (`SourceDefinition31Data`),
   with the cusp slot definitionally `ArithmeticCuspOriginCompatibility` and the
   orbicurve slot definitionally `S1881D9OrbicurveMissing`.

5. **Exactness of the reduction** (`S1887D9CuspMissing_iff_cusp`):

       S1881D9CuspMissing l S  <->  Nonempty (Iut.OrbicurveBoundaryCusp S.cK).

   Equivalently `S1887D9CuspFirstMissing_iff` for the named first-missing type.

6. **Non-substitution guard.**  `S1887D9CuspSlot_cK_ne_actualOrbicurve`:
   `S.cK != S1726Orbicurve` (signatures `(1,l-tors)^±` versus once-punctured
   `(1,1)`), and `S1887D9CuspSlot_cF_ne_actualOrbicurve` for `C_F`.  A boundary cusp
   of the actual S1726 orbicurve is therefore not the D9 cusp of `C_K`; it is not
   substituted.

7. **Field decomposition of the missing datum**
   (`S1887BoundaryCuspEquivPrefixData`):

       Iut.OrbicurveBoundaryCusp X  ~=  Sigma P : S1887BoundaryCuspPrefix X, S1887BoundaryCuspPointData P

   with `S1887BoundaryCuspPrefix` = (compactification stack, open map, representable
   open immersion) and `S1887BoundaryCuspPointData` = (residue scheme, point of the
   compactification fiber, boundary separation).  The first field is the
   compactification stack (`S1887BoundaryCuspPrefixOfCusp_compactification`), the
   first hard field the representable open immersion
   (`..._openImmersion`, `S1887D9CuspFirstMissing_prefix_openImmersion`).

## 3. The exact first missing statement

    S1887D9CuspFirstMissing l S  :=  Iut.OrbicurveBoundaryCusp S.cK          (Type 1)

    Nonempty (S1887D9CuspFirstMissing l S)  <->  S1881D9CuspMissing l S.

In words: **one boundary cusp of the K-core orbicurve `C_K = S.cK`**, i.e. a
compactification stack of `C_K` with a representable open immersion and a boundary
point outside the open orbicurve.  Its first missing field is the compactification
stack; its first hard field is `Iut.EtaleStackOpenImmersion`
(= `EtaleStackRepresentableMorphismProperty` with the open-immersion property),
which requires for every scheme-valued point a full 2-pullback presentation.

Why it is not obtained here:

* A repository-wide search finds `Iut.OrbicurveBoundaryCusp` only as the structure
  (`Iut/Foundations/Orbicurve.lean:576`) and as fields of source records
  (`SourceSignQuotientData.epsilon`, `SourceClauseF.boundary_origin.cusp`,
  `OrbicurveCuspidalDecompositionData.cusp`, ...).  Every existing declaration with
  that return type is a projection of a supplied field (`nativeEpsilonGeometric`,
  `cusp_of_clauseF`, `searchCusp`, ...).  No construction exists.
* No inhabitant of `EtaleStackRepresentableMorphismProperty` (hence none of
  `EtaleStackOpenImmersion` or `EtaleStackFiniteEtaleMorphism`) occurs in the tree
  except as a hypothesis; the representable open-immersion / 2-pullback line is
  S1743/S1756/S1784/S1804/S1831, still partially missing (`S1804` builds the
  iso-comma model and the identity-point pullback only).
* The D9 `C_K` itself is missing (S1881: `S1881D9OrbicurveMissing`), so even the
  ambient orbicurve of the cusp is not available; the cusp datum is downstream of
  the D9 orbicurve slot.

## 4. Honest boundary (not claimed)

* The unconditional D9 cusp pair is **not** filled: `S1887D9CuspPairOfCusp` and
  `S1887S1732SourceData` take the boundary cusp as an argument.  No cusp, no
  compactification stack and no open immersion is manufactured.
* The frozen D9 cusp content is `ArithmeticCuspOriginCompatibility` only.  The
  full Definition 3.1(f) clause `SourceClauseF` additionally requires the
  Clause (c) torsion-basis identity (`quotient_basis_eq_k_torsion_basis` against
  `D.k_torsion_basis`), the identification `boundary_cusp_eq_epsilon` with the
  supplied geometric `epsilon`, and the cuspidal decomposition
  `Iut.OrbicurveCuspidalDecompositionData E.c_groups.groups` (itself a cusp plus a
  closed decomposition subgroup with surjective restriction).  None of these is
  touched here.
* The paper's local generator origin map (IUT I, Definition 3.1(f) second half) is
  not encoded by the frozen structure; it remains
  `IUT-I.definition-3.1-D9-cusp-local-generator`.
* No `True`, `PUnit`, arbitrary proposition/group, `sorry`, `admit`, or new axiom.

## 5. One executable next step

Construct `Iut.EtaleStackOpenImmersion` for the representable stack morphism of the
actual affine model into its compactification: for each scheme-valued point build
`EtaleStackBaseChangePresentation` with apex the scheme fiber product, reusing the
iso-comma model of `S1804IsoCommaPullbackActual` for the `TwoPullbackWitness`.  This
is the first hard field of the first missing datum; it does not by itself produce
`C_K`, which remains the D9 orbicurve slot.
