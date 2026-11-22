import LeanFormal.IUT.IUTIII.Corollary312.StepXI.SourceSharedBoundary
import LeanFormal.IUT.IUTIII.Theorem311.SourceProcessionBoundary
import LeanFormal.IUT.IUTII.Kummer.TimesMuIsm
import LeanFormal.IUT.Audit.Status

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

/-!
# Source-level Kummer and evaluation arrows (reduced interface)

This module freezes the reduced source-level interface of the first vertical
(Kummer) arrow and of the evaluation arrows of the commutative diagram of
IUT III, Remark 3.10.2, so that the IPL decomposition of IUT III,
Remark 3.11.1, (iii), and the SHE two-path statement can both be posed on it.

## Original (paper) route

* IUT II, Definition 4.9, (i): a `x`-mu-Kummer structure on a Frobenioid is an
  `Ism`-orbit of isomorphisms `O^xmu(G') ~ O^xmu(A)` of ind-topological
  modules; it determines, and is completely determined by, the invariant
  submodules `I_kappa_H(A) = Im(O^x(G')^H)`, `H` open in the Galois group.
* IUT II, Corollary 4.10, (ii): the evaluation isomorphisms of Corollary 4.6,
  (iv), (v), determine an evaluation isomorphism `F_env ~ F_gau` of
  F-prime-strips; (iii) composes with it to build the Theta-x-mu-links.
* IUT III, Remark 3.10.2: the four-corner commutative diagram of
  `F^boxplus-triangleright-x-mu`-prime-strips; the first vertical arrow is
  the induced version of the Kummer isomorphism of Proposition 2.1, (ii);
  the lower horizontals are the evaluation isomorphism of IUT II,
  Corollary 4.10, (ii), and the tautological isomorphisms of Proposition
  3.7, (iii), (iv); the upper horizontals are the etale-like evaluation
  isomorphism and the natural isomorphisms of Proposition 3.10, (i). Each
  lower horizontal is the conjugate of the corresponding upper horizontal by
  the vertical Kummer isomorphisms.
* IUT III, Remark 3.11.1, (iii): the IPL linking isomorphisms are obtained by
  composing the inverses of the first two lower horizontals, then the first
  vertical arrow (Kummer theory portion of Theorem 3.11, (iii), (c), (d)),
  then the three upper horizontals (evaluation map portion). SHE states that
  the construction and its output are simultaneously well-defined relative to
  the arithmetic holomorphic structures in the domain and codomain of the
  Theta-link.
* IUT III, Theorem 3.11, (ii): the log-Kummer correspondence; (iii), (a)-(d):
  compatibility of the Kummer isomorphisms and evaluation maps with the
  horizontal arrows (Theta-x-mu-LGP-link compatibility).

## Reduced route (deviations)

R1. Objects. The paper works with `F^boxplus-triangleright-x-mu`-prime-strips
    and full poly-isomorphism sets. This module has only `FPrimeStrip V` and
    single `FPrimeStripEquiv` representatives; there is no `x`-mu strip type
    in the repository (DSH-F API-1 gap). Every arrow below is such a single
    representative, and the `x`-mu layer is carried separately.
R2. Kummer layer. The `x`-mu-Kummer structure of Definition 4.9, (i), is
    realized per place by `TimesMuKummer.Isomorphism` between torsion
    quotients of the units of `Mon v`; the ind-topology, mono-theta
    environments, and the Frobenioid evaluations are not constructed, and a
    single group `G` acts at every place (the family of local absolute Galois
    groups is not constructed).
R3. Vertices. The `env`/`gau`/`LGP`/`lgp` strips of the paper are not
    constructed in the repository; the records below are therefore
    parameterized by their strip vertices. No theorem identifies any of these
    vertices with the supplied Hodge-theater-family links `fLinkAt`/`dLinkAt`;
    the coricity identification remains a source obligation.
R4. Horizontals. The evaluation arrow collects the paper's three upper
    horizontals (resp. the lower evaluation isomorphism) into one record; the
    intermediate coric vertices are not split off. The second and third
    columns of Remark 3.10.2 (tautological and natural isomorphisms of
    Propositions 3.7 and 3.10) are out of scope of this module.
R5. No coherence is asserted between the strip-level representative and the
    carried unit layer of an arrow (the paper derives both from one arrow of
    prime-strips; freezing a coherence law would be a new, unproved
    identification).
R6. The identification of the reduced q-pilot anchor with the paper's q-pilot
    `F^boxplus-triangleright-x-mu`-prime-strip is NOT made (DSH-F trap T5).

## Named source cards (not constructed here)

* Card LK: `SourceTimesMuKummerLayer` (the `x`-mu layer, Definition 4.9, (i)).
* Card VK: `SourceVerticalKummerCard` (the vertical Kummer arrows of the
  log-Kummer correspondence along one source column, Theorem 3.11, (ii)).
* Card EV: `SourceEvaluationUnitPortion` (the `(-)^triangleright-x-mu` unit
  portion of the evaluation isomorphism, Corollary 4.10, (ii)).
* Card SQ: `SourceKummerEvaluationSquare.commutes` (the conjugation of
  Remark 3.10.2; Theta-x-mu-LGP compatibility, Theorem 3.11, (iii), (a), (b)).
* Card IPL: `SourceLinkFactorization.factorization` (the frozen IPL formula of
  Remark 3.11.1, (iii)).

## Proved here

Layer injectivity/surjectivity and the invariant-image law; uniqueness of the
`Ism`-orbit of any `x`-mu-Kummer isomorphism over the same actions; existence
of gate-only witnesses (`sourceKummerArrow_self`, `sourceEvaluationArrow_self`)
recording satisfiability of the frozen records; inhabitability
characterizations; the two-path equality of the square; accessors.

## Not claimed here

The actual Kummer isomorphisms of Theorem 3.11, (ii), the evaluation
isomorphism of Corollary 4.10, (ii), the (Ind1)-(Ind3) indeterminacies, any
IPL/SHE/APT conclusion, any Theta-x-mu-link, and any Theorem 3.11 output.
-/

namespace LeanFormal.IUT

universe uG uv ua upi umon ui u w

namespace Theorem311Source

variable {V : Type uv}

/-! ## 1. The reduced x-mu-Kummer layer (IUT II, Definition 4.9, (i)) -/

/-- Card LK: the reduced `x`-mu-Kummer layer of a source-level vertical Kummer
arrow at one pair of strips (upper, lower).

Original: IUT II, Definition 4.9, (i).  A `x`-mu-Kummer structure on a
Frobenioid is an `Ism`-orbit of isomorphisms `O^xmu(G') ~ O^xmu(A)` of
ind-topological modules; it determines, and is completely determined by, the
submodules `I_kappa_H(A) = Im(O^x(G')^H)` inside `O^xmu(A)`, for `H` running
over the open subgroups.  The layer therefore records *which units* (the
`O^x`/`O^xmu` layer) the isomorphism acts on.

Reduced form: `sourceAction` and `targetAction` are the supplied actions on
the unit groups of the `v`-components, and `kummer` is a Kummer-compatible
isomorphism of the torsion quotients per place, carrying equivariance and the
invariant-image law as fields of `TimesMuKummer.Isomorphism`.  No field is a
`Prop` slot closable by `True`; every field is data on the concrete carriers
`TimesMuQuotient (Mon v)^x`. -/
structure SourceTimesMuKummerLayer (G : Type uG) [Group G] [TopologicalSpace G]
    (upper lower : FPrimeStrip V) where
  /-- the action of `G` on the units of the upper strip, placed at `v` -/
  sourceAction : ∀ v : V, G →* MulAut ((upper.Mon v)ˣ)
  /-- the action of `G` on the units of the lower strip, placed at `v` -/
  targetAction : ∀ v : V, G →* MulAut ((lower.Mon v)ˣ)
  /-- the `x`-mu-Kummer isomorphism at each place, equivariant with the
  actions and mapping the invariant submodules onto the invariant submodules
  (the `I_kappa_H(A)` law of Definition 4.9, (i)) -/
  kummer : ∀ v : V, TimesMuKummer.Isomorphism (sourceAction v) (targetAction v)

namespace SourceTimesMuKummerLayer

variable {G : Type uG} [Group G] [TopologicalSpace G]
variable {upper lower : FPrimeStrip V}
variable (L : SourceTimesMuKummerLayer G upper lower)

/-- The layer isomorphism is injective at every place (*injectivity* reading of
the Definition 4.9(i) isomorphism condition). -/
theorem kummer_equiv_injective (v : V) :
    Function.Injective (L.kummer v).equiv :=
  (L.kummer v).equiv.injective

/-- The layer isomorphism is surjective at every place. -/
theorem kummer_equiv_surjective (v : V) :
    Function.Surjective (L.kummer v).equiv :=
  (L.kummer v).equiv.surjective

/-- The invariant-image law: the image of every invariant submodule of the
source layer is exactly the invariant submodule of the target layer
(the `I_kappa_H(A)` determination of Definition 4.9, (i)). -/
theorem invariantImage_law (v : V) (H : OpenSubgroup G) :
    (L.kummer v).equiv ''
        (TimesMuKummer.invariantImage (L.sourceAction v) H :
          Set (TimesMuQuotient ((upper.Mon v)ˣ))) =
      (TimesMuKummer.invariantImage (L.targetAction v) H :
        Set (TimesMuQuotient ((lower.Mon v)ˣ))) :=
  (L.kummer v).invariantImage H

/-- Uniqueness of the `x`-mu-Kummer orbit: any `x`-mu-Kummer isomorphism over
the same actions as the frozen layer lies in the same `Ism`-orbit as the
frozen one.  This is the reduced form of the paper's "the `x`-mu-Kummer
structure is completely determined by the collection of invariant submodules,
as the unique `Ism`-orbit" (IUT II, Definition 4.9, (i)). -/
theorem kummer_orbit_unique (v : V)
    (k : TimesMuKummer.Isomorphism (L.sourceAction v) (L.targetAction v)) :
    k.orbitOf = (L.kummer v).orbitOf :=
  TimesMuKummer.Isomorphism.orbitOf_eq k (L.kummer v)

end SourceTimesMuKummerLayer

/-! ## 2. The source-level vertical Kummer arrow (Remark 3.10.2, first
vertical arrow) -/

/-- The source-level vertical Kummer arrow, between two source strips.

Original: the "first vertical arrow" of the commutative diagram of IUT III,
Remark 3.10.2 — the induced `F^boxplus-triangleright-x-mu`-prime-strip
version of the Kummer isomorphism of the final display of Proposition 2.1,
(ii) (whose codomain is the vertically coric D-Theta-Hodge theater), and the
Kummer theory portion of Theorem 3.11, (iii), (c), (d).  As part of the
log-Kummer correspondence (Theorem 3.11, (ii)) it is accompanied by the
(Ind3) upper-semi inclusions/surjections; those are not part of this reduced
record (they live in the separate vertical log-Kummer contract).

Reduced form: `stripIso` is one `FPrimeStripEquiv` representative of the full
poly-isomorphism, and `layer` is the Definition 4.9(i) `x`-mu content
(Card LK).  Constructing an inhabitant is the source obligation of the
log-Kummer correspondence; the reduced record deliberately does not identify
`stripIso` with the supplied Hodge-theater-family links. -/
structure SourceKummerArrow (G : Type uG) [Group G] [TopologicalSpace G]
    (upper lower : FPrimeStrip V) where
  /-- single `F`-level representative of the full poly-isomorphism -/
  stripIso : FPrimeStripEquiv upper lower
  /-- the `x`-mu-Kummer layer (Card LK) -/
  layer : SourceTimesMuKummerLayer G upper lower

/-- Assembly of a Kummer arrow from its two cards. -/
def sourceKummerArrowOfLayer {G : Type uG} [Group G] [TopologicalSpace G]
    {upper lower : FPrimeStrip V} (stripIso : FPrimeStripEquiv upper lower)
    (layer : SourceTimesMuKummerLayer G upper lower) :
    SourceKummerArrow G upper lower :=
  { stripIso := stripIso, layer := layer }

/-- Inhabitability characterization (gate): a Kummer arrow exists exactly when
a strip-level representative and the Definition 4.9(i) `x`-mu layer exist. -/
theorem sourceKummerArrow_nonempty_iff {G : Type uG} [Group G]
    [TopologicalSpace G] (upper lower : FPrimeStrip V) :
    Nonempty (SourceKummerArrow G upper lower) ↔
      ∃ iso : FPrimeStripEquiv upper lower,
        Nonempty (SourceTimesMuKummerLayer G upper lower) :=
  ⟨fun ⟨K⟩ => ⟨K.stripIso, ⟨K.layer⟩⟩,
    fun ⟨iso, ⟨layer⟩⟩ => ⟨sourceKummerArrowOfLayer iso layer⟩⟩

/-- Gate-only witness: the frozen record is satisfiable (identity strip
isomorphism, trivial actions, `Isomorphism.refl`).  Contains no arithmetic
content and is not a construction of the paper's Kummer isomorphism. -/
theorem sourceKummerArrow_self {G : Type uG} [Group G] [TopologicalSpace G]
    (S : FPrimeStrip V) : Nonempty (SourceKummerArrow G S S) :=
  ⟨sourceKummerArrowOfLayer (FPrimeStripEquiv.refl S)
    { sourceAction := fun _ => 1
      targetAction := fun _ => 1
      kummer := fun v =>
        TimesMuKummer.Isomorphism.refl (1 : G →* MulAut ((S.Mon v)ˣ)) }⟩

/-! ## 3. The source-level evaluation arrow (IUT II, Corollary 4.10, (ii)) -/

/-- Card EV: the `(-)^triangleright-x-mu` unit-group portion of the evaluation
isomorphism at one pair of strips.

Original: IUT III, Theorem 3.11, (iii), (c), and section 1, (iii): the tensor
packets of log-shells are compatible, relative to the Kummer isomorphisms, with
the unit group portion `(-)^triangleright-x-mu` of the Theta-x-mu-LGP-link; the
constructions, the related Kummer isomorphisms, and the evaluation maps are
equivariant under automorphisms of the domain and codomain.

Reduced form: per place, a `G`-equivariant isomorphism of the `x`-mu layers.
The invariant-submodule law of Card LK is deliberately not carried here: the
paper attaches it to Kummer structures, not to the evaluation isomorphism. -/
structure SourceEvaluationUnitPortion (G : Type uG) [Group G] [TopologicalSpace G]
    (upper lower : FPrimeStrip V) where
  /-- the action of `G` on the units of the upper strip, placed at `v` -/
  sourceAction : ∀ v : V, G →* MulAut ((upper.Mon v)ˣ)
  /-- the action of `G` on the units of the lower strip, placed at `v` -/
  targetAction : ∀ v : V, G →* MulAut ((lower.Mon v)ˣ)
  /-- the `x`-mu-layer isomorphism induced by the evaluation isomorphism -/
  unitLayer : ∀ v : V,
    TimesMuQuotient ((upper.Mon v)ˣ) ≃* TimesMuQuotient ((lower.Mon v)ˣ)
  /-- equivariance in the sense of Theorem 3.11, (iii), (c) -/
  unitLayer_equivariant : ∀ (v : V) (g : G) (x : TimesMuQuotient ((upper.Mon v)ˣ)),
    unitLayer v (TimesMuQuotient.action (sourceAction v) g x) =
      TimesMuQuotient.action (targetAction v) g (unitLayer v x)

namespace SourceEvaluationUnitPortion

variable {G : Type uG} [Group G] [TopologicalSpace G]
variable {upper lower : FPrimeStrip V}
variable (P : SourceEvaluationUnitPortion G upper lower)

/-- The unit portion is injective at every place. -/
theorem unitLayer_injective (v : V) :
    Function.Injective (P.unitLayer v) :=
  (P.unitLayer v).injective

end SourceEvaluationUnitPortion

/-- The source-level evaluation arrow, between two source strips.

Original: IUT II, Corollary 4.10, (ii): "the evaluation isomorphisms of
Corollary 4.6, (iv), (v), determine an evaluation isomorphism
`F_env ~ F_gau` of `F`-prime-strips"; in IUT III, Remark 3.10.2, this is the
first lower horizontal arrow, and the "three upper horizontal arrows" are the
etale-like evaluation isomorphism together with the natural isomorphisms of
Proposition 3.10, (i), second display.  These are the evaluation map portion of
Theorem 3.11, (iii), (c), (d).

Reduced form: one `FPrimeStripEquiv` representative of the evaluation
isomorphism, plus the Card EV unit portion.  In `SourceLinkFactorization` and
`SourceKummerEvaluationSquare` below, `evaluation` is the collapsed composite
of the three upper horizontals. -/
structure SourceEvaluationArrow (G : Type uG) [Group G] [TopologicalSpace G]
    (upper lower : FPrimeStrip V) where
  /-- single `F`-level representative of the evaluation isomorphism -/
  stripIso : FPrimeStripEquiv upper lower
  /-- the `(-)^triangleright-x-mu` unit portion (Card EV) -/
  unitPortion : SourceEvaluationUnitPortion G upper lower

/-- Assembly of an evaluation arrow from its two cards. -/
def sourceEvaluationArrowOfUnitPortion {G : Type uG} [Group G]
    [TopologicalSpace G] {upper lower : FPrimeStrip V}
    (stripIso : FPrimeStripEquiv upper lower)
    (unitPortion : SourceEvaluationUnitPortion G upper lower) :
    SourceEvaluationArrow G upper lower :=
  { stripIso := stripIso, unitPortion := unitPortion }

/-- Inhabitability characterization (gate): an evaluation arrow exists exactly
when a strip-level representative and the Card EV unit portion exist. -/
theorem sourceEvaluationArrow_nonempty_iff {G : Type uG} [Group G]
    [TopologicalSpace G] (upper lower : FPrimeStrip V) :
    Nonempty (SourceEvaluationArrow G upper lower) ↔
      ∃ iso : FPrimeStripEquiv upper lower,
        Nonempty (SourceEvaluationUnitPortion G upper lower) :=
  ⟨fun ⟨E⟩ => ⟨E.stripIso, ⟨E.unitPortion⟩⟩,
    fun ⟨iso, ⟨portion⟩⟩ => ⟨sourceEvaluationArrowOfUnitPortion iso portion⟩⟩

/-- Gate-only witness: the frozen record is satisfiable (identity strip
isomorphism, trivial actions, identity unit layer).  Contains no arithmetic
content and is not a construction of the paper's evaluation isomorphism. -/
theorem sourceEvaluationArrow_self {G : Type uG} [Group G] [TopologicalSpace G]
    (S : FPrimeStrip V) : Nonempty (SourceEvaluationArrow G S S) :=
  ⟨sourceEvaluationArrowOfUnitPortion (FPrimeStripEquiv.refl S)
    { sourceAction := fun _ => 1
      targetAction := fun _ => 1
      unitLayer := fun v => MulEquiv.refl (TimesMuQuotient ((S.Mon v)ˣ))
      unitLayer_equivariant := fun _ _ _ => rfl }⟩

/-! ## 4. The reduced four-corner square (Remark 3.10.2; Theta-x-mu-LGP
compatibility, Theorem 3.11, (iii), (a), (b)) -/

/-- The reduced four-corner square of IUT III, Remark 3.10.2 (first two
columns).  `upperLeft`/`upperRight` are the vertically coric `(n,o)`-level
`env`- and `gau`-strips; `lowerLeft`/`lowerRight` the `n,m`-level ones.
`leftKummer` is the first vertical arrow (Card LK content) and `rightKummer`
the induced Kummer isomorphism on the right.

Original: "each of these lower horizontal arrows may be constructed by
conjugating the corresponding upper horizontal arrow by the relevant Kummer
isomorphisms, i.e., by the vertical arrows in the diagram"; and, relative to
the Kummer isomorphism, the full poly-isomorphism of the Theta-x-mu-LGP-link
is compatible with the horizontal arrows (Theorem 3.11, (iii), (a), (b)).

Reduced form: `commutes` freezes the conjugation as the commutativity of the
square, `(inv kappa_1) >> lower = upper >> (inv kappa_2)`, which is equivalent
to `lower = (inv kappa_2) >> upper >> kappa_1` on the level of the
groupoid laws.  The square does NOT identify the two arithmetic holomorphic
structures: it compares composites of isomorphisms, not structures (cf. the
SHE trap of the DSH-F report). -/
structure SourceKummerEvaluationSquare (G : Type uG) [Group G] [TopologicalSpace G]
    (upperLeft upperRight lowerLeft lowerRight : FPrimeStrip V) where
  /-- the upper (vertically coric) horizontal evaluation arrow -/
  upperHorizontal : SourceEvaluationArrow G upperLeft upperRight
  /-- the lower horizontal evaluation arrow (Corollary 4.10, (ii)) -/
  lowerHorizontal : SourceEvaluationArrow G lowerLeft lowerRight
  /-- the first vertical Kummer arrow, on the left -/
  leftKummer : SourceKummerArrow G lowerLeft upperLeft
  /-- the induced Kummer isomorphism, on the right -/
  rightKummer : SourceKummerArrow G lowerRight upperRight
  /-- the conjugation law / commutativity of the square -/
  commutes :
    (leftKummer.stripIso.symm).trans lowerHorizontal.stripIso =
      upperHorizontal.stripIso.trans (rightKummer.stripIso.symm)

namespace SourceKummerEvaluationSquare

variable {G : Type uG} [Group G] [TopologicalSpace G]
variable {upperLeft upperRight lowerLeft lowerRight : FPrimeStrip V}
variable (S : SourceKummerEvaluationSquare G upperLeft upperRight lowerLeft
  lowerRight)

/-- The SHE domain-side expression: descend by the inverse of the left Kummer
isomorphism into the `n,m`-level (Theta-link domain) row, then walk the lower
horizontal evaluation arrow. -/
def domainExpression : FPrimeStripEquiv upperLeft lowerRight :=
  (S.leftKummer.stripIso.symm).trans S.lowerHorizontal.stripIso

/-- The SHE codomain-side expression: walk the upper (vertically coric,
codomain-side) row first, then descend by the inverse of the right Kummer
isomorphism. -/
def codomainExpression : FPrimeStripEquiv upperLeft lowerRight :=
  (S.upperHorizontal.stripIso).trans (S.rightKummer.stripIso.symm)

/-- The two-path equality: on this interface the domain and codomain
expressions agree.  This is the reduced form on which the SHE two-path
statement of Remark 3.11.1, (iii) — and its "closed loop" reading via
Remark 3.9.5, (viii), (ix) — can be posed.  It is not a proof of SHE. -/
theorem domainExpression_eq_codomainExpression :
    S.domainExpression = S.codomainExpression :=
  S.commutes

end SourceKummerEvaluationSquare

/-! ## 5. The frozen IPL factorization (Remark 3.11.1, (iii)) -/

/-- The frozen source form of the IPL composite of IUT III, Remark 3.11.1,
(iii):

`inputLink = (inv lowerHorizontal_1) >> (inv lowerHorizontal_2) >> kummer >> evaluation`.

Original: "At a more explicit level, the linking isomorphisms of 'intermediate'
F^boxplus-triangleright-x-mu-prime-strips are given by composing the inverses
of the first two lower horizontal arrows of the commutative diagram of
Remark 3.10.2, followed by the first vertical arrow of this diagram —
corresponding to the Kummer theory portion of Theorem 3.11, (iii), (c), (d) —
followed by the three upper horizontal arrows of the diagram — corresponding
to the evaluation map portion of Theorem 3.11, (iii), (c), (d)."

Reduced form and the reading of the fields: the composite is traversed from
the intermediate `n,m`-level LGP vertex, so the fields are named in traversal
order, matching the displayed formula.  `lowerHorizontal_1` is the lower
horizontal whose inverse is traversed first (the tautological isomorphism of
Proposition 3.7, (iii), between the `gau` vertex and the `LGP` vertex);
`lowerHorizontal_2` is the evaluation isomorphism of IUT II, Corollary 4.10,
(ii), on the bottom row (`env -> gau`; its inverse walks `gau -> env`).
The paper's own numbering calls the evaluation isomorphism the "first" lower
horizontal; this record keeps the frozen formula's order.  `kummer` is the
first vertical arrow (`env` column) and `evaluation` the collapsed composite
of the three upper horizontals (coric row).  The third lower horizontal
(`LGP -> lgp`) is not part of this composite. -/
structure SourceLinkFactorization (G : Type uG) [Group G] [TopologicalSpace G]
    (intermediateStrip gauStrip envStrip coricEnvStrip qPilotStrip : FPrimeStrip V) where
  /-- the lower horizontal whose inverse is traversed first (traversal order;
  paper: the tautological isomorphism of Proposition 3.7, (iii)) -/
  lowerHorizontal₁ : FPrimeStripEquiv gauStrip intermediateStrip
  /-- the lower horizontal whose inverse is traversed second (traversal order;
  paper: the evaluation isomorphism of IUT II, Corollary 4.10, (ii)) -/
  lowerHorizontal₂ : FPrimeStripEquiv envStrip gauStrip
  /-- the first vertical arrow -/
  kummer : SourceKummerArrow G envStrip coricEnvStrip
  /-- the collapsed composite of the three upper horizontals -/
  evaluation : SourceEvaluationArrow G coricEnvStrip qPilotStrip
  /-- the linking isomorphism of the intermediate strip -/
  inputLink : FPrimeStripEquiv intermediateStrip qPilotStrip
  /-- the frozen IPL formula -/
  factorization :
    inputLink =
      (lowerHorizontal₁.symm).trans
        ((lowerHorizontal₂.symm).trans
          (kummer.stripIso.trans evaluation.stripIso))

namespace SourceLinkFactorization

variable {G : Type uG} [Group G] [TopologicalSpace G]
variable {intermediateStrip gauStrip envStrip coricEnvStrip qPilotStrip :
  FPrimeStrip V}

/-- The composite on the right-hand side of the frozen IPL formula. -/
def composite (F : SourceLinkFactorization G intermediateStrip gauStrip envStrip
    coricEnvStrip qPilotStrip) :
    FPrimeStripEquiv intermediateStrip qPilotStrip :=
  (F.lowerHorizontal₁.symm).trans
    ((F.lowerHorizontal₂.symm).trans
      (F.kummer.stripIso.trans F.evaluation.stripIso))

/-- The frozen factorization, restated with the named composite. -/
theorem inputLink_eq_composite (F : SourceLinkFactorization G intermediateStrip
    gauStrip envStrip coricEnvStrip qPilotStrip) :
    F.inputLink = F.composite :=
  F.factorization

end SourceLinkFactorization

/-! ## 6. Source anchors -/

section SourceAnchors

variable {l : PrimeGeFive} {Label : Type u} {Choice : Type w} [AddGroup Label]

/-- Card VK: the vertical Kummer arrows of the log-Kummer correspondence
(IUT III, Theorem 3.11, (ii)) along one source column `n` of a source input.

Each arrow goes from the `m`-member `fPrimeStripAt n m` to the `(n,0)`-core.
Constructing these arrows is the source obligation; note that no field
identifies them with the supplied family links of the Hodge-theater family
(the vertical coricity identification of Theorem 1.5, (i), is a separate
source theorem, not assumed here).  The `(Ind3)` upper-semi content of
Theorem 3.11, (ii), is not part of this reduced card. -/
structure SourceVerticalKummerCard (G : Type uG) [Group G] [TopologicalSpace G]
    (I : OriginalInput.{ua, uv, upi, umon, ui} l V) (n : Int) where
  /-- the `m`-th vertical Kummer arrow of the column -/
  kummer : ∀ m : Int, SourceKummerArrow G (I.fPrimeStripAt n m) (I.fPrimeStripAt n 0)

/-- The reduced reference for the "coric"/"fixed" q-pilot strip of the source
input: the prime strip of the input Hodge theater (the `F`-layer only).

NOT asserted: that this strip "is" the paper's q-pilot
`F^boxplus-triangleright-x-mu`-prime-strip (DSH-F trap T5), and not the
`x`-mu-layer or the identification with the `(1,0)`-level q-pilot object.
This anchor exists so that the `qPilotStrip` vertex of
`SourceLinkFactorization` can be instantiated by the actual source input. -/
def sourceQPilotStrip
    (input : SourceProcessionBoundary.Input (l := l) (V := V) (Label := Label)
      (Choice := Choice)) :
    FPrimeStrip V :=
  input.theater.primeStrip

end SourceAnchors

end Theorem311Source

namespace Audit

def sourceKummerEvaluationArrows : Obligation :=
  { id := "IUT-III.source-kummer-evaluation-arrows"
    source :=
      "IUT II, Definition 4.9, (i); Corollary 4.10, (ii); IUT III, " ++
        "Remark 3.10.2; Remark 3.11.1, (iii), (iv); Theorem 3.11, (ii), " ++
        "(iii), (a)--(d); Corollary 3.12, proof, Step (xi-b)"
    status := VerificationStatus.interface
    note :=
      "Reduced source interface for the first vertical (Kummer) arrow and " ++
        "the evaluation arrows of Remark 3.10.2: frozen records " ++
        "SourceKummerArrow (x-mu layer as TimesMuKummer.Isomorphism, one " ++
        "F-prime-strip representative), SourceEvaluationArrow (Corollary " ++
        "4.10, (ii), unit portion with equivariance), SourceLinkFactorization " ++
        "(the frozen IPL formula of Remark 3.11.1, (iii)), and " ++
        "SourceKummerEvaluationSquare (Remark 3.10.2 conjugation / " ++
        "Theta-x-mu-LGP compatibility). Proved: layer injectivity/" ++
        "surjectivity, the invariant-image law, Ism-orbit uniqueness, " ++
        "gate-only satisfiability witnesses, inhabitability " ++
        "characterizations, and the two-path equality. NOT constructed: the " ++
        "actual Kummer isomorphisms of Theorem 3.11, (ii), the evaluation " ++
        "isomorphism of Corollary 4.10, (ii), the (Ind1)-(Ind3) " ++
        "indeterminacies, and any identification with the supplied " ++
        "Hodge-theater-family links; no IPL/SHE/APT conclusion is asserted."
    dependsOn :=
      [ "IUT-II.vertical-log-kummer",
        "IUT-II.vertical-log-kummer-correspondence",
        "IUT-III.K1.vertical-log-kummer-boundary",
        "IUT-III.K2.frobenioid-mod-realification-boundary" ] }

end Audit

end LeanFormal.IUT
