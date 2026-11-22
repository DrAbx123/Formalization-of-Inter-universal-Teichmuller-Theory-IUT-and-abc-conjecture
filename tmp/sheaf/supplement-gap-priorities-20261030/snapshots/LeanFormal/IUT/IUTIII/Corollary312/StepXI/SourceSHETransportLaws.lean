import LeanFormal.IUT.IUTI.HodgeTheater.PrimeStripCore
import LeanFormal.IUT.IUTII.Frobenioid.PrimeStripsConstruction
import LeanFormal.IUT.IUTIII.Corollary312.StepXI.Contract
import LeanFormal.IUT.Audit.Status
import Mathlib.Tactic

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

/-!
# Card-SHE conditional assembly upgrade: the simultaneity square and its transport laws

This module solidifies the Card-SHE conditional assembly path at the same
depth as the sibling Card-IPL module `Theorem311/SourcePolyIsoTransportLaws.lean`
(SHA256 `E064E76534E9542A6F66D0E077D01B0C7ADCB3F2ECFBDA8D1726FC9035EAEE53`).
The Card-SHE card is `IUT-III.SHE` (`Corollary312/Obligations.lean:12-17`,
pending: "Prove expressibility in the fixed one-column structure."); its
definition site is IUT III, Remark 3.11.1, (iii) (SHE) (pagewise plain text
9890--9907, PDF p. 161), and its use site is Corollary 3.12, proof, Step
(xi-b) (focused extract lines 1007--1044) with the summary at (xi-c)
(1045--1066).  What is frozen here:

1. the named supply structure `SourceSimultaneousHolomorphicExpression` --
   the simultaneity object requested by the DSH-F report section 2.2, gap S1,
   and fixed syntactically in the section 3.3 draft: four F-prime-strip legs,
   two composite expressions (domain-first and codomain-first), and the
   commuting equation between them.  The two arithmetic holomorphic
   structures are NOT identified; only the two constructed expressions are
   required to agree;
2. transport-version statements: the link-conjugation engine
   `FPrimeStripLink.conjugate` with its defining laws, transport of the whole
   square along quadruples of `FPrimeStripEquiv`s, and the fiber-level
   components of the simultaneity equation;
3. the (xi-b) consumer wiring `sheStatement` / `sheSlot_evidence` for the
   `StepXIContract.she` slot (Contract.lean:32--43; `she` at :38,
   `she_evidence` at :41) and the `StepXIInput.she` / `she_evidence` shape
   (ParametricStepXI.lean:36/:39).

## Original (paper) route

* IUT III, Remark 3.11.1, (iii) (SHE) (pagewise plain text 9890--9907, PDF
  p. 161): the construction of the output data, as well as the output data
  itself, is expressed in terms that are simultaneously valid/executable/
  well-defined relative to both the arithmetic holomorphic structure that
  gives rise to the Theta-pilot object in the domain of the Theta-link and
  the arithmetic holomorphic structure that gives rise to the input data
  prime-strip in the codomain of the Theta-link.
* IUT III, Corollary 3.12, proof, Step (xi-b) (focused extract 1007--1044;
  the property list at 1032--1034): the properties consumed are (IPL),
  (SHE), (APT); the qualitative abstract output is linked [cf. (IPL)] and
  expressed simultaneously in the domain and codomain structures [cf. (SHE)].
* IUT III, Corollary 3.12, proof, Step (xi-c) (1045--1066): the output is
  constructible "relative to the arithmetic holomorphic structure in the
  1-column"; in the holomorphic hull the expression is in terms of
  localizations of arithmetic vector bundles over the 1,circ local rings.

## Reduced route (deviations)

R1. The four legs and both expressions are F-prime-strip fiber links
    (`FPrimeStripLink`), NOT the paper`s full poly-isomorphisms of
    F-times-mu-prime-strips: the times-mu layer is not modeled (the G1 gap of
    the Card-IPL verdict; the reduced legs here play the same role the
    `FPrimeStrip` level plays there).
R2. The two expressions are data fields: the internal operations of the
    construction algorithm are not modeled.  The constructor
    `ofCommutingLegs` records the case where the expressions are the two
    composites of the four legs and those composites commute.
R3. The Kummer legs are opaque links: no weight, local-unit, or evaluation
    record is attached (DSH-F gap S2).
R4. No binding of the square to the label 1,circ or to a source column is
    constructed (DSH-F gap S3); the holomorphic-hull expression (gap S4) is
    out of scope.
R5. The finite model `FiniteSHESquare` (`ConcreteFiniteRouteColumns.lean`) is
    NOT used: its vertical arrow is an involution of a finite column index,
    a different object type; treating it as SHE would change the proposition
    (DSH-F gap S5).

The two negative results of the Card-IPL G1 verdict (probe SHA256
`D660C2B40E5332E62769CC93C6F5E4721A3B7240A960ADCBA40B6069BF4B02AD`,
report section 15.3: the shell does not determine the times-mu carrier, and
does not determine the poly-isomorphism layer) are relied on as recorded
history and are NOT re-proved here.

## Open obligations (explicit fields; no free construction)

* Every field of `SourceSimultaneousHolomorphicExpression` is a discharge
  obligation of the eventual source instantiation: no source instance is
  constructed or asserted.
* Discharging the Kummer legs as actual source Kummer arrows with their
  weight/local-unit records, the binding to the 1,circ column, the hull
  expression, and the times-mu/full-poly-isomorphism upgrade of the legs are
  the open source-facing work (gaps S2, S3, S4, G1).
* The semantic landing predicate `SourceLocalizationExpressible`
  (`Theorem311/SourceArithmeticHolomorphicLanding.lean`, audit card
  `IUT-III.source-SHE-landing-evidence`, pending) is a separate reduced
  reading of the same (SHE) slot; this module neither restates it nor
  consumes it, and no cross-wiring lemma from this square to that predicate
  is provided (left to the named pending card).

## Proved here

The conjugation engine (`FPrimeStripLink.conjugate` with the pointwise
unpacking laws and composition compatibility `conjugate_trans_mapPi_apply` /
`conjugate_trans_mapG_apply` / `conjugate_trans_mapMon_apply`); the square
object with `ofCommutingLegs`, `swap` and the transport map `transport`;
the fiber-level components of the simultaneity equation
(`simultaneous_index`, and the cast form `simultaneous_mapPi_apply` /
`simultaneous_mapG_apply` / `simultaneous_mapMon_apply`); and the consumer
wiring `sheStatement` / `sheSlot_evidence`.

## Non-claims

No construction of the paper`s arithmetic holomorphic structures, Kummer
arrows, bundles, or hull; no assertion that any source data realizes the
square; no IPL/SHE/APT conclusion; no slot closed by `True`.  This module
does not restate or reprove the Card-IPL exchange laws
(`SourcePolyIsoTransportLaws.lean`) nor any APT-surface statement: it is the
SHE-only piece of the north-wall three-card boundary.
-/

namespace LeanFormal.IUT

universe uv upi umon

/-! ## 1. The link-conjugation engine -/

namespace FPrimeStripLink

variable {V : Type uv}
variable {A B A' B' : FPrimeStrip.{umon, uv, upi} V}

/-- Transport a fiber link along strip equivalences on both sides: read the
source strip through `sigma` and the target strip through `tau`.  The
conjugated link keeps the index map and transports the three fiber
homomorphisms. -/
def conjugate (L : FPrimeStripLink A B)
    (sigma : FPrimeStripEquiv A A') (tau : FPrimeStripEquiv B B') :
    FPrimeStripLink A' B' where
  index := L.index
  mapPi := fun v =>
    (tau.isoPi (L.index v)).toMonoidHom.comp
      ((L.mapPi v).comp (sigma.isoPi v).symm.toMonoidHom)
  mapG := fun v =>
    (tau.isoG (L.index v)).toMonoidHom.comp
      ((L.mapG v).comp (sigma.isoG v).symm.toMonoidHom)
  mapMon := fun v =>
    (tau.isoMon (L.index v)).toMonoidHom.comp
      ((L.mapMon v).comp (sigma.isoMon v).symm.toMonoidHom)
  compatProj := fun v => by
    ext x
    simp only [MonoidHom.comp_apply]
    have hL := DFunLike.congr_fun (L.compatProj v) ((sigma.isoPi v).symm x)
    simp only [MonoidHom.comp_apply] at hL
    have hsigma : A.proj v ((sigma.isoPi v).symm x) =
        (sigma.isoG v).symm (A'.proj v x) := by
      have h := sigma.compatProj_apply v ((sigma.isoPi v).symm x)
      simp only [MulEquiv.apply_symm_apply] at h
      rw [h, MulEquiv.symm_apply_apply]
    change B'.proj (L.index v)
        (tau.isoPi (L.index v) (L.mapPi v ((sigma.isoPi v).symm x))) =
      tau.isoG (L.index v) (L.mapG v ((sigma.isoG v).symm (A'.proj v x)))
    rw [tau.compatProj_apply (L.index v) (L.mapPi v ((sigma.isoPi v).symm x)),
      hL, hsigma]
  compatAction := fun v g x => by
    have hsigma : (sigma.isoMon v).symm (A'.action v g x) =
        A.action v ((sigma.isoPi v).symm g) ((sigma.isoMon v).symm x) := by
      have h := sigma.compatAction v ((sigma.isoPi v).symm g) ((sigma.isoMon v).symm x)
      simp only [MulEquiv.apply_symm_apply] at h
      rw [← h]
      simp only [MulEquiv.symm_apply_apply]
    change tau.isoMon (L.index v)
        (L.mapMon v ((sigma.isoMon v).symm (A'.action v g x))) =
      B'.action (L.index v)
        (tau.isoPi (L.index v) (L.mapPi v ((sigma.isoPi v).symm g)))
        (tau.isoMon (L.index v) (L.mapMon v ((sigma.isoMon v).symm x)))
    rw [hsigma,
      L.compatAction v ((sigma.isoPi v).symm g) ((sigma.isoMon v).symm x),
      tau.compatAction]
  compatDegree := fun v x => by
    change B'.degree (L.index v)
        (tau.isoMon (L.index v) (L.mapMon v ((sigma.isoMon v).symm x))) =
      A'.degree v x
    rw [tau.compatDegree]
    rw [L.compatDegree v ((sigma.isoMon v).symm x)]
    rw [← sigma.compatDegree v ((sigma.isoMon v).symm x), MulEquiv.apply_symm_apply]

@[simp] theorem conjugate_index (L : FPrimeStripLink A B)
    (sigma : FPrimeStripEquiv A A') (tau : FPrimeStripEquiv B B') :
    (L.conjugate sigma tau).index = L.index := rfl

@[simp] theorem conjugate_mapPi_apply (L : FPrimeStripLink A B)
    (sigma : FPrimeStripEquiv A A') (tau : FPrimeStripEquiv B B')
    (v : V) (x : A'.toDPrimeStrip.Pi v) :
    (L.conjugate sigma tau).mapPi v x =
      tau.isoPi (L.index v) (L.mapPi v ((sigma.isoPi v).symm x)) := rfl

@[simp] theorem conjugate_mapG_apply (L : FPrimeStripLink A B)
    (sigma : FPrimeStripEquiv A A') (tau : FPrimeStripEquiv B B')
    (v : V) (x : A'.G v) :
    (L.conjugate sigma tau).mapG v x =
      tau.isoG (L.index v) (L.mapG v ((sigma.isoG v).symm x)) := rfl

@[simp] theorem conjugate_mapMon_apply (L : FPrimeStripLink A B)
    (sigma : FPrimeStripEquiv A A') (tau : FPrimeStripEquiv B B')
    (v : V) (x : A'.Mon v) :
    (L.conjugate sigma tau).mapMon v x =
      tau.isoMon (L.index v) (L.mapMon v ((sigma.isoMon v).symm x)) := rfl

/-- Conjugation is compatible with composition of links, in pointwise form
for the three fiber homomorphisms: the conjugate of a composite link is
pointwise the composite of the conjugates.  (Stated pointwise; consumers use
the fiber values, and no equality of link structures is needed.) -/
theorem conjugate_trans_mapPi_apply {C : FPrimeStrip.{umon, uv, upi} V}
    {C' : FPrimeStrip.{umon, uv, upi} V}
    (L1 : FPrimeStripLink A B) (L2 : FPrimeStripLink B C)
    (sigma : FPrimeStripEquiv A A') (sigma' : FPrimeStripEquiv B B')
    (tau : FPrimeStripEquiv C C') (v : V) (x : A'.toDPrimeStrip.Pi v) :
    ((L1.trans L2).conjugate sigma tau).mapPi v x =
      ((L1.conjugate sigma sigma').trans (L2.conjugate sigma' tau)).mapPi v x := by
  change tau.isoPi (L2.index (L1.index v))
      (L2.mapPi (L1.index v) (L1.mapPi v ((sigma.isoPi v).symm x))) =
    tau.isoPi (L2.index (L1.index v))
      (L2.mapPi (L1.index v)
        ((sigma'.isoPi (L1.index v)).symm
          (sigma'.isoPi (L1.index v) (L1.mapPi v ((sigma.isoPi v).symm x)))))
  rw [MulEquiv.symm_apply_apply]

theorem conjugate_trans_mapG_apply {C : FPrimeStrip.{umon, uv, upi} V}
    {C' : FPrimeStrip.{umon, uv, upi} V}
    (L1 : FPrimeStripLink A B) (L2 : FPrimeStripLink B C)
    (sigma : FPrimeStripEquiv A A') (sigma' : FPrimeStripEquiv B B')
    (tau : FPrimeStripEquiv C C') (v : V) (x : A'.G v) :
    ((L1.trans L2).conjugate sigma tau).mapG v x =
      ((L1.conjugate sigma sigma').trans (L2.conjugate sigma' tau)).mapG v x := by
  change tau.isoG (L2.index (L1.index v))
      (L2.mapG (L1.index v) (L1.mapG v ((sigma.isoG v).symm x))) =
    tau.isoG (L2.index (L1.index v))
      (L2.mapG (L1.index v)
        ((sigma'.isoG (L1.index v)).symm
          (sigma'.isoG (L1.index v) (L1.mapG v ((sigma.isoG v).symm x)))))
  rw [MulEquiv.symm_apply_apply]

theorem conjugate_trans_mapMon_apply {C : FPrimeStrip.{umon, uv, upi} V}
    {C' : FPrimeStrip.{umon, uv, upi} V}
    (L1 : FPrimeStripLink A B) (L2 : FPrimeStripLink B C)
    (sigma : FPrimeStripEquiv A A') (sigma' : FPrimeStripEquiv B B')
    (tau : FPrimeStripEquiv C C') (v : V) (x : A'.Mon v) :
    ((L1.trans L2).conjugate sigma tau).mapMon v x =
      ((L1.conjugate sigma sigma').trans (L2.conjugate sigma' tau)).mapMon v x := by
  change tau.isoMon (L2.index (L1.index v))
      (L2.mapMon (L1.index v) (L1.mapMon v ((sigma.isoMon v).symm x))) =
    tau.isoMon (L2.index (L1.index v))
      (L2.mapMon (L1.index v)
        ((sigma'.isoMon (L1.index v)).symm
          (sigma'.isoMon (L1.index v) (L1.mapMon v ((sigma.isoMon v).symm x)))))
  rw [MulEquiv.symm_apply_apply]

end FPrimeStripLink

/-! ## 2. The Card-SHE simultaneity square -/

variable {V : Type uv}

/-- Card-SHE simultaneity square: the named supply structure of the Card-SHE
conditional assembly path.  The upper (domain) and lower (codomain) rows are
two adjacent Theta-Hodge theaters` strips and their vertically coric
counterparts; the two composite expressions (domain-first: upper horizontal
then the right Kummer arrow; codomain-first: the left Kummer arrow then lower
horizontal) are required to agree as links from the upper-left to the
lower-right strip.  The two arithmetic holomorphic structures are NOT
identified: only the two constructed expressions commute.  Every field is an
explicit discharge obligation; no source instance is constructed or asserted
(reductions R1--R4 of the module docstring). -/
structure SourceSimultaneousHolomorphicExpression
    (upperLeft upperRight lowerLeft lowerRight : FPrimeStrip.{umon, uv, upi} V)
    (upperHorizontal : FPrimeStripLink upperLeft upperRight)
    (lowerHorizontal : FPrimeStripLink lowerLeft lowerRight)
    (leftKummer : FPrimeStripLink upperLeft lowerLeft)
    (rightKummer : FPrimeStripLink upperRight lowerRight) where
  /-- the domain-first composite expression (upper horizontal, then the right
  Kummer arrow) -/
  domainExpression : FPrimeStripLink upperLeft lowerRight
  /-- the codomain-first composite expression (left Kummer arrow, then lower
  horizontal) -/
  codomainExpression : FPrimeStripLink upperLeft lowerRight
  /-- simultaneity: the two expressions agree -/
  simultaneous : domainExpression = codomainExpression

namespace SourceSimultaneousHolomorphicExpression

variable {A B C D : FPrimeStrip.{umon, uv, upi} V}
variable {uH : FPrimeStripLink A B} {lH : FPrimeStripLink C D}
variable {lK : FPrimeStripLink A C} {rK : FPrimeStripLink B D}

/-- Constructor from an explicit commuting four-leg square: when the two
composite paths formed from the four legs agree, the square is realized with
those composites as its expressions. -/
def ofCommutingLegs (h : uH.trans rK = lK.trans lH) :
    SourceSimultaneousHolomorphicExpression A B C D uH lH lK rK where
  domainExpression := uH.trans rK
  codomainExpression := lK.trans lH
  simultaneous := h

@[simp] theorem ofCommutingLegs_domainExpression (h : uH.trans rK = lK.trans lH) :
    (ofCommutingLegs h).domainExpression = uH.trans rK := rfl

@[simp] theorem ofCommutingLegs_codomainExpression (h : uH.trans rK = lK.trans lH) :
    (ofCommutingLegs h).codomainExpression = lK.trans lH := rfl

/-- Orientation swap: interchanging the two expressions preserves the square
(the simultaneity statement is symmetric). -/
def swap (E : SourceSimultaneousHolomorphicExpression A B C D uH lH lK rK) :
    SourceSimultaneousHolomorphicExpression A B C D uH lH lK rK where
  domainExpression := E.codomainExpression
  codomainExpression := E.domainExpression
  simultaneous := E.simultaneous.symm

@[simp] theorem swap_simultaneous
    (E : SourceSimultaneousHolomorphicExpression A B C D uH lH lK rK) :
    E.swap.simultaneous = E.simultaneous.symm := rfl

/-- Transport the whole square along strip equivalences: conjugate every leg
and both expressions.  This is the transport-version statement of Card-SHE:
the simultaneity of the two composite expressions transports along
equivalences of the four strips. -/
def transport (E : SourceSimultaneousHolomorphicExpression A B C D uH lH lK rK)
    {A' B' C' D' : FPrimeStrip.{umon, uv, upi} V}
    (sigmaUL : FPrimeStripEquiv A A') (sigmaUR : FPrimeStripEquiv B B')
    (sigmaLL : FPrimeStripEquiv C C') (sigmaLR : FPrimeStripEquiv D D') :
    SourceSimultaneousHolomorphicExpression A' B' C' D'
      (uH.conjugate sigmaUL sigmaUR) (lH.conjugate sigmaLL sigmaLR)
      (lK.conjugate sigmaUL sigmaLL) (rK.conjugate sigmaUR sigmaLR) where
  domainExpression := E.domainExpression.conjugate sigmaUL sigmaLR
  codomainExpression := E.codomainExpression.conjugate sigmaUL sigmaLR
  simultaneous := by rw [E.simultaneous]

/-- The index component of the simultaneity equation. -/
theorem simultaneous_index
    (E : SourceSimultaneousHolomorphicExpression A B C D uH lH lK rK) (v : V) :
    E.domainExpression.index v = E.codomainExpression.index v :=
  congrArg (fun L : FPrimeStripLink A D => L.index v) E.simultaneous

/-- The Pi-fiber component of the simultaneity equation, in transport form:
after identifying the index fibers along `simultaneous_index`, the two Pi
homomorphisms agree on every element. -/
theorem simultaneous_mapPi_apply
    (E : SourceSimultaneousHolomorphicExpression A B C D uH lH lK rK)
    (v : V) (x : A.toDPrimeStrip.Pi v) :
    (E.simultaneous_index v) ▸ (E.domainExpression.mapPi v x) =
      E.codomainExpression.mapPi v x := by
  cases E with
  | mk d c h =>
    cases h
    rfl

/-- The G-fiber component of the simultaneity equation, in transport form. -/
theorem simultaneous_mapG_apply
    (E : SourceSimultaneousHolomorphicExpression A B C D uH lH lK rK)
    (v : V) (x : A.G v) :
    (E.simultaneous_index v) ▸ (E.domainExpression.mapG v x) =
      E.codomainExpression.mapG v x := by
  cases E with
  | mk d c h =>
    cases h
    rfl

/-- The Mon-fiber component of the simultaneity equation, in transport form. -/
theorem simultaneous_mapMon_apply
    (E : SourceSimultaneousHolomorphicExpression A B C D uH lH lK rK)
    (v : V) (x : A.Mon v) :
    (E.simultaneous_index v) ▸ (E.domainExpression.mapMon v x) =
      E.codomainExpression.mapMon v x := by
  cases E with
  | mk d c h =>
    cases h
    rfl

/-! ## 3. The (xi-b) consumer slot -/

/-- The (SHE) slot statement carried by the square: the two composite
expressions agree. -/
def sheStatement (E : SourceSimultaneousHolomorphicExpression A B C D uH lH lK rK) :
    Prop :=
  E.domainExpression = E.codomainExpression

@[simp] theorem sheStatement_eq
    (E : SourceSimultaneousHolomorphicExpression A B C D uH lH lK rK) :
    E.sheStatement = (E.domainExpression = E.codomainExpression) := rfl

/-- The (xi-b) consumer wiring: for a `StepXIContract` whose (SHE) slot is
instantiated with this square`s statement, the square`s simultaneity field is
evidence for the slot (the contract pattern of `Contract.lean:32-43`, `she`
at :38 and `she_evidence` at :41; the same shape is consumed by
`StepXIInput.she` / `she_evidence` at `ParametricStepXI.lean:36`/:39).  The
semantic landing predicate of `SourceArithmeticHolomorphicLanding.lean` (the
pending card `IUT-III.source-SHE-landing-evidence`) is a separate reduced
reading of the same slot and is not restated or consumed here. -/
theorem sheSlot_evidence
    (E : SourceSimultaneousHolomorphicExpression A B C D uH lH lK rK)
    {contract : StepXIContract} (h : contract.she = E.sheStatement) :
    contract.she :=
  Eq.mp h.symm E.simultaneous

end SourceSimultaneousHolomorphicExpression

end LeanFormal.IUT

namespace LeanFormal.IUT.Audit

/-- Card-SHE conditional assembly upgrade: the simultaneity square of the
Theta-link domain/codomain arithmetic holomorphic structures, its transport
laws, and the (xi-b) consumer wiring. -/
def sourceSHESimultaneityExchange : Obligation :=
  { id := "IUT-III.source-SHE-simultaneity-exchange"
    source :=
      "IUT III, Remark 3.11.1, (iii) (SHE; pagewise 9890-9907, PDF p. 161); " ++
        "Corollary 3.12, proof, Step (xi-b) (focused extract 1007-1044), " ++
        "(xi-c) (1045-1066)"
    status := VerificationStatus.interface
    note :=
      "Reduced simultaneity square for Card-SHE, frozen as an interface: " ++
        "SourceSimultaneousHolomorphicExpression (four F-prime-strip legs, two " ++
        "composite expressions, commuting equation; the domain/codomain " ++
        "structures are NOT identified), ofCommutingLegs (commuting four-leg " ++
        "squares), swap, transport along quadruples of FPrimeStripEquivs via the " ++
        "link-conjugation engine FPrimeStripLink.conjugate with its defining " ++
        "laws and composition compatibility, the fiber-level components of the " ++
        "simultaneity equation (simultaneous_index and the cast forms for " ++
        "Pi/G/Mon), and the (xi-b) consumer wiring sheStatement / " ++
        "sheSlot_evidence for the StepXIContract.she slot (Contract.lean:32-43; " ++
        "ParametricStepXI.lean:36/39 for the StepXIInput shape). NOT constructed: " ++
        "actual source Kummer arrows with weight/local-unit records (S2), the " ++
        "binding to the 1,circ column (S3), the holomorphic-hull expression " ++
        "(S4), and the times-mu/full-poly-isomorphism upgrade of the legs (G1). " ++
        "The two G1 negative results (probe SHA D660C2B4..., report section " ++
        "15.3) are relied on as recorded history and are NOT re-proved. No slot " ++
        "is closed by True; the semantic landing predicate and its pending " ++
        "evidence card IUT-III.source-SHE-landing-evidence " ++
        "(SourceArithmeticHolomorphicLanding.lean) remain separate."
    dependsOn :=
      [ "IUT-III.SHE",
        "IUT-III.source-arithmetic-holomorphic-landing",
        "IUT-I-II.prime-strip-core" ] }

end LeanFormal.IUT.Audit
