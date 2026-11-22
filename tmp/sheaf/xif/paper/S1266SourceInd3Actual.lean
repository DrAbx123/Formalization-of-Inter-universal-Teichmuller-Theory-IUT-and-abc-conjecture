import LeanFormal.IUT.IUTIII.Theorem311.SourceFTimesMuPrimeStripPolyIsomorphism
import LeanFormal.IUT.IUTIII.Theorem311.SourceProcessionCapsuleData

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

/-!
# S1266: actual (Ind3) times-mu stage data of IUT III, Theorem 3.11, from OriginalInput

## Source anchors

* IUT III, Theorem 3.11, (ii), the `(Ind3)` clause (physical page 156): as one
  varies `m` in Z, the isomorphisms of (a) are "upper semi-compatible",
  relative to the log-links of the `n`-th column of the log-theta-lattice,
  via inclusions at `v_Q` in `V^non_Q` and surjections at `v_Q` in `V^arc_Q`;
  cf. Proposition 3.5, (ii), (a), (b).
* IUT II, Definition 4.9, (i): the `x`-mu quotient is the quotient of the unit
  group by its full torsion subgroup.  The repository carrier for the
  F-turnstile-times-mu-prime-strips of Theorem 3.11(i) is
  `SourceFTimesMuPrimeStrip`, with full poly-isomorphisms
  `SourceFTimesMuPrimeStripFullPolyIsomorphism`.
* `SourceH1H2Construction.fPrimeStripAt` and `fLinkAt` are the actual source
  projections `(I.theaterAt n m).primeStrip` and
  `(I.linkAt n m n' m').primeStripEquiv` of the single input contract
  `OriginalInput`; no test carrier and no existential certificate is used.
* `SourceProcessionCapsuleData` is the repository data layer for the tensor
  packets of log-shells.  It records explicitly that the valuation set `VQ`,
  the place types `Place vQ`, the log-shell modules `Shell` and the
  poly-isomorphism action are additional named data, not fields or projections
  of `OriginalInput`.

## What this file constructs, for an arbitrary `I : OriginalInput l V`

* `ind3TimesMuStrip I n m` -- the `m`-indexed times-mu prime-strip.  Its
  underlying F-prime-strip is exactly `I.fPrimeStripAt n m`, and its times-mu
  fibers are exactly the torsion quotients of the actual unit groups;
* `ind3Stage` -- the actual `TimesMuQuotient` stage at `(n, m, v)`;
* `ind3StageAction` -- the actual `m`-indexed times-mu action, the descended
  units action of the actual stage, with the explicit formula on quotient
  classes (`ind3StageAction_quotientMap`);
* `ind3StagePolyIso` -- the actual full poly-isomorphism from stage `m` to the
  core stage `0`, induced by the actual source link `I.fLinkAt n m n 0`;
* `ind3StageComparison` -- the induced `TimesMuQuotient` stage comparison,
  with its action law, quotient-map law, degree law and identity law at
  `m = 0`;
* `sourceInd3StageData` -- the packaged (Ind3) stage data at a place.

## What is not constructed here, named exactly

The (Ind3) clause is a statement about tensor packets of log-shells and their
Kummer isomorphisms, not about the times-mu quotients: at the times-mu level
the stage comparison is an isomorphism (`ind3StageComparison_image_univ`), so a
one-sided containment/surjection comparison cannot arise from it.  The exact
first missing source datum is therefore the analytic log-shell carrier itself:
the module assignment `Shell i vQ v` that is the first field of
`SourceProcessionCapsule.LogShellFamily` (`Ind3LogShellCarrier` below, taken
over the actual places `V`).  `OriginalInput` has no field of that form, and the
only inhabitant of the data layer in the repository,
`SourceProcessionCapsuleContract.trivial`, is the one-point model, which its own
docstring states is not a faithfulness claim.  No instance of
`Ind3LogShellCarrier` is provided here, and none is asserted.

No proof placeholders, no new axiom, no trivial one-point carrier, and no
weakened restatement: every definition below is a projection of
`OriginalInput` or a field of an already proved source carrier, and every
theorem is proved.
-/

namespace LeanFormal.IUT.XiFPaper.S1266SourceInd3Actual

open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.SourceProcessionCapsule

noncomputable section

universe ua uv upi umon ui uR uShell

variable {l : PrimeGeFive} {V : Type uv}
variable (I : OriginalInput.{ua, uv, upi, umon, ui} l V)

/-! ## 1. The m-indexed times-mu prime-strip over the actual source strip -/

/-- The `m`-indexed times-mu prime-strip obtained from the actual source
F-prime-strip `I.fPrimeStripAt n m` by the canonical times-mu construction. -/
def ind3TimesMuStrip (n m : Int) : SourceFTimesMuPrimeStrip V :=
  SourceFTimesMuPrimeStrip.canonical (I.fPrimeStripAt n m)

/-- The underlying F-prime-strip of the stage-`m` times-mu prime-strip is the
actual source F-prime-strip at `(n, m)`. -/
theorem ind3TimesMuStrip_toFPrimeStrip (n m : Int) :
    (ind3TimesMuStrip I n m).toFPrimeStrip = I.fPrimeStripAt n m :=
  rfl

/-- The actual `TimesMuQuotient` stage at the vertical coordinate `m` and the
place `v`: the `x`-mu quotient of the unit group of the actual F-prime-strip. -/
abbrev Ind3Stage (n m : Int) (v : V) : Type umon :=
  TimesMuQuotient ((I.fPrimeStripAt n m).Mon v)ˣ

/-- The times-mu fiber of the stage-`m` times-mu prime-strip is exactly the
actual `TimesMuQuotient` stage. -/
theorem ind3TimesMuStrip_timesMu (n m : Int) (v : V) :
    (ind3TimesMuStrip I n m).timesMu v = Ind3Stage I n m v :=
  rfl

/-! ## 2. The m-indexed times-mu action -/

/-- The actual `m`-indexed times-mu action: the action of the geometric
`Pi`-group of the actual stage on its times-mu quotient, descended from the
actual units action of `I.fPrimeStripAt n m`. -/
def ind3StageAction (n m : Int) (v : V) :
    (I.fPrimeStripAt n m).toDPrimeStrip.Pi v →* MulAut (Ind3Stage I n m v) :=
  (I.fPrimeStripAt n m).timesMuAction v

/-- The times-mu action on a quotient class is the class of the actual units
action of the stage: the action is not an abstract replacement but the
descended actual action. -/
theorem ind3StageAction_quotientMap (n m : Int) (v : V)
    (g : (I.fPrimeStripAt n m).toDPrimeStrip.Pi v)
    (u : ((I.fPrimeStripAt n m).Mon v)ˣ) :
    ind3StageAction I n m v g (TimesMuQuotient.quotientMap u) =
      TimesMuQuotient.quotientMap ((I.fPrimeStripAt n m).unitsAction v g u) :=
  rfl

/-! ## 3. The stage comparison to the core stage 0 -/

/-- The actual full poly-isomorphism from the stage-`m` times-mu prime-strip to
the core stage `0`, induced by the actual source link `I.fLinkAt n m n 0`. -/
def ind3StagePolyIso (n m : Int) :
    SourceFTimesMuPrimeStripEquivalence
      (ind3TimesMuStrip I n m) (ind3TimesMuStrip I n 0) :=
  SourceFTimesMuPrimeStripEquivalence.canonicalLift (I.fLinkAt n m n 0)

/-- The actual `TimesMuQuotient` stage comparison from stage `m` to the core
stage `0`.  Its formula is `TimesMuQuotient.congr (Units.mapEquiv ((I.fLinkAt n m n 0).isoMon v))`,
the same formula as the paper-layer `xMuQuotientEquiv`, so this candidate and
the paper-layer construction compute the same comparison. -/
def ind3StageComparison (n m : Int) (v : V) :
    Ind3Stage I n m v ≃* Ind3Stage I n 0 v :=
  (ind3StagePolyIso I n m).isoTimesMu v

/-- Action compatibility of the stage comparison: it intertwines the stage-`m`
times-mu action with the core-stage action along the actual strip link. -/
theorem ind3StageComparison_action (n m : Int) (v : V)
    (g : (I.fPrimeStripAt n m).toDPrimeStrip.Pi v) (x : Ind3Stage I n m v) :
    ind3StageComparison I n m v (ind3StageAction I n m v g x) =
      ind3StageAction I n 0 v ((I.fLinkAt n m n 0).isoPi v g)
        (ind3StageComparison I n m v x) :=
  (ind3StagePolyIso I n m).compatAction v g x

/-- Quotient-map compatibility: on quotient classes the stage comparison is the
unit-level comparison induced by the actual `isoMon` of the strip link. -/
theorem ind3StageComparison_quotientMap (n m : Int) (v : V)
    (u : ((I.fPrimeStripAt n m).Mon v)ˣ) :
    ind3StageComparison I n m v (TimesMuQuotient.quotientMap u) =
      TimesMuQuotient.quotientMap
        (Units.mapEquiv ((I.fLinkAt n m n 0).isoMon v) u) :=
  (ind3StagePolyIso I n m).compatQuotientMap v u

/-- Degree compatibility: the stage comparison preserves the realified degree
of the actual times-mu prime-strips. -/
theorem ind3StageComparison_degree (n m : Int) (v : V) (x : Ind3Stage I n m v) :
    (ind3TimesMuStrip I n 0).timesMuDegree v (ind3StageComparison I n m v x) =
      (ind3TimesMuStrip I n m).timesMuDegree v x :=
  (ind3StagePolyIso I n m).compatDegree v x

/-- Identity law: at `m = 0` the stage comparison is the identity, because the
actual source link `I.fLinkAt n 0 n 0` is `FPrimeStripEquiv.refl`. -/
theorem ind3StageComparison_zero (n : Int) (v : V) :
    ind3StageComparison I n 0 v = MulEquiv.refl (Ind3Stage I n 0 v) := by
  rw [ind3StageComparison, ind3StagePolyIso, I.fLinkAt_refl]
  show TimesMuQuotient.congr
      (Units.mapEquiv (MulEquiv.refl ((I.fPrimeStripAt n 0).Mon v))) =
    MulEquiv.refl (Ind3Stage I n 0 v)
  rw [unitsMapEquiv_refl, TimesMuQuotient.congr_refl]

/-- Direction guard for the (Ind3) clause.  At the times-mu level the stage
comparison is an isomorphism, so the comparison image of the whole stage is the
whole core stage: the one-sided containment/surjection comparison of
Proposition 3.5, (ii), cannot be produced from the times-mu stages, and must
come from the analytic log-shell carriers that `OriginalInput` does not
supply. -/
theorem ind3StageComparison_image_univ (n m : Int) (v : V) :
    ind3StageComparison I n m v '' (Set.univ : Set (Ind3Stage I n m v)) =
      Set.univ := by
  rw [Set.image_univ]
  exact Set.range_eq_univ.mpr (ind3StageComparison I n m v).surjective

/-! ## 4. The packaged (Ind3) stage data -/

/-- The actual (Ind3) stage data at a place `v` and column `n`: the
`m`-indexed stage actions and the actual stage comparisons to the core stage,
together with the action law that ties them to the actual strip links. -/
structure SourceInd3StageData (n : Int) (v : V) where
  /-- The actual stage comparison from stage `m` to the core stage `0`. -/
  compare : ∀ m : Int, Ind3Stage I n m v ≃* Ind3Stage I n 0 v
  /-- The actual `m`-indexed times-mu action. -/
  action : ∀ m : Int,
    (I.fPrimeStripAt n m).toDPrimeStrip.Pi v →* MulAut (Ind3Stage I n m v)
  /-- The action law of the comparison. -/
  compat : ∀ (m : Int) (g : (I.fPrimeStripAt n m).toDPrimeStrip.Pi v)
      (x : Ind3Stage I n m v),
    compare m (action m g x) =
      action 0 ((I.fLinkAt n m n 0).isoPi v g) (compare m x)

/-- The actual (Ind3) stage data, assembled from the actual actions and the
actual strip links. -/
def sourceInd3StageData (n : Int) (v : V) : SourceInd3StageData I n v where
  compare m := ind3StageComparison I n m v
  action m := ind3StageAction I n m v
  compat m g x := ind3StageComparison_action I n m v g x

@[simp] theorem sourceInd3StageData_compare (n : Int) (v : V) (m : Int) :
    (sourceInd3StageData I n v).compare m = ind3StageComparison I n m v :=
  rfl

@[simp] theorem sourceInd3StageData_action (n : Int) (v : V) (m : Int) :
    (sourceInd3StageData I n v).action m = ind3StageAction I n m v :=
  rfl

/-! ## 5. The exact first missing source datum

The (Ind3) clause depends on the tensor packets of log-shells
`I(S^±_{j+1} F(n,∘D)_{v_Q})` and on their Kummer isomorphisms
(Proposition 3.5, (ii), (a), (b)).  The repository data layer
`SourceProcessionCapsule.LogShellFamily` has, as its first field, the module
assignment `Shell : (i : Capsule j) → (vQ : VQ) → Place vQ → Type uShell`.
At the actual places `V` that field is what is recorded below.  It is not a
projection of `OriginalInput`, and no instance is constructed. -/

/-- The exact first missing source datum: the analytic log-shell modules at the
actual places `V`, indexed by the capsule labels of `S^±_{j+1}`, i.e. the first
field of `SourceProcessionCapsule.LogShellFamily` taken over the actual places.
This is the carrier on which the Kummer isomorphisms of Proposition 3.5, (ii),
act. -/
structure Ind3LogShellCarrier (R : Type uR) [CommSemiring R] (j : Nat) where
  /-- The first missing field: the analytic log-shell module at each capsule
      label and each actual place. -/
  shell : (i : Capsule j) → V → Type uShell
  [addCommMonoid : ∀ i v, AddCommMonoid (shell i v)]
  [module : ∀ i v, Module R (shell i v)]

/-- Exactness of the recorded field: for any valuation set whose place types map
into the actual places, the log-shell assignment of `Ind3LogShellCarrier` is
literally the first field `Shell` of `SourceProcessionCapsule.LogShellFamily`.
Nothing is renamed or re-typed: the missing datum of this file is the first
field of the source data layer. -/
def Ind3LogShellCarrier.toLogShellFamily
    (R : Type uR) [CommSemiring R] (j : Nat)
    (L : Ind3LogShellCarrier.{uv, uR, uShell} (V := V) (R := R) j)
    (VQ : Type) (Place : VQ → Type) (p : ∀ vQ, Place vQ → V) :
    LogShellFamily R Place j where
  Shell i vQ v := L.shell i (p vQ v)
  addCommMonoid i vQ v := L.addCommMonoid i (p vQ v)
  module i vQ v := L.module i (p vQ v)

/-- The open source instance stated exactly: an actual log-shell carrier over
the actual places.  It is not proved, and it is not replaceable by the trivial
one-point model of the data layer. -/
def Ind3LogShellCarrierRequired (R : Type uR) [CommSemiring R] (j : Nat) : Prop :=
  Nonempty (Ind3LogShellCarrier.{uv, uR, uShell} (V := V) (R := R) j)

end

end LeanFormal.IUT.XiFPaper.S1266SourceInd3Actual

namespace LeanFormal.IUT.Audit

/-- Status record for the S1266 actual (Ind3) times-mu stage data. -/
def s1266SourceInd3Actual : Obligation :=
  { id := "IUT-III.Ind3.times-mu-stage-actual"
    source :=
      "IUT III, Theorem 3.11, (ii), (Ind3); Proposition 3.5, (ii), (a), (b); " ++
        "IUT II, Definition 4.9, (i)"
    status := VerificationStatus.sourceProjection
    note :=
      "Constructed for every OriginalInput: the m-indexed times-mu prime-strips " ++
        "over the actual F-prime-strips, the actual TimesMuQuotient stages, the " ++
        "m-indexed times-mu actions with their formula on quotient classes, and " ++
        "the actual stage comparisons to the core stage induced by the source " ++
        "links fLinkAt, with action, quotient-map, degree and identity laws. " ++
        "The stage comparison is an isomorphism, so the one-sided Ind3 " ++
        "containment/surjection clauses do not follow at this level; the exact " ++
        "first missing datum is the analytic log-shell carrier " ++
        "Ind3LogShellCarrier (the first field of LogShellFamily), which is " ++
        "declared but not constructed or asserted."
    dependsOn :=
      [ "IUT-II.times-mu-torsion-quotient"
      , "IUT-III.Ind3.upper-semi-reduction"
      , "IUT-III.ind3-upper-semi-construction" ] }

end LeanFormal.IUT.Audit
