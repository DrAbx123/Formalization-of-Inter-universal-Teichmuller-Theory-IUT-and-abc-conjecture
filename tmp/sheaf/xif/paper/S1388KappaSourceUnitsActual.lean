import LeanFormal.IUT.IUTII.Frobenioid.SourceKappaOrbitUnitsActionSupply
import tmp.sheaf.xif.paper.S1187NonReflKummerCommonGroupActual
import LeanFormal.IUT.IUTIII.Theorem311.SourceH1H2Construction
import LeanFormal.IUT.IUTI.HodgeTheater.SourceHodgeTheaterFamilySourceReduction

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 2000000

/-!
# S1388: actual source units and a pair datum with non-refl Kummer representatives

The S1302 gap fixed the first field of `KappaOrbitUnitsActionPairDatum` as
`sourceUnits`/`sourceAction` of IUT II, Definition 4.9, (i).  This file
constructs the pair datum on an actual source unit group, with both Kummer
representatives coming from actual source links (no `Isomorphism.refl`, no
finite model):

* the source strip is the actual intermediate strip `S01 = I.fPrimeStripAt 0 1`;
* `sourceUnits v = (S01.Mon v)^x`, the actual source units of that strip;
* `sourceAction v` is the actual `unitsAction` of `S01` composed with the
  canonical evaluation factorization;
* the upper/lower factors are the actual source links `S01 -> S00` and
  `S01 -> S11` (restrictions of `I.fLinkAt`);
* `kappaUpper`/`kappaLower` are the S1187 non-refl Kummer isomorphisms of
  those actual links.

Reduction (explicit): the repository's strip groups `Pi v` carry no profinite
topology, so the product group is given the indiscrete fallback topology, as in
S1195/S1187.  The `OpenSubgroup` quantification in the Kummer laws is therefore
over that topology (effectively only the top open subgroup), not over the
paper's full profinite open-subgroup lattice.

The file also states exactly what is still missing: the paper's group-theoretic
`O^x(G)` module/action and its identification with the actual strip units.
Without that identification a pointwise `kappa.equiv x != x` statement is not
even well-typed, because the two sides live on the unit groups of different
strips (the S1210 note does not record this type-level point).
-/

namespace LeanFormal.IUT.XiFPaper.S1388KappaSourceUnitsActual

open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.XiFPaper.S1187NonReflKummerCommonGroupActual

universe ua uv upi umon ui

variable {l : PrimeGeFive} {V : Type uv}
variable (I : OriginalInput.{ua, uv, upi, umon, ui} l V)

/-- The actual lower-left strip S(0,0). -/
abbrev S00 : FPrimeStrip.{umon, uv, upi} V := I.fPrimeStripAt 0 0

/-- The actual intermediate strip S(0,1), used as the source module. -/
abbrev S01 : FPrimeStrip.{umon, uv, upi} V := I.fPrimeStripAt 0 1

/-- The actual lower-right strip S(1,1). -/
abbrev S11 : FPrimeStrip.{umon, uv, upi} V := I.fPrimeStripAt 1 1

local instance topS01 : ∀ v : V, TopologicalSpace ((S01 (I := I)).Pi v) :=
  fun _ => ⊥

/-- The common group of the actual intermediate strip: the product of its
local geometric groups. -/
abbrev MiddleGraph : Type _ := GraphGroup (upper := S01 (I := I))

/-- The canonical evaluation factorization of the intermediate strip. -/
noncomputable def middleEval (v : V) : MiddleGraph (I := I) →* (S01 (I := I)).Pi v :=
  factorUpper (upper := S01 (I := I)) v

/-- The actual S01 -> S00 factorization through the source link. -/
noncomputable def pairFactorUpper (v : V) :
    MiddleGraph (I := I) →* (S00 (I := I)).Pi v :=
  factorLower (upper := S01 (I := I)) (lower := S00 (I := I))
    (I.fLinkAt 0 1 0 0) v

/-- The actual S01 -> S11 factorization through the source link. -/
noncomputable def pairFactorLower (v : V) :
    MiddleGraph (I := I) →* (S11 (I := I)).Pi v :=
  factorLower (upper := S01 (I := I)) (lower := S11 (I := I))
    (I.fLinkAt 0 1 1 1) v

/-- The actual upper Kummer representative from the source link S01 -> S00. -/
noncomputable def middleKappaUpper (v : V) :
    TimesMuKummer.Isomorphism
      (((S01 (I := I)).unitsAction v).comp (middleEval (I := I) v))
      (((S00 (I := I)).unitsAction v).comp (pairFactorUpper (I := I) v)) :=
  kummerIsoAt (upper := S01 (I := I)) (lower := S00 (I := I))
    (I.fLinkAt 0 1 0 0) v

/-- The actual lower Kummer representative from the source link S01 -> S11. -/
noncomputable def middleKappaLower (v : V) :
    TimesMuKummer.Isomorphism
      (((S01 (I := I)).unitsAction v).comp (middleEval (I := I) v))
      (((S11 (I := I)).unitsAction v).comp (pairFactorLower (I := I) v)) :=
  kummerIsoAt (upper := S01 (I := I)) (lower := S11 (I := I))
    (I.fLinkAt 0 1 1 1) v

/-- The actual pair datum.  The source module is the unit group of the actual
intermediate strip; both representatives are actual link isomorphisms. -/
noncomputable def actualMiddlePairDatum :
    KappaOrbitUnitsActionPairDatum (MiddleGraph (I := I))
      (S00 (I := I)) (S11 (I := I)) where
  sourceUnits := fun v => ((S01 (I := I)).Mon v)ˣ
  commGroupSourceUnits := fun _ => inferInstance
  sourceAction := fun v => ((S01 (I := I)).unitsAction v).comp (middleEval (I := I) v)
  factorUpper := pairFactorUpper (I := I)
  factorLower := pairFactorLower (I := I)
  kappaUpper := middleKappaUpper (I := I)
  kappaLower := middleKappaLower (I := I)

@[simp] theorem actualMiddlePairDatum_sourceUnits (v : V) :
    (actualMiddlePairDatum (I := I)).sourceUnits v = ((S01 (I := I)).Mon v)ˣ := rfl

@[simp] theorem actualMiddlePairDatum_sourceAction (v : V) :
    (actualMiddlePairDatum (I := I)).sourceAction v =
      ((S01 (I := I)).unitsAction v).comp (middleEval (I := I) v) := rfl

@[simp] theorem actualMiddlePairDatum_factorUpper (v : V) :
    (actualMiddlePairDatum (I := I)).factorUpper v = pairFactorUpper (I := I) v := rfl

@[simp] theorem actualMiddlePairDatum_factorLower (v : V) :
    (actualMiddlePairDatum (I := I)).factorLower v = pairFactorLower (I := I) v := rfl

@[simp] theorem actualMiddlePairDatum_kappaUpper (v : V) :
    (actualMiddlePairDatum (I := I)).kappaUpper v = middleKappaUpper (I := I) v := rfl

@[simp] theorem actualMiddlePairDatum_kappaLower (v : V) :
    (actualMiddlePairDatum (I := I)).kappaLower v = middleKappaLower (I := I) v := rfl


/-! ## The source and target strips are distinct actual strips -/

/-- The actual strips S(0,1) and S(0,0) are distinct prime strips: the
Hodge-theater family has aligned arithmetic and distinct indices. -/
theorem S01_ne_S00 : S01 (I := I) ≠ S00 (I := I) := by
  have h : I.indexOf 0 1 ≠ I.indexOf 0 0 := by
    intro h
    have h' := congrArg I.index_equiv h
    simp [I.indexOf_apply] at h'
  exact primeStrip_ne_of_index_ne_of_arithmetic_eq (F := I.family)
    (A := I.initial.arithmetic) (fun i => I.arithmetic_alignment i) h

/-- The actual strips S(0,1) and S(1,1) are distinct prime strips. -/
theorem S01_ne_S11 : S01 (I := I) ≠ S11 (I := I) := by
  have h : I.indexOf 0 1 ≠ I.indexOf 1 1 := by
    intro h
    have h' := congrArg I.index_equiv h
    simp [I.indexOf_apply] at h'
  exact primeStrip_ne_of_index_ne_of_arithmetic_eq (F := I.family)
    (A := I.initial.arithmetic) (fun i => I.arithmetic_alignment i) h

/-! ## The two representatives are the actual link isomorphisms -/

/-- The upper representative is literally the S1187 link isomorphism. -/
theorem middleKappaUpper_eq_kummerIsoAt (v : V) :
    middleKappaUpper (I := I) v =
      kummerIsoAt (upper := S01 (I := I)) (lower := S00 (I := I))
        (I.fLinkAt 0 1 0 0) v := rfl

/-- The lower representative is literally the S1187 link isomorphism. -/
theorem middleKappaLower_eq_kummerIsoAt (v : V) :
    middleKappaLower (I := I) v =
      kummerIsoAt (upper := S01 (I := I)) (lower := S11 (I := I))
        (I.fLinkAt 0 1 1 1) v := rfl

/-- Pointwise formula for the upper representative: it is the quotient
equivalence induced by the actual unit equivalence of the link S01 -> S00. -/
theorem middleKappaUpper_equiv_apply (v : V)
    (u : ((S01 (I := I)).Mon v)ˣ) :
    (middleKappaUpper (I := I) v).equiv (TimesMuQuotient.quotientMap u) =
      TimesMuQuotient.quotientMap
        (Units.mapEquiv ((I.fLinkAt 0 1 0 0).isoMon v) u) := by
  unfold middleKappaUpper
  rw [kummerIsoAt_equiv]
  exact quotientUnitsEquiv_quotientMap _ u

/-- Pointwise formula for the lower representative: it is the quotient
equivalence induced by the actual unit equivalence of the link S01 -> S11. -/
theorem middleKappaLower_equiv_apply (v : V)
    (u : ((S01 (I := I)).Mon v)ˣ) :
    (middleKappaLower (I := I) v).equiv (TimesMuQuotient.quotientMap u) =
      TimesMuQuotient.quotientMap
        (Units.mapEquiv ((I.fLinkAt 0 1 1 1).isoMon v) u) := by
  unfold middleKappaLower
  rw [kummerIsoAt_equiv]
  exact quotientUnitsEquiv_quotientMap _ u

/-- The assembled two-strip layer is the composite of the two actual link
isomorphisms. -/
theorem actualMiddlePairDatum_layerKummer_equiv_apply (v : V)
    (x : TimesMuQuotient ((S00 (I := I)).Mon v)ˣ) :
    ((actualMiddlePairDatum (I := I)).layerKummer v).equiv x =
      (middleKappaLower (I := I) v).equiv
        ((middleKappaUpper (I := I) v).equiv.symm x) := rfl

/-- No identity representative is used for either side: the source carrier
is the actual intermediate strip S01, while the targets are the actual strips
S00 and S11.  The two representatives are the actual S1187 link isomorphisms
above, not the canonical identity completion of the upper or lower strip. -/
theorem actualMiddlePairDatum_kappaUpper_eq_link (v : V) :
    (actualMiddlePairDatum (I := I)).kappaUpper v =
      kummerIsoAt (upper := S01 (I := I)) (lower := S00 (I := I))
        (I.fLinkAt 0 1 0 0) v := rfl

/-- Lower-side form of the same exactness statement. -/
theorem actualMiddlePairDatum_kappaLower_eq_link (v : V) :
    (actualMiddlePairDatum (I := I)).kappaLower v =
      kummerIsoAt (upper := S01 (I := I)) (lower := S11 (I := I))
        (I.fLinkAt 0 1 1 1) v := rfl

/-! ## Exact remaining source field

The pair datum above is built from the actual unit group of the intermediate
actual strip S01.  It is a genuine unit-group source module of an actual strip,
and both Kummer representatives are actual link isomorphisms, so neither is
the identity completion of the upper or lower strip.

The paper's O^x(G) of IUT II, Definition 4.9, (i) is the group-theoretic
algorithm applied to the abstract group G.  That algorithm, and hence an
identification of the abstract group G with the strip groups together with an
identification of the paper's module with the actual strip unit group, is not
constructed in the repository.  This is the exact remaining first field.

The other actual source-side carriers considered for sourceUnits do not close
this field:

* the actual log-shell carrier of SourceLogShellCarrier/SourceLocalLogShellDatum
  has a genuine commutative unit group (the integral units of the completion),
  but the repository G-actions on the log-shell (SourceLogShellXMuChainAction-
  Compatibility) are Q-linear actions on the additive log-coordinate field K,
  not multiplicative actions on that unit group; no TimesMuKummer.Isomorphism
  from them to the strip units is constructed;
* the actual Ind3 stage Ind3Stage I n m v is a TimesMuQuotient of the actual
  strip units with an actual Ind3 action, but using it as sourceUnits forces
  the double quotient TimesMuQuotient (TimesMuQuotient U) and the natural
  comparison to the strip action does not satisfy the invariant-image law of
  TimesMuKummer.Isomorphism (the fixed subgroup on the quotient can be strictly
  larger than the image of the fixed subgroup on U); it is therefore not a
  valid source module for the kappa pair;
* the actual middle strip unit group used above is the only available actual
  CommGroup with a genuine G-action and actual link isomorphisms to both
  targets.  It is not the paper's O^x(G), which is exactly the remaining
  identification.

There is a second, type-level point that the S1210 witness note does not
record: TimesMuKummer.Isomorphism relates TimesMuQuotient U and
TimesMuQuotient W for the two actual carriers U = (S01.Mon v)^x and
W = (S00.Mon v)^x (respectively (S11.Mon v)^x).  These are different types,
so a pointwise statement that kappa.equiv x is not x is not well-typed without
a comparison map between the two carriers.  The identity-Isomorphism
alternative is therefore unavailable for these representatives by construction;
a numerical nontriviality witness requires the missing group-theoretic
identification above.  No weak Nonempty, True, PUnit, finite model, axiom, or
sorry is inserted to replace it.
-/
/-! ## Axiom probes -/

#print axioms actualMiddlePairDatum
#print axioms middleKappaUpper_equiv_apply
#print axioms middleKappaLower_equiv_apply
#print axioms actualMiddlePairDatum_layerKummer_equiv_apply
#print axioms actualMiddlePairDatum_kappaUpper_eq_link
#print axioms actualMiddlePairDatum_kappaLower_eq_link
#print axioms S01_ne_S00
#print axioms S01_ne_S11

end LeanFormal.IUT.XiFPaper.S1388KappaSourceUnitsActual
