/-
Copyright (c) 2026 LeanFormal contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import tmp.sheaf.xif.paper.S1978LocalFieldOCarrierActual
import tmp.sheaf.xif.paper.S1895OIdentificationsActual
import tmp.sheaf.xif.paper.S1527OOrderEqualityActual
import tmp.sheaf.xif.paper.OneColumnFinitePrimePlaceActual
import tmp.sheaf.xif.paper.S1679CompleteODCarrierActual
import tmp.sheaf.xif.paper.OrigXiFPaperBoundaryStripActual
import tmp.sheaf.xif.paper.IPLAPTDataActual
import LeanFormal.IUT.IUTIII.Theorem311.SourceH1H2Construction

/-!
# S1992: the rebased local O^× input

Layer: **O** (original Theta-link / q-pilot), direct worker of S1978.

## The gap addressed

S1978 constructs the actual local `O^×` carrier
`LocalOFieldUnits p = (Integers (AlgebraicClosure Q_p))^×`, its actual local
Galois action, its nontrivial `O^×μ` quotient, the actual local `O^×`
F-prime-strip `localOFieldStrip` on the S1895 place type, and a reduced paper
q-pilot object `localOFieldPaperO` carrying that strip.  It proves that the
local strip is **not** equivalent to the S1487 shear strip
(`no_localOFieldStrip_equiv_shear`), hence that the S1895 input cannot be
re-based by an equivalence of strips; the input itself must be rebuilt.  It
then *records* the missing objects

  `S1978RebasedPaperInput D`  (an `OriginalInput` with the same initial data
  whose `(1,0)` F-prime-strip is `localOFieldStrip`) and
  `S1978RebasedPaperO D`      (the corresponding `PaperQPilotObject`),

without constructing them.  This file attacks exactly that pair.

## What is constructed here

1. **The rebased theater-family datum.** `S1992RebasedLocalFamily D` is the
   exact input-side datum that S1978's missing type asks for at the family
   level: a `SourceHodgeTheaterFamily` over the S1895 place type
   `PaperV = FinitePrimePlace 2 7`, an index equivalence with `Int × Int`,
   the arithmetic alignment with the S1895 initial data, and the requirement
   that the `(1,0)` member's prime-strip **is** `localOFieldStrip`.

2. **The rebased input.** `S1992RebasedLocalFamily.toInput` builds the
   `OriginalInput` with the S1895 initial data out of that datum, and
   `S1992RebasedLocalFamily.toRebasedInput` inhabits S1978's
   `S1978RebasedPaperInput D`; conversely `ofRebasedInput` recovers the
   datum from S1978's missing type.  Hence, proved:
   `Nonempty (S1978RebasedPaperInput D) ↔ Nonempty (S1992RebasedLocalFamily D)`:
   the family datum is *exactly* the missing input, with no loss.

3. **The paper q-pilot object on the rebased input.**
   `S1992RebasedPaperO D E : S1978RebasedPaperO D` for every datum `E`.
   Its four `PaperQPilotObject` identification slots are instantiated by the
   *actual* S1895 paper-level propositions (`S1895FTimesMuProp`,
   `S1895FullLogKummerProp`, `S1679PaperLineBundleIdentified`,
   `S1895ScalarProp`) and each of them is **proved** for the rebased input:
   the `(1,0)` core of the rebased input is `localOFieldStrip`, so the
   canonical times-mu strip is fully poly-isomorphic to itself; the one-column
   log-Kummer correspondence is the actual S1895 correspondence of the rebased
   input; the line bundle is the actual S1679 `O(-D)` carrier; and the q-pilot
   scalar is the actual S1487/S1527 completion magnitude because the rebased
   input has the same initial data.  The strip anchors and the `(1,0)` label
   binding are also proved.

4. **Structure of any strip compatible with the local one.**  For any
   F-prime-strip `S` linked to `localOFieldStrip`:
   * its value monoid at `v` is the actual local `O^×` group up to the link
     (`linked_mon_equiv`);
   * its degree is trivial (`linked_degree_trivial`) — the actual norm-log
     degree of an integral unit is `1` since every integral unit has norm one
     (`localOFieldUnitsDegree_apply_eq_one`);
   * its action is the transport of the actual local Galois action along the
     link (`linked_action_form`).
   Consequently all genuine freedom of a "compatible local strip" sits in the
   per-place transport data (equivalences of the local absolute Galois groups
   and of the `O^×` value monoid); the value-monoid content and the degree
   are forced.

5. **The obstruction inside the rebased family.**  A `HodgeTheater` is
   determined by its arithmetic data, its prime-strip and its theta packet, and
   the family links force all theta `q`'s — hence all theta packets — to
   agree (`thetaPacket_eq_of_q_eq`).  Therefore in any
   `SourceHodgeTheaterFamily` the map `i ↦ primeStrip` is injective
   (`S1992RebasedLocalFamily.strip_injective`).  Three consequences are proved:
   * a family all of whose theaters carry *exactly* `localOFieldStrip` has at
     most one index (`index_subsingleton_of_constant_local_strip`); so the
     rebased family necessarily contains at least two **distinct** local strips
     (`S1992RebasedLocalFamily.exists_distinct_strips`), indeed infinitely many
     (`S1992RebasedLocalFamily.infinite_strips`);
   * every member's strip is linked to `localOFieldStrip` by the actual family
     link (`S1992RebasedLocalFamily.other_strip_linked`);
   * no Hodge-theater link can exist between a theater carrying
     `localOFieldStrip` and a theater carrying an S1487 shear strip
     (`no_hodgeTheaterLink_local_shear`); so the S1487/S1527 shear family
     cannot be patched by replacing its `(1,0)` member — the whole family has
     to be rebuilt on the local carrier.

## The exact first missing

`S1992FirstMissing D := S1992RebasedLocalFamily D` (equivalently,
`S1978RebasedPaperInput D`).  By item 5 this datum is *not* a cosmetic
restatement: its strip map must be injective on `Int × Int`, so it must supply
infinitely many pairwise **distinct** F-prime-strips, each linked to the actual
local `O^×` strip and hence (item 4) carrying the actual local `O^×` value
monoid, the trivial degree and an action transported from the actual local
Galois action.  Concretely, the missing construction is

  a family of per-place decorations of `localOFieldStrip` — triples of
  equivalences `(Pi_v ≃ Pi_v, G_v ≃ G_v, O^×_v ≃ O^×_v)` at each place `v`
  of `FinitePrimePlace 2 7`, whose induced strip data are provably pairwise
  distinct —

i.e. it requires actual non-identity automorphism data of the local absolute
Galois groups / of the local `O^×` carrier.  The tree constructs no nontrivial
automorphism of `LocalAbsoluteGalois p` and no non-identity `AlgEquiv` of a
p-adic algebraic closure; the value-monoid degree cannot supply the distinction
because it is provably trivial (item 4).  This is the exact remaining gap; it is
recorded below as a structure with no inhabitant, not faked.

No `sorry`, `axiom`, `True`/`PUnit` slot, empty type, arbitrary
inhabitant or `Nonempty` gate is used.  The missing datum is a structure; the
only conditional results are of the form "a datum gives the paper object".
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.XiFPaper.S1992RebasedLocalInputActual

/-- The concrete Gaussian field of the S1280/S1487/S1895/S1527 source data is a
field: `X^2 + 1` is irreducible over `ℚ`.  This is the same local instance
the S1895 and S1527 files use; it is a proved fact, not an assumption. -/
local instance s1992GaussianIrreducible :
    Fact (Irreducible (Polynomial.X ^ 2 - Polynomial.C (-1) : Polynomial ℚ)) :=
  ⟨gaussianPolynomial_irreducible⟩

local instance s1992FivePrime : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩

open LeanFormal.IUT
open LeanFormal.IUT.LocalFieldIntegralUnits
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.ArithmeticQPilotLogVolume
open LeanFormal.IUT.XiFPaper.S1951KummerEvaluationSquareActual
open LeanFormal.IUT.XiFPaper.S1527OOrderEqualityActual
open LeanFormal.IUT.XiFPaper.S1487OQPilotScalarEqualityActual
open LeanFormal.IUT.XiFPaper.S1895OIdentificationsActual
open LeanFormal.IUT.XiFPaper.S1978LocalFieldOCarrierActual
open LeanFormal.IUT.XiFPaper.S1679CompleteODCarrierActual
open LeanFormal.IUT.XiFPaper.OrigXiFPaperBoundaryStrip
open LeanFormal.IUT.XiFPaper.OneColumnFinitePrimePlaceActual
open LeanFormal.IUT.Theorem311Source.IPLAPTDataActual

/-! ## 1. Theta packets and Hodge theaters -/

theorem thetaPacket_eq_of_q_eq {l : PrimeGeFive} {P Q : FiniteThetaPacket l}
    (h : P.q = Q.q) : P = Q := by
  obtain ⟨q, hq, s, hse⟩ := P
  obtain ⟨q', hq', s', hse'⟩ := Q
  simp only at h
  subst h
  have hs : s = s' := funext fun j => (hse j).trans (hse' j).symm
  subst hs
  rfl

/-- Two Hodge theaters with the same arithmetic data, the same prime-strip and
the same theta packet are equal. -/
theorem hodgeTheater_eq_of_components {l : PrimeGeFive} {V : Type}
    {T T' : HodgeTheater.{0, 0, 0, 0} l V}
    (ha : T.arithmetic = T'.arithmetic) (hs : T.primeStrip = T'.primeStrip)
    (hp : T.thetaPacket = T'.thetaPacket) : T = T' := by
  cases T
  cases T'
  simp only at ha hs hp
  rw [ha, hs, hp]

/-! ## 2. The rebased theater-family datum -/

/-- **The exact input-side datum of the rebased local O^× paper input.**  A
source Hodge-theater family over the S1895 place type whose index is
`Int × Int`, whose arithmetic data is the S1895 initial arithmetic, and whose
`(1,0)` member carries the actual local `O^×` strip `localOFieldStrip`.

This is the datum that S1978 recorded as missing.  It is not inhabited here;
see section 5 for the structural obstructions that any inhabitant must meet. -/
structure S1992RebasedLocalFamily (D : S1895PaperInput) where
  /-- the rebased Hodge-theater family on the S1895 place type -/
  family : SourceHodgeTheaterFamily.{0, 0, 0, 0, 0} D.l PaperV
  /-- the lattice coordinates of the family index -/
  index_equiv : family.index ≃ SourceTheorem311Index
  /-- every theater uses the S1895 initial arithmetic data -/
  arithmetic_alignment : ∀ i, (family.theater i).arithmetic =
    (S1895PaperInput.I D).initial.arithmetic
  /-- the `(1,0)` member carries the actual local `O^×` strip -/
  core_eq_local : (family.theater (index_equiv.symm (1, 0))).primeStrip =
    localOFieldStrip

namespace S1992RebasedLocalFamily

variable {D : S1895PaperInput}

/-- The rebased original input: the S1895 initial data on the rebased family. -/
noncomputable def toInput (E : S1992RebasedLocalFamily D) :
    OriginalInput.{0, 0, 0, 0, 0} D.l PaperV where
  initial := (S1895PaperInput.I D).initial
  family := E.family
  index_equiv := E.index_equiv
  arithmetic_alignment := E.arithmetic_alignment

/-- The `(1,0)` core of the rebased input is the `(1,0)` member of the
rebased family. -/
theorem toInput_fPrimeStripAt_zero (E : S1992RebasedLocalFamily D) :
    E.toInput.fPrimeStripAt 1 0 =
      (E.family.theater (E.index_equiv.symm (1, 0))).primeStrip := rfl

/-- The `(1,0)` F-prime-strip of the rebased input is the actual local
`O^×` strip. -/
theorem toInput_core_eq_local (E : S1992RebasedLocalFamily D) :
    E.toInput.fPrimeStripAt 1 0 = localOFieldStrip :=
  E.core_eq_local

/-- Its initial theta data is the S1895 initial data. -/
theorem toInput_initial (E : S1992RebasedLocalFamily D) :
    E.toInput.initial = (S1895PaperInput.I D).initial := rfl

/-- **An inhabitant of S1978's missing rebased input.** -/
noncomputable def toRebasedInput (E : S1992RebasedLocalFamily D) :
    S1978RebasedPaperInput D where
  input := E.toInput
  same_initial := rfl
  core_eq_local := E.toInput_core_eq_local

/-- The converse: S1978's missing rebased input is an inhabitant of the family
datum.  Hence the family datum loses nothing. -/
noncomputable def ofRebasedInput (R : S1978RebasedPaperInput D) :
    S1992RebasedLocalFamily D where
  family := R.input.family
  index_equiv := R.input.index_equiv
  arithmetic_alignment := fun i =>
    (R.input.arithmetic_alignment i).trans
      (congrArg (fun S : SourceDefinition31Data D.l => S.arithmetic) R.same_initial)
  core_eq_local := R.core_eq_local

/-- The rebased input datum and the family datum are the same missing object. -/
theorem nonempty_iff_rebasedPaperInput (D : S1895PaperInput) :
    Nonempty (S1978RebasedPaperInput D) ↔
      Nonempty (S1992RebasedLocalFamily D) :=
  ⟨fun ⟨R⟩ => ⟨ofRebasedInput R⟩, fun ⟨E⟩ => ⟨E.toRebasedInput⟩⟩

end S1992RebasedLocalFamily

/-! ## 3. The paper q-pilot object on the rebased input

The point of the rebased input is that the `(1,0)` core is the *actual local*
strip, so every paper-level identification slot can be instantiated by the
actual S1895 paper proposition and proved at the rebased input.  Nothing here is
a local surrogate. -/

/-- The `PaperQPilotObject` over the rebased input, with `(1,0)` strip the
actual local `O^×` strip and all four paper-level identification slots
instantiated by the actual S1895 paper propositions. -/
noncomputable def S1992RebasedPaperObject (D : S1895PaperInput)
    (E : S1992RebasedLocalFamily D) :
    PaperQPilotObject (l := D.l) (V := PaperV)
      (Label := OrigXiFPaperLabel)
      (Choice := OrigXiFPaperChoice E.toInput)
      E.toInput
      (SelfGroup localOFieldStrip)
      localOFieldStrip where
  boundary := OrigXiFPaperBoundary E.toInput 1 0
  strip := localOFieldStrip
  strip_eq_source := E.toInput_core_eq_local.symm
  oneColumn := actualOneColumnFinitePrimePlace
  lineBundle := s1679Carrier D.l
  logKummer := selfKummerArrow localOFieldStrip
  qPilotLogVolume := sourceQPilotSignedLog E.toInput.initial
  qPilotLogVolume_eq := rfl
  paper_strip_identification := S1895FTimesMuProp E.toInput localOFieldStrip
  paper_lineBundle_identification := S1679PaperLineBundleIdentified D.l
  paper_logKummer_identification := S1895FullLogKummerProp E.toInput
  paper_qPilot_log_identification :=
    S1895ScalarProp E.toInput (sourceQPilotSignedLog E.toInput.initial)

/-- **The rebased paper q-pilot object of S1978**, inhabited from the family
datum. -/
noncomputable def S1992RebasedPaperO (D : S1895PaperInput)
    (E : S1992RebasedLocalFamily D) : S1978RebasedPaperO D where
  rebased := E.toRebasedInput
  object := S1992RebasedPaperObject D E
  object_strip := rfl

/-- The rebased paper object's strip is the actual local `O^×` strip. -/
theorem S1992RebasedPaperO_strip (D : S1895PaperInput)
    (E : S1992RebasedLocalFamily D) :
    (S1992RebasedPaperO D E).object.strip = localOFieldStrip :=
  (S1992RebasedPaperO D E).object_strip

/-- The rebased input's initial data is the S1895 initial data. -/
theorem S1992RebasedPaperO_initial (D : S1895PaperInput)
    (E : S1992RebasedLocalFamily D) :
    (S1992RebasedPaperO D E).rebased.input.initial =
      (S1895PaperInput.I D).initial :=
  (S1992RebasedPaperO D E).rebased.same_initial

/-- The `(1,0)` core of the rebased paper object's input is the local strip. -/
theorem S1992RebasedPaperO_core (D : S1895PaperInput)
    (E : S1992RebasedLocalFamily D) :
    (S1992RebasedPaperO D E).rebased.input.fPrimeStripAt 1 0 =
      localOFieldStrip :=
  (S1992RebasedPaperO D E).rebased.core_eq_local

/-- **Paper-level F-times-mu identification, proved on the rebased input.**  The
canonical times-mu strip on `localOFieldStrip` is fully poly-isomorphic to the
canonical times-mu strip on the rebased `(1,0)` core, because that core *is*
`localOFieldStrip`. -/
theorem S1992RebasedPaperO_paper_strip (D : S1895PaperInput)
    (E : S1992RebasedLocalFamily D) :
    (S1992RebasedPaperO D E).object.paper_strip_identification := by
  change Nonempty (SourceFTimesMuPrimeStripFullPolyIsomorphism
    (SourceFTimesMuPrimeStrip.canonical localOFieldStrip)
    (SourceFTimesMuPrimeStrip.canonical
      ((S1992RebasedPaperO D E).rebased.input.fPrimeStripAt 1 0)))
  rw [S1992RebasedPaperO_core D E]
  exact ⟨SourceFTimesMuPrimeStripFullPolyIsomorphism.id _⟩

/-- **Paper-level full one-column log-Kummer identification, proved on the
rebased input.** -/
theorem S1992RebasedPaperO_paper_logKummer (D : S1895PaperInput)
    (E : S1992RebasedLocalFamily D) :
    (S1992RebasedPaperO D E).object.paper_logKummer_identification :=
  ⟨s1895FullLogKummerCorrespondence (S1992RebasedPaperO D E).rebased.input,
    rfl⟩

/-- **Paper-level line-bundle identification, proved on the rebased input**: it
is the actual S1679 `O(-D)` identification. -/
theorem S1992RebasedPaperO_paper_lineBundle (D : S1895PaperInput)
    (E : S1992RebasedLocalFamily D) :
    (S1992RebasedPaperO D E).object.paper_lineBundle_identification :=
  s1679_identified D.l

/-- The rebased q-pilot scalar is the actual completion magnitude
`-localLogMagnitude S1487Cand = -(order_C3 * log 5)`: the rebased input has
the S1895 initial data, for which the actual S1527/S1487 evaluation is
proved. -/
theorem S1992RebasedPaperO_qPilot_eq (D : S1895PaperInput)
    (E : S1992RebasedLocalFamily D) :
    (S1992RebasedPaperO D E).object.qPilotLogVolume =
      -localLogMagnitude S1487Cand := by
  change sourceQPilotSignedLog (S1992RebasedPaperO D E).rebased.input.initial =
    -localLogMagnitude S1487Cand
  rw [S1992RebasedPaperO_initial D E]
  exact s1895PaperO_qPilot_eq D

/-- **Paper-level q-pilot log-volume identification, proved on the rebased
input**: the scalar is the actual completion magnitude and is nonpositive. -/
theorem S1992RebasedPaperO_paper_qPilot (D : S1895PaperInput)
    (E : S1992RebasedLocalFamily D) :
    (S1992RebasedPaperO D E).object.paper_qPilot_log_identification :=
  ⟨S1992RebasedPaperO_qPilot_eq D E,
    sourceQPilotSignedLog_nonpos _⟩

/-- The two strip anchors of the rebased paper object. -/
theorem S1992RebasedPaperO_anchors (D : S1895PaperInput)
    (E : S1992RebasedLocalFamily D) :
    (S1992RebasedPaperO D E).object.strip =
        sourceQPilotStrip (S1992RebasedPaperO D E).object.boundary ∧
      (S1992RebasedPaperO D E).object.boundary.target_q =
        (S1992RebasedPaperO D E).object.boundary.theater.thetaPacket.q :=
  ⟨(S1992RebasedPaperO D E).object.strip_eq_source, rfl⟩

/-- The `(1,0)` label binding of the rebased paper object: `n = 1`,
`m = 0`, and the carrier is exactly the object's actual one-column
structure. -/
theorem S1992RebasedPaperO_label (D : S1895PaperInput)
    (E : S1992RebasedLocalFamily D) :
    (s1895OneColumnLabel PaperV (S1992RebasedPaperO D E).object.oneColumn).n = 1 ∧
      (s1895OneColumnLabel PaperV
        (S1992RebasedPaperO D E).object.oneColumn).m = 0 ∧
      (s1895OneColumnLabel PaperV
          (S1992RebasedPaperO D E).object.oneColumn).carrier =
        (S1992RebasedPaperO D E).object.oneColumn :=
  ⟨rfl, rfl, rfl⟩

/-- **All four paper-level identifications and the anchors hold on the rebased
paper object.** -/
theorem S1992RebasedPaperO_identifications (D : S1895PaperInput)
    (E : S1992RebasedLocalFamily D) :
    (S1992RebasedPaperO D E).object.paper_strip_identification ∧
      (S1992RebasedPaperO D E).object.paper_logKummer_identification ∧
      (S1992RebasedPaperO D E).object.paper_lineBundle_identification ∧
      (S1992RebasedPaperO D E).object.paper_qPilot_log_identification ∧
      ((S1992RebasedPaperO D E).object.strip =
          sourceQPilotStrip (S1992RebasedPaperO D E).object.boundary ∧
        (S1992RebasedPaperO D E).object.boundary.target_q =
          (S1992RebasedPaperO D E).object.boundary.theater.thetaPacket.q) :=
  ⟨S1992RebasedPaperO_paper_strip D E,
    S1992RebasedPaperO_paper_logKummer D E,
    S1992RebasedPaperO_paper_lineBundle D E,
    S1992RebasedPaperO_paper_qPilot D E,
    S1992RebasedPaperO_anchors D E⟩


/-! ## 4. The actual local `O^×` carrier of any compatible strip

Any F-prime-strip linked to `localOFieldStrip` has the actual local
`O^×` value monoid up to the link, the trivial degree, and an action
transported from the actual local Galois action.  Hence no value-monoid content
or degree content can distinguish two compatible local strips. -/

/-- The norm-log degree of a unit of a normed field, evaluated. -/
theorem unitNormLogDegree_eq_ofAdd_norm (K : Type*) [NormedField K] (u : Kˣ) :
    unitNormLogDegree K u = Multiplicative.ofAdd (Real.log ‖(u : K)‖) := rfl

/-- **The actual norm-log degree of the local `O^×` carrier is trivial**:
every integral unit of the algebraic closure has p-adic norm one. -/
theorem localOFieldUnitsDegree_apply_eq_one (p : Nat) [Fact (Nat.Prime p)]
    (u : LocalOFieldUnits p) : localOFieldUnitsDegree p u = 1 := by
  have hsub : ((Units.map
      (Integers (AlgebraicClosure ℚ_[p])).subtype.toMonoidHom u :
      (AlgebraicClosure ℚ_[p])ˣ) : AlgebraicClosure ℚ_[p]) =
      ((u : (Integers (AlgebraicClosure ℚ_[p]))) : AlgebraicClosure ℚ_[p]) := rfl
  rw [localOFieldUnitsDegree, MonoidHom.comp_apply, localUnitNormDegreeFor,
    unitNormLogDegree_eq_ofAdd_norm, hsub,
    LocalFieldIntegralUnits.norm_unit_eq_one u, Real.log_one]
  rfl

/-- The local strip's degree is trivial. -/
theorem localOFieldStrip_degree_apply_eq_one (v : PaperV)
    (x : localOFieldStrip.Mon v) : localOFieldStrip.degree v x = 1 :=
  @localOFieldUnitsDegree_apply_eq_one v.1 ⟨v.prime⟩ x

/-- The value monoid of a strip linked to the local strip is the actual local
`O^×` group, up to the link. -/
theorem linked_mon_equiv (S : FPrimeStrip PaperV)
    (φ : FPrimeStripEquiv localOFieldStrip S) (v : PaperV) :
    Nonempty (localOFieldStrip.Mon v ≃* S.Mon v) :=
  ⟨φ.isoMon v⟩

/-- **A compatible local strip has trivial degree**: the only degree in its
link class is the trivial one. -/
theorem linked_degree_trivial (S : FPrimeStrip PaperV)
    (φ : FPrimeStripEquiv localOFieldStrip S) (v : PaperV) (x : S.Mon v) :
    S.degree v x = 1 := by
  have h := φ.compatDegree v ((φ.isoMon v).symm x)
  rw [MulEquiv.apply_symm_apply] at h
  rw [h, localOFieldStrip_degree_apply_eq_one v]

/-- **A compatible local strip's action is the transport of the actual local
Galois action along the link.** -/
theorem linked_action_form (S : FPrimeStrip PaperV)
    (φ : FPrimeStripEquiv localOFieldStrip S) (v : PaperV)
    (g : S.Pi v) (x : localOFieldStrip.Mon v) :
    S.action v g (φ.isoMon v x) =
      φ.isoMon v (localOFieldStrip.action v ((φ.isoPi v).symm g) x) := by
  have h := φ.compatAction v ((φ.isoPi v).symm g) x
  rw [MulEquiv.apply_symm_apply] at h
  exact h.symm

/-! ## 5. The obstructions inside any rebased family

A Hodge theater is determined by its arithmetic data, its prime-strip and its
theta packet; the family links force the theta `q` — hence the theta
packet — to be common, and `arithmetic_alignment` forces the
arithmetic data to be common.  Therefore the prime-strip map of a rebased family
is injective.  In particular the family cannot be constant on the actual local
strip: it must contain at least two distinct compatible local strips.  And the
S1487/S1527 shear strips cannot be mixed into it at all. -/

/-- In a source Hodge-theater family with a common arithmetic datum, the
prime-strip map is injective. -/
theorem strip_injective_of_common_arithmetic
    {l : PrimeGeFive} {F : SourceHodgeTheaterFamily.{0, 0, 0, 0, 0} l PaperV}
    {A : InitialThetaArithmeticData.{0} l}
    (hA : ∀ i, (F.theater i).arithmetic = A) :
    Function.Injective (fun i => (F.theater i).primeStrip) := by
  intro i j h
  exact F.distinct (hodgeTheater_eq_of_components ((hA i).trans (hA j).symm) h
    (thetaPacket_eq_of_q_eq (F.link_q i j)))

/-- **A family all of whose theaters carry exactly the actual local `O^×`
strip has at most one index.**  (The arithmetic data and the theta packet are
forced, so all theaters coincide.) -/
theorem index_subsingleton_of_constant_local_strip
    (F : SourceHodgeTheaterFamily.{0, 0, 0, 0, 0} D.l PaperV)
    (hA : ∀ i, (F.theater i).arithmetic =
      (S1895PaperInput.I D).initial.arithmetic)
    (hstrip : ∀ i, (F.theater i).primeStrip = localOFieldStrip) :
    Subsingleton F.index := by
  refine ⟨fun i j => ?_⟩
  exact F.distinct (hodgeTheater_eq_of_components ((hA i).trans (hA j).symm)
    ((hstrip i).trans (hstrip j).symm) (thetaPacket_eq_of_q_eq (F.link_q i j)))

/-- In a rebased family the prime-strip map is injective. -/
theorem S1992RebasedLocalFamily.strip_injective (E : S1992RebasedLocalFamily D) :
    Function.Injective (fun i => (E.family.theater i).primeStrip) := by
  intro i j h
  exact E.family.distinct (hodgeTheater_eq_of_components
    ((E.arithmetic_alignment i).trans (E.arithmetic_alignment j).symm) h
    (thetaPacket_eq_of_q_eq (E.family.link_q i j)))

/-- The `(1,0)` member of a rebased family carries the actual local
`O^×` strip (restatement of the datum field). -/
theorem S1992RebasedLocalFamily.core_strip (E : S1992RebasedLocalFamily D) :
    (E.family.theater (E.index_equiv.symm (1, 0))).primeStrip = localOFieldStrip :=
  E.core_eq_local

/-- **Every theater of a rebased family carries a strip compatible with the
actual local `O^×` strip**: the actual family link from the `(1,0)`
member is an `FPrimeStripEquiv` from `localOFieldStrip` to it. -/
theorem S1992RebasedLocalFamily.other_strip_linked (E : S1992RebasedLocalFamily D)
    (i : E.family.index) :
    Nonempty (FPrimeStripEquiv localOFieldStrip
      (E.family.theater i).primeStrip) := by
  have h := (E.family.link (E.index_equiv.symm (1, 0)) i).primeStripEquiv
  rw [E.core_eq_local] at h
  exact ⟨h⟩

/-- **The rebased family cannot be constant on the actual local strip.** -/
theorem S1992RebasedLocalFamily.not_constant_local
    (E : S1992RebasedLocalFamily D) :
    ¬ ∀ i, (E.family.theater i).primeStrip = localOFieldStrip := by
  intro h
  haveI : Subsingleton E.family.index :=
    index_subsingleton_of_constant_local_strip E.family E.arithmetic_alignment h
  have h01 : E.index_equiv.symm (0, 0) = E.index_equiv.symm (1, 0) :=
    Subsingleton.elim _ _
  have h' : ((0, 0) : SourceTheorem311Index) = (1, 0) :=
    E.index_equiv.symm.injective h01
  exact absurd (congrArg Prod.fst h') (by norm_num)

/-- **The rebased family must contain two distinct compatible local strips.** -/
theorem S1992RebasedLocalFamily.exists_distinct_strips
    (E : S1992RebasedLocalFamily D) :
    ∃ i j : E.family.index, i ≠ j ∧
      (E.family.theater i).primeStrip ≠ (E.family.theater j).primeStrip := by
  refine ⟨E.index_equiv.symm (0, 0), E.index_equiv.symm (1, 0), ?_, ?_⟩
  · intro h
    have h' : ((0, 0) : SourceTheorem311Index) = (1, 0) :=
      E.index_equiv.symm.injective h
    exact absurd (congrArg Prod.fst h') (by norm_num)
  · intro h
    have h' : E.index_equiv.symm (0, 0) = E.index_equiv.symm (1, 0) :=
      E.strip_injective h
    have h'' : ((0, 0) : SourceTheorem311Index) = (1, 0) :=
      E.index_equiv.symm.injective h'
    exact absurd (congrArg Prod.fst h'') (by norm_num)

/-- **A rebased family carries infinitely many pairwise distinct compatible
local strips**: the strip map is injective from `Int × Int`. -/
theorem S1992RebasedLocalFamily.infinite_strips (E : S1992RebasedLocalFamily D) :
    Set.Infinite (Set.range (fun i => (E.family.theater i).primeStrip)) := by
  haveI : Infinite E.family.index :=
    Infinite.of_injective E.index_equiv.symm E.index_equiv.symm.injective
  exact Set.infinite_range_of_injective E.strip_injective

/-- The actual local `O^×` strip is not the S1487 shear strip at any
lattice point. -/
theorem no_localOFieldStrip_equiv_shear_strip (n m : Int) :
    ¬ Nonempty (FPrimeStripEquiv localOFieldStrip (S1487Strip n m)) := by
  letI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  rintro ⟨e⟩
  have hM : LocalOFieldUnits 5 ≃* SourceHaarActualValueMonoid := by
    change (localOFieldStrip.Mon s1895FivePlace) ≃*
      ((S1487Strip n m).Mon s1895FivePlace)
    exact e.isoMon s1895FivePlace
  have hU : Nonempty (LocalOFieldUnits 5 ≃*
      (SourceHaarActualValueMonoid)ˣ) :=
    ⟨(groupUnitsEquiv (LocalOFieldUnits 5)).trans (Units.mapEquiv hM)⟩
  exact no_localOFieldUnits_equiv_sourceHaarUnits 5 hU

/-- **No Hodge-theater link can join a local-strip theater to a shear-strip
theater.**  Hence the S1487/S1527 shear family cannot be patched by replacing
its `(1,0)` member: the family has to be rebuilt on the local carrier. -/
theorem no_hodgeTheaterLink_local_shear {l : PrimeGeFive}
    {T U : HodgeTheater.{0, 0, 0, 0} l PaperV} (n m : Int)
    (hT : T.primeStrip = localOFieldStrip) (hU : U.primeStrip = S1487Strip n m) :
    ¬ Nonempty (HodgeTheaterLink T U) := by
  rintro ⟨L⟩
  have h : FPrimeStripEquiv localOFieldStrip (S1487Strip n m) := by
    have hL := L.primeStripEquiv
    rwa [hT, hU] at hL
  exact no_localOFieldStrip_equiv_shear_strip n m ⟨h⟩

/-- The `(1,0)` prime-strip of the S1527/S1487 shear input is the shear
strip, not the actual local `O^×` strip. -/
theorem s1527Input_core_eq_shear {l : PrimeGeFive}
    (S : SourceDefinition31Data.{0} l) :
    (S1487OriginalInput S).fPrimeStripAt 1 0 = S1487Strip 1 0 := rfl

/-- Consequently the shear input has no link from a theater carrying the local
strip, at its `(1,0)`` member. -/
theorem no_link_from_local_to_shear_input
    {l : PrimeGeFive} (S : SourceDefinition31Data.{0} l)
    {T : HodgeTheater.{0, 0, 0, 0} l PaperV}
    (hT : T.primeStrip = localOFieldStrip) :
    ¬ Nonempty (HodgeTheaterLink T
      ((S1487OriginalInput S).theaterAt 1 0)) := by
  have hU : ((S1487OriginalInput S).theaterAt 1 0).primeStrip =
      S1487Strip 1 0 := rfl
  exact no_hodgeTheaterLink_local_shear 1 0 hT hU

/-- The S1895 input is **not** already a rebased input: its `(1,0)` core is
the S1487 shear strip, which is not the actual local `O^×` strip. -/
theorem s1895Input_not_rebased (D : S1895PaperInput) :
    (S1895PaperInput.I D).fPrimeStripAt 1 0 ≠ localOFieldStrip :=
  paperInput_core_ne_local D

/-- The rebased paper object's strip is not the S1895 paper object's strip: the
rebasing genuinely changes the `(1,0)` `F`-prime-strip. -/
theorem S1992RebasedPaperO_strip_ne_s1895 (D : S1895PaperInput)
    (E : S1992RebasedLocalFamily D) :
    (S1992RebasedPaperO D E).object.strip ≠ (S1895PaperO D).strip := by
  intro h
  exact no_localOFieldStrip_equiv_paperO D
    ⟨(S1992RebasedPaperO_strip D E).symm ▸ h ▸
      FPrimeStripEquiv.refl (S1895PaperO D).strip⟩

/-! ## 6. The exact first missing -/

/-- **The exact first missing of the rebased local `O^×` paper input**:
the rebased source Hodge-theater family datum.  Equivalently (section 2) it is
S1978's `S1978RebasedPaperInput`.  No inhabitant is asserted. -/
abbrev S1992FirstMissing (D : S1895PaperInput) := S1992RebasedLocalFamily D

/-- **Any inhabitant of the exact missing type yields S1978's rebased paper
q-pilot object**, with all four paper-level identifications proved. -/
theorem S1992FirstMissing_suffices (D : S1895PaperInput) :
    Nonempty (S1992FirstMissing D) → Nonempty (S1978RebasedPaperO D) :=
  fun ⟨E⟩ => ⟨S1992RebasedPaperO D E⟩

/-- Conversely, the rebased input of an inhabitant of S1978's rebased paper
object is an inhabitant of the exact missing type. -/
theorem S1992FirstMissing_of_rebasedPaperO (D : S1895PaperInput) :
    Nonempty (S1978RebasedPaperO D) → Nonempty (S1992FirstMissing D) :=
  fun ⟨O⟩ => ⟨S1992RebasedLocalFamily.ofRebasedInput O.rebased⟩

/-- The exact missing type is exactly S1978's missing paper object, at the level
of nonempty types. -/
theorem S1992FirstMissing_iff_rebasedPaperO (D : S1895PaperInput) :
    Nonempty (S1992FirstMissing D) ↔ Nonempty (S1978RebasedPaperO D) :=
  ⟨S1992FirstMissing_suffices D, S1992FirstMissing_of_rebasedPaperO D⟩

/-- **What the exact missing datum still has to supply**: by
`exists_distinct_strips` it cannot be constant on the actual local strip;
it must produce at least two distinct compatible local strips, each of which by
section 4 has the actual local `O^×` value monoid and the trivial degree. -/
theorem S1992FirstMissing_requires_distinct_strips
    (D : S1895PaperInput) : ∀ E : S1992FirstMissing D,
    ∃ i j : E.family.index, i ≠ j ∧
      (E.family.theater i).primeStrip ≠ (E.family.theater j).primeStrip :=
  fun E => E.exists_distinct_strips

/-! ## 7. Axiom probes -/

#print axioms thetaPacket_eq_of_q_eq
#print axioms hodgeTheater_eq_of_components
#print axioms S1992RebasedLocalFamily.toRebasedInput
#print axioms S1992RebasedLocalFamily.nonempty_iff_rebasedPaperInput
#print axioms S1992RebasedPaperObject
#print axioms S1992RebasedPaperO
#print axioms S1992RebasedPaperO_strip
#print axioms S1992RebasedPaperO_initial
#print axioms S1992RebasedPaperO_paper_strip
#print axioms S1992RebasedPaperO_paper_logKummer
#print axioms S1992RebasedPaperO_paper_lineBundle
#print axioms S1992RebasedPaperO_paper_qPilot
#print axioms S1992RebasedPaperO_anchors
#print axioms S1992RebasedPaperO_label
#print axioms S1992RebasedPaperO_identifications
#print axioms localOFieldUnitsDegree_apply_eq_one
#print axioms localOFieldStrip_degree_apply_eq_one
#print axioms linked_degree_trivial
#print axioms linked_action_form
#print axioms strip_injective_of_common_arithmetic
#print axioms index_subsingleton_of_constant_local_strip
#print axioms S1992RebasedLocalFamily.strip_injective
#print axioms S1992RebasedLocalFamily.not_constant_local
#print axioms S1992RebasedLocalFamily.exists_distinct_strips
#print axioms no_localOFieldStrip_equiv_shear_strip
#print axioms no_hodgeTheaterLink_local_shear
#print axioms s1527Input_core_eq_shear
#print axioms no_link_from_local_to_shear_input
#print axioms S1992FirstMissing_suffices
#print axioms S1992FirstMissing_of_rebasedPaperO
#print axioms S1992FirstMissing_iff_rebasedPaperO
#print axioms S1992RebasedLocalFamily.core_strip
#print axioms S1992RebasedLocalFamily.other_strip_linked
#print axioms linked_mon_equiv
#print axioms s1895Input_not_rebased
#print axioms S1992RebasedPaperO_strip_ne_s1895
#print axioms S1992RebasedLocalFamily.infinite_strips

end LeanFormal.IUT.XiFPaper.S1992RebasedLocalInputActual
