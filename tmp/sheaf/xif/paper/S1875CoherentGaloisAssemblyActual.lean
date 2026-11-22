/-
# S1875: assembly of the coherent-cover PreGalois/Galois category at the
  target hom universe, and the exact missing

## Inputs available in the tree

* S1854 constructs the actual coherent category
  `S1854CoherentCategory01 : Category.{0,1} CoherentCover` (homs are the S1766
  Type-0 small carriers of the underlying covers), the forgetful functor to
  S1809's actual `Category.{0,1}` on covers, full and faithful, and the
  terminal coherent cover `S1854HasTerminal01 : HasTerminal CoherentCover`.
* S1857 proves, at this same target universe, pullbacks and finite coproducts
  from S1856's first-missing inputs:
  `S1857HasPullbacks01_of_firstMissing : S1856PullbackFirstMissing →
  HasPullbacks C01` and
  `S1857HasFiniteCoproducts01_of_firstMissing : S1856CoproductFirstMissing →
  HasFiniteCoproducts C01`.  The geometric inputs themselves are
  `S1856PullbackFirstMissing` and `S1856CoproductFirstMissing`.
* S1868 (`S1868CoherentFiberActual.lean`, compiled in this session) supplies,
  at the target universe `S1854CoherentCategory01`:
  - `S1868PreGaloisCategory01 (hE) : PreGaloisCategory CoherentCover`, the
    five fields transported from S1830's unconditional pre-Galois structure
    on `(FiniteEtale R')'op` along the coherent affine equivalence;
  - `S1868Fiber01 : CoherentCover ⥤ FintypeCat.{0}`, the Omega-fibre functor;
  - `S1868FiberFunctor01 (hE) (hIso)`, its six-field structure;
  where `hE : S1868CoherentAlgebraFunctor.IsEquivalence` and
  `hIso : S1835BCReflectsIsos` (S1855's field 6).
  S1868 also proves `S1868Full_proof : S1868Full` unconditionally (via
  S1878's coherent affine fullness), hence
  `S1868FirstMissing_iff_essSurj : S1868FirstMissing ↔ S1868EssSurj`; the
  sharp remaining statement is `S1868EssSurj`, essential surjectivity of the
  coherent affine comparison.
* S1867 (`S1867CoherentQuotientsActual.lean`) supplies only a generic
  transport skeleton: `S1867HasColimitsOfShape_of_apex` produces colimits at
  `S1854CoherentCategory11` from ambient colimits *whose coherent apexes are
  given*.  The apex-coherence input is not discharged and there is no
  `Category.{0,1}` version, so S1867 does not supply the two PreGalois fields.

## What is assembled

The main result is the actual `GaloisCategory` at `S1854CoherentCategory01`:

  `S1875GaloisCategory (h : S1868FirstMissing) (hIso : S1835BCReflectsIsos) :
    @GaloisCategory.{1,0} CoherentCover S1854CoherentCategory01`,

built from S1868's transported PreGalois structure and fibre functor.
`S1875CoherentGaloisInputs` bundles the two named inputs and
`S1875GaloisCategory_of_inputs` is the same result from the bundle.  The
five-field intermediate is `S1875PreGaloisCategory_of_S1868FirstMissing`, and
`S1875PreGaloisMissing_of_S1868FirstMissing` records that this route obtains
the two fields that the direct S1854/S1857 route leaves open.  The reduced form
`S1875GaloisCategory_of_essSurj (h : S1868EssSurj)
(hIso : S1835BCReflectsIsos)` is the same assembly from the sharp input
`S1868EssSurj`; `S1875CoherentGaloisInputsEssSurj` bundles it, and
`S1875GaloisCategory_of_inputsEssSurj` unpacks the bundle.

The direct route is also recorded, with its exact missing:

* `S1875PreGaloisCategory_iff` (given the S1856 limit inputs):
    PreGaloisCategory C01  ↔  Nonempty S1875PreGaloisMissing,
  where `S1875PreGaloisMissing` is exactly the two remaining Mathlib fields
  (quotients by finite groups; mono/direct-summand);
* `S1875GaloisCategory_iff`: GaloisCategory C01 ↔ S1875FiberFunctorStatement P
  for a fixed PreGalois structure P, and `S1875GaloisCategory_iff_missing`
  bundles the two.

## What is constructed

* `S1875LimitInputs`: the S1856 limit inputs as one structure;
* `S1875HasTerminal`, `S1875HasPullbacks`, `S1875HasFiniteCoproducts`: the
  three available fields of `PreGaloisCategory` at C01;
* `S1875PreGaloisCategory_of_missing`: the actual five-field
  `PreGaloisCategory` at C01, from the limit inputs and the two missing
  fields;
* `S1875GaloisCategory_of_missing`: the actual `GaloisCategory` at C01 from a
  fibre-functor statement;
* the first-missing forms `S1875PreGaloisCategory_of_firstMissing` and
  `S1875GaloisCategory_of_firstMissing`, which consume S1856's named first
  missing inputs directly;
* the S1868-based assembly: `S1875PreGaloisCategory_of_coherentAffineEquiv`,
  `S1875PreGaloisCategory_of_S1868FirstMissing`,
  `S1875PreGaloisMissing_of_S1868FirstMissing`,
  `S1875GaloisCategory_of_coherentAffineEquiv`, `S1875GaloisCategory`, and
  `S1875GaloisCategory_of_inputs`, together with the reduced forms
  `S1875PreGaloisCategory_of_essSurj`, `S1875PreGaloisMissing_of_essSurj`,
  `S1875GaloisCategory_of_essSurj` and
  `S1875GaloisCategory_of_inputsEssSurj`;
* two genuine fragments of the missing fields, proved for C01:
  - `S1875TrivialActionHasColimit`: every constant action of a finite group
    has a colimit (the trivial-action fragment of (G2));
  - `S1875MonoDirectSummand_of_initial`: a mono whose domain is initial is the
    first leg of a binary coproduct (the initial-domain fragment of (G3)).

  These are fragments only; the general fields are not proved on the direct
  route, though the S1868 route obtains them under its two named inputs.

## Honest boundary

No sorry, admit, new axiom, fake category, fake limit or fake fibre functor.
The S1868-based `GaloisCategory` is conditional on exactly `S1868EssSurj`
(essential surjectivity of S1868's coherent affine comparison; fullness is
unconditional, `S1868Full_proof`) and `S1835BCReflectsIsos` (S1855's field
6); neither is assumed.  The direct-route theorems are conditional on the S1856 limit data
and the two named fields.  The two fragments are not the general fields.
Only propext, Classical.choice and Quot.sound occur; see the audit block.
-/

import tmp.sheaf.xif.paper.S1857CoherentLimits01Actual
import tmp.sheaf.xif.paper.S1868CoherentFiberActual
import Mathlib.CategoryTheory.Galois.Basic

noncomputable section

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 2000000

namespace LeanFormal.IUT.XiFPaper.S1875CoherentGaloisAssemblyActual

open CategoryTheory
open CategoryTheory.Limits
open LeanFormal.IUT.XiFPaper.S1728CoverCategoryActual
open LeanFormal.IUT.XiFPaper.S1728CoverCategoryActual.S1728Paper
open LeanFormal.IUT.XiFPaper.S1852CoherentCoverActual
open LeanFormal.IUT.XiFPaper.S1854CoherentCategoryActual
open LeanFormal.IUT.XiFPaper.S1856CoherentLimitsActual
open LeanFormal.IUT.XiFPaper.S1857CoherentLimits01Actual
open LeanFormal.IUT.XiFPaper.S1868CoherentFiberActual
open LeanFormal.IUT.XiFPaper.S1835FiberRPrimeActual
open LeanFormal.IUT.XiFPaper.S1830G2G3RPrimeActual

attribute [local instance] S1854CoherentCategory01

/-! ## 1. The S1856 limit inputs, bundled -/

/-- The two S1856 first-missing data in the shape consumed by S1857: a chosen
S1728 pullback structure with its apex coherence, and a chosen S1728 initial
object and binary-coproduct structure with their apex coherence.  This is a
bundle of the hypotheses, not a new geometric assumption. -/
structure S1875LimitInputs where
  /-- The chosen pullback structure on the S1728 cover category. -/
  hasPullbacks : Limits.HasPullbacks S1728Cover
  /-- Pullback-apex coherence for that structure (S1854's condition). -/
  pullbackApex : S1854PullbackApexCoherent hasPullbacks
  /-- The chosen initial object on the S1728 cover category. -/
  hasInitial : Limits.HasInitial S1728Cover
  /-- The chosen binary-coproduct structure on the S1728 cover category. -/
  hasBinaryCoproducts : Limits.HasBinaryCoproducts S1728Cover
  /-- Coproduct-apex coherence for those structures (S1854's condition). -/
  coproductApex : S1854CoproductApexCoherent hasInitial hasBinaryCoproducts

/-! ## 2. The three available fields at the target universe

These are literal fields of `PreGaloisCategory` at
`S1854CoherentCategory01`, quoted from S1854 and S1857.  Nothing is
reconstructed. -/

/-- The coherent category has a terminal object (S1854, transported from
S1762's terminal cover).  This field is unconditional. -/
theorem S1875HasTerminal : Limits.HasTerminal CoherentCover :=
  S1854HasTerminal01

/-- The coherent category has pullbacks, from the S1856 limit inputs
(S1857's transport to `Category.{0,1}`). -/
theorem S1875HasPullbacks (L : S1875LimitInputs) :
    @Limits.HasPullbacks CoherentCover S1854CoherentCategory01 :=
  S1857HasPullbacks01 L.hasPullbacks L.pullbackApex

/-- The coherent category has finite coproducts, from the S1856 limit inputs
(S1857's transport to `Category.{0,1}`). -/
theorem S1875HasFiniteCoproducts (L : S1875LimitInputs) :
    @Limits.HasFiniteCoproducts CoherentCover S1854CoherentCategory01 :=
  S1857HasFiniteCoproducts01 L.hasInitial L.hasBinaryCoproducts L.coproductApex

/-! ## 3. The exact missing fields and the fibre-functor statement -/

/-- (G2) at the target universe, written exactly as the Mathlib field: every
action of a finite group `G` on the coherent category has a colimit.  This is
not proved here; it is the first component of the missing data. -/
def S1875QuotientsByFiniteGroups : Prop :=
  ∀ (G : Type) [Group G] [Finite G],
    Limits.HasColimitsOfShape (SingleObj G) CoherentCover

/-- (G3) at the target universe, written exactly as the Mathlib field: every
monomorphism is the first leg of a binary coproduct.  This is not proved here;
it is the second component of the missing data. -/
def S1875MonoDirectSummand : Prop :=
  ∀ {X Y : CoherentCover} (i : X ⟶ Y) [Mono i],
    ∃ (Z : CoherentCover) (u : Z ⟶ Y), Nonempty (IsColimit (BinaryCofan.mk i u))

/-- The exact missing data for `PreGaloisCategory` at `S1854CoherentCategory01`:
the two fields not supplied by S1854/S1857. -/
structure S1875PreGaloisMissing where
  /-- (G2): quotients by finite groups. -/
  quotients : S1875QuotientsByFiniteGroups
  /-- (G3): mono induces an isomorphism on a direct summand. -/
  mono : S1875MonoDirectSummand

/-- The exact missing data for `GaloisCategory`: a fibre functor to
`FintypeCat.{0}` with its six structure fields (`PreGaloisCategory.FiberFunctor`).
The PreGalois structure is an explicit argument so that the statement does not
silently depend on a global instance. -/
def S1875FiberFunctorStatement
    (P : @PreGaloisCategory.{1,0} CoherentCover S1854CoherentCategory01) : Prop :=
  ∃ F : CoherentCover ⥤ FintypeCat.{0},
    Nonempty (@PreGaloisCategory.FiberFunctor CoherentCover S1854CoherentCategory01 P F)

/-! ## 4. Two proved fragments of the missing fields

These are genuine theorems about the actual `Category.{0,1}` structure, but
they cover only the trivial action and the initial domain; they do not give the
general fields and are not used as if they did. -/

/-- Fragment of (G2): the constant action of a finite group on a coherent
cover (the trivial action) has a colimit, namely the object itself.  This is
the trivial-action case only. -/
theorem S1875TrivialActionHasColimit (G : Type) [Group G] (A : CoherentCover) :
    Limits.HasColimit ((Functor.const (SingleObj G)).obj A) := by
  let c : Cocone ((Functor.const (SingleObj G)).obj A) :=
    { pt := A
      ι := 𝟙 _ }
  refine ⟨c, ?_⟩
  refine
    { desc := fun s => s.ι.app (SingleObj.star G)
      fac := ?_
      uniq := ?_ }
  · intro s j
    have hj : j = SingleObj.star G := Quiver.SingleObj.ext
    subst hj
    exact Category.id_comp _
  · intro s m hm
    exact (Category.id_comp m).symm.trans (hm (SingleObj.star G))

/-- Fragment of (G3): if the domain of a mono is initial, then the mono is the
first leg of a binary coproduct, with complement the codomain and second leg
the identity.  This is the initial-domain case only. -/
theorem S1875MonoDirectSummand_of_initial {X Y : CoherentCover}
    (hX : Limits.IsInitial X) (i : X ⟶ Y) [Mono i] :
    ∃ (Z : CoherentCover) (u : Z ⟶ Y), Nonempty (IsColimit (BinaryCofan.mk i u)) := by
  refine ⟨Y, 𝟙 Y, ⟨?_⟩⟩
  refine BinaryCofan.IsColimit.mk (s := BinaryCofan.mk i (𝟙 Y))
    (fun {T} f g => g) ?_ ?_ ?_
  · intro T f g
    rw [BinaryCofan.mk_inl]
    exact IsInitial.hom_ext hX (i ≫ g) f
  · intro T f g
    rw [BinaryCofan.mk_inr]
    exact Category.id_comp g
  · intro T f g m hm1 hm2
    rw [BinaryCofan.mk_inr] at hm2
    have hm2' : (𝟙 Y) ≫ (show Y ⟶ T from m) = g := hm2
    change (show Y ⟶ T from m) = g
    simpa using hm2'

/-! ## 5. Assembly of `PreGaloisCategory` at the target universe -/

/-- **The five-field `PreGaloisCategory` at `S1854CoherentCategory01`**, from
the S1856 limit inputs and exactly the two missing fields.  The three other
fields are S1854's terminal object and S1857's pullbacks and finite
coproducts; nothing is fabricated. -/
theorem S1875PreGaloisCategory_of_missing (L : S1875LimitInputs)
    (m : S1875PreGaloisMissing) :
    @PreGaloisCategory.{1,0} CoherentCover S1854CoherentCategory01 where
  hasTerminal := S1854HasTerminal01
  hasPullbacks := S1857HasPullbacks01 L.hasPullbacks L.pullbackApex
  hasFiniteCoproducts :=
    S1857HasFiniteCoproducts01 L.hasInitial L.hasBinaryCoproducts L.coproductApex
  hasQuotientsByFiniteGroups := m.quotients
  monoInducesIsoOnDirectSummand := fun {X Y} (i : X ⟶ Y) [Mono i] => m.mono i

/-- The exact missing data for `GaloisCategory` at `C01`: the PreGalois
missing fields together with a fibre functor for the resulting PreGalois
structure. -/
def S1875GaloisMissing (L : S1875LimitInputs) : Prop :=
  ∃ (m : S1875PreGaloisMissing),
    S1875FiberFunctorStatement (S1875PreGaloisCategory_of_missing L m)

/-- Extract the two missing fields from a `PreGaloisCategory` instance at C01. -/
theorem S1875PreGaloisMissing_of_instance
    (P : @PreGaloisCategory.{1,0} CoherentCover S1854CoherentCategory01) :
    S1875PreGaloisMissing where
  quotients := fun (G : Type) (hG : Group G) (hF : Finite G) =>
    @PreGaloisCategory.hasQuotientsByFiniteGroups CoherentCover
      S1854CoherentCategory01 P G hG hF
  mono := fun {X Y} (i : X ⟶ Y) (hi : Mono i) =>
    @PreGaloisCategory.monoInducesIsoOnDirectSummand CoherentCover
      S1854CoherentCategory01 P X Y i hi

/-- **The exact missing for `PreGaloisCategory` at C01**, given the S1856
limit inputs: the class holds if and only if the two named fields hold.  The
forward direction extracts the Mathlib fields, the backward direction is
`S1875PreGaloisCategory_of_missing`. -/
theorem S1875PreGaloisCategory_iff (L : S1875LimitInputs) :
    @PreGaloisCategory.{1,0} CoherentCover S1854CoherentCategory01 ↔
      Nonempty S1875PreGaloisMissing := by
  constructor
  · intro P
    exact ⟨S1875PreGaloisMissing_of_instance P⟩
  · rintro ⟨m⟩
    exact S1875PreGaloisCategory_of_missing L m

/-- The available fields of `PreGaloisCategory`, summarized. -/
theorem S1875PreGaloisAvailable (L : S1875LimitInputs) :
    Limits.HasTerminal CoherentCover ∧
      @Limits.HasPullbacks CoherentCover S1854CoherentCategory01 ∧
      @Limits.HasFiniteCoproducts CoherentCover S1854CoherentCategory01 :=
  ⟨S1875HasTerminal, S1875HasPullbacks L, S1875HasFiniteCoproducts L⟩

/-! ## 6. Assembly of `GaloisCategory` at the target universe -/

/-- **The `GaloisCategory` structure at `S1854CoherentCategory01`**, from the
PreGalois missing fields and the fibre-functor statement.  The fibre functor is
an explicit hypothesis; it is not constructed here. -/
theorem S1875GaloisCategory_of_missing (L : S1875LimitInputs)
    (m : S1875PreGaloisMissing)
    (hF : S1875FiberFunctorStatement (S1875PreGaloisCategory_of_missing L m)) :
    @GaloisCategory.{1,0} CoherentCover S1854CoherentCategory01 := by
  letI := S1875PreGaloisCategory_of_missing L m
  exact GaloisCategory.mk hF

/-- **The exact missing for `GaloisCategory` at C01** for a fixed PreGalois
structure: the Galois class holds if and only if a fibre functor with its six
fields exists. -/
theorem S1875GaloisCategory_iff (L : S1875LimitInputs)
    (P : @PreGaloisCategory.{1,0} CoherentCover S1854CoherentCategory01) :
    @GaloisCategory.{1,0} CoherentCover S1854CoherentCategory01 ↔
      S1875FiberFunctorStatement P := by
  constructor
  · intro g
    have h : P = g.toPreGaloisCategory := Subsingleton.elim _ _
    rw [h]
    exact g.hasFiberFunctor
  · intro hF
    letI := P
    exact GaloisCategory.mk hF

/-- **The exact missing for `GaloisCategory` at C01**, with both the PreGalois
fields and the fibre functor inside one predicate. -/
theorem S1875GaloisCategory_iff_missing (L : S1875LimitInputs) :
    @GaloisCategory.{1,0} CoherentCover S1854CoherentCategory01 ↔
      S1875GaloisMissing L := by
  constructor
  · intro g
    obtain ⟨m⟩ := (S1875PreGaloisCategory_iff L).mp g.toPreGaloisCategory
    refine ⟨m, ?_⟩
    have h : S1875PreGaloisCategory_of_missing L m = g.toPreGaloisCategory :=
      Subsingleton.elim _ _
    rw [h]
    exact g.hasFiberFunctor
  · rintro ⟨m, hF⟩
    exact S1875GaloisCategory_of_missing L m hF

/-! ## 7. The forms consuming S1856's named first missing directly -/

/-- Pullbacks at C01 from S1856's named first missing. -/
theorem S1875HasPullbacks_of_firstMissing
    (hP : S1856PullbackFirstMissing) :
    @Limits.HasPullbacks CoherentCover S1854CoherentCategory01 :=
  S1857HasPullbacks01_of_firstMissing hP

/-- Finite coproducts at C01 from S1856's named first missing. -/
theorem S1875HasFiniteCoproducts_of_firstMissing
    (hC : S1856CoproductFirstMissing) :
    @Limits.HasFiniteCoproducts CoherentCover S1854CoherentCategory01 :=
  S1857HasFiniteCoproducts01_of_firstMissing hC

/-- **PreGaloisCategory at C01 from S1856's first missing and the two missing
fields.**  This is the reduction a consumer should cite: the geometric inputs
are S1856's `S1856PullbackFirstMissing` and `S1856CoproductFirstMissing`, and
the categorical fields left over are exactly `S1875PreGaloisMissing`. -/
theorem S1875PreGaloisCategory_of_firstMissing
    (hP : S1856PullbackFirstMissing) (hC : S1856CoproductFirstMissing)
    (m : S1875PreGaloisMissing) :
    @PreGaloisCategory.{1,0} CoherentCover S1854CoherentCategory01 where
  hasTerminal := S1854HasTerminal01
  hasPullbacks := S1875HasPullbacks_of_firstMissing hP
  hasFiniteCoproducts := S1875HasFiniteCoproducts_of_firstMissing hC
  hasQuotientsByFiniteGroups := m.quotients
  monoInducesIsoOnDirectSummand := fun {X Y} (i : X ⟶ Y) [Mono i] => m.mono i

/-- **GaloisCategory at C01 from S1856's first missing, the two missing fields
and a fibre functor.** -/
theorem S1875GaloisCategory_of_firstMissing
    (hP : S1856PullbackFirstMissing) (hC : S1856CoproductFirstMissing)
    (m : S1875PreGaloisMissing)
    (hF : S1875FiberFunctorStatement
      (S1875PreGaloisCategory_of_firstMissing hP hC m)) :
    @GaloisCategory.{1,0} CoherentCover S1854CoherentCategory01 := by
  letI := S1875PreGaloisCategory_of_firstMissing hP hC m
  exact GaloisCategory.mk hF

/-! ## 8. The assembled Galois category at the target universe (S1868 route) -/

section S1868Assembly

attribute [local instance] S1854CoherentCategory11
attribute [local instance] S1854CoherentCategory01
attribute [local instance] S1830Main.S1830PreGaloisCategory

/-- **The five-field `PreGaloisCategory` at `S1854CoherentCategory01`**,
transported by S1868 from S1830's unconditional pre-Galois structure on
`(FiniteEtale R')'op` along the coherent affine equivalence. -/
theorem S1875PreGaloisCategory_of_coherentAffineEquiv
    (hE : S1868CoherentAlgebraFunctor.IsEquivalence) :
    @PreGaloisCategory.{1,0} CoherentCover S1854CoherentCategory01 :=
  S1868PreGaloisCategory01 hE

/-- The same five-field structure from S1868's named first missing
`S1868FirstMissing`. -/
theorem S1875PreGaloisCategory_of_S1868FirstMissing
    (h : S1868FirstMissing) :
    @PreGaloisCategory.{1,0} CoherentCover S1854CoherentCategory01 :=
  S1868PreGaloisCategory01 (S1868FirstMissing_iff_equivalence.mp h)

/-- **The two fields left open by the direct S1854/S1857 route are obtained**
from the S1868 route: under S1868's coherent affine equivalence, the
coherent category has quotients by finite groups and mono/direct-summand. -/
theorem S1875PreGaloisMissing_of_S1868FirstMissing
    (h : S1868FirstMissing) : S1875PreGaloisMissing :=
  S1875PreGaloisMissing_of_instance
    (S1875PreGaloisCategory_of_S1868FirstMissing h)

/-- **The actual `GaloisCategory` at `S1854CoherentCategory01`**, from the
coherent affine equivalence and S1855's field 6.  The fibre functor is
S1868's Omega-fibre functor with its six fields. -/
theorem S1875GaloisCategory_of_coherentAffineEquiv
    (hE : S1868CoherentAlgebraFunctor.IsEquivalence)
    (hIso : S1835BCReflectsIsos) :
    @GaloisCategory.{1,0} CoherentCover S1854CoherentCategory01 := by
  letI : @PreGaloisCategory.{1,0} CoherentCover S1854CoherentCategory01 :=
    S1868PreGaloisCategory01 hE
  exact GaloisCategory.mk ⟨S1868Fiber01, ⟨S1868FiberFunctor01 hE hIso⟩⟩

/-- The exact inputs of the S1868 assembly: the coherent affine equivalence
and S1855's field 6. -/
def S1875CoherentGaloisInputs : Prop :=
  S1868FirstMissing ∧ S1835BCReflectsIsos

/-- **The assembled `GaloisCategory` from the exact input bundle.** -/
theorem S1875GaloisCategory_of_inputs (h : S1875CoherentGaloisInputs) :
    @GaloisCategory.{1,0} CoherentCover S1854CoherentCategory01 :=
  S1875GaloisCategory_of_coherentAffineEquiv
    (S1868FirstMissing_iff_equivalence.mp h.1) h.2

/-- **The assembled `GaloisCategory` at the target universe**, from S1868's
named first missing and S1855's field 6.  This is the main theorem of the
file: an actual Mathlib `GaloisCategory` at `Category.{0,1}` on the coherent
covers, conditional exactly on the two named inputs. -/
theorem S1875GaloisCategory
    (h : S1868FirstMissing) (hIso : S1835BCReflectsIsos) :
    @GaloisCategory.{1,0} CoherentCover S1854CoherentCategory01 :=
  S1875GaloisCategory_of_coherentAffineEquiv
    (S1868FirstMissing_iff_equivalence.mp h) hIso

/-- The five-field structure from S1868's reduced first missing: essential
surjectivity alone, since fullness is `S1868Full_proof`. -/
theorem S1875PreGaloisCategory_of_essSurj
    (h : S1868EssSurj) :
    @PreGaloisCategory.{1,0} CoherentCover S1854CoherentCategory01 :=
  S1868PreGaloisCategory01
    (S1868FirstMissing_iff_equivalence.mp (S1868FirstMissing_iff_essSurj.mpr h))

/-- The two direct-route fields from the reduced input `S1868EssSurj`. -/
theorem S1875PreGaloisMissing_of_essSurj (h : S1868EssSurj) :
    S1875PreGaloisMissing :=
  S1875PreGaloisMissing_of_instance (S1875PreGaloisCategory_of_essSurj h)

/-- The exact reduced input bundle: essential surjectivity of the coherent
affine comparison and S1855's field 6. -/
def S1875CoherentGaloisInputsEssSurj : Prop :=
  S1868EssSurj ∧ S1835BCReflectsIsos

/-- **The assembled `GaloisCategory` at the target universe in reduced form**,
from S1868's essential-surjectivity statement and S1855's field 6. -/
theorem S1875GaloisCategory_of_essSurj
    (h : S1868EssSurj) (hIso : S1835BCReflectsIsos) :
    @GaloisCategory.{1,0} CoherentCover S1854CoherentCategory01 :=
  S1875GaloisCategory_of_coherentAffineEquiv
    (S1868FirstMissing_iff_equivalence.mp (S1868FirstMissing_iff_essSurj.mpr h)) hIso

/-- The same assembled `GaloisCategory` from the reduced input bundle. -/
theorem S1875GaloisCategory_of_inputsEssSurj
    (h : S1875CoherentGaloisInputsEssSurj) :
    @GaloisCategory.{1,0} CoherentCover S1854CoherentCategory01 :=
  S1875GaloisCategory_of_essSurj h.1 h.2

end S1868Assembly

/-! ## 9. What would complete the assembly

The S1868 route reduces the whole assembly to two named inputs, neither proved
in the tree:

1. `S1868EssSurj` (S1868): essential surjectivity of the coherent affine
   comparison.  Fullness is unconditional (`S1868Full_proof`), and
   `S1868FirstMissing_iff_essSurj` reduces `S1868FirstMissing` to this;
2. `S1835BCReflectsIsos` (S1855's field 6).

Their conjunction is `S1875CoherentGaloisInputsEssSurj`, and
`S1875GaloisCategory_of_inputsEssSurj` produces the actual `GaloisCategory`
from it (`S1875CoherentGaloisInputs` and `S1875GaloisCategory_of_inputs` are
the same bundle stated with `S1868FirstMissing`).

On the direct S1854/S1857 route, the remaining inputs are the S1856 limit data
(`S1856PullbackFirstMissing`, `S1856CoproductFirstMissing`) together with the
two fields `S1875PreGaloisMissing`; S1867 supplies only the generic
apex-coherence transport `S1867HasColimitsOfShape_of_apex`, not those fields.
Given the limit data and the two fields, `S1875PreGaloisCategory_of_firstMissing`
produces `PreGaloisCategory`, and `S1875GaloisCategory_of_firstMissing` adds a
fibre functor.  The equivalences `S1875PreGaloisCategory_iff`,
`S1875GaloisCategory_iff` and `S1875GaloisCategory_iff_missing` certify that
these are exactly the remaining fields. -/

/-! ## 10. Checks and axiom audit -/

#check S1875LimitInputs
#check S1875HasTerminal
#check S1875HasPullbacks
#check S1875HasFiniteCoproducts
#check S1875QuotientsByFiniteGroups
#check S1875MonoDirectSummand
#check S1875PreGaloisMissing
#check S1875FiberFunctorStatement
#check S1875GaloisMissing
#check S1875TrivialActionHasColimit
#check S1875MonoDirectSummand_of_initial
#check S1875PreGaloisCategory_of_missing
#check S1875PreGaloisMissing_of_instance
#check S1875PreGaloisCategory_iff
#check S1875PreGaloisAvailable
#check S1875GaloisCategory_of_missing
#check S1875GaloisCategory_iff
#check S1875GaloisCategory_iff_missing
#check S1875HasPullbacks_of_firstMissing
#check S1875HasFiniteCoproducts_of_firstMissing
#check S1875PreGaloisCategory_of_firstMissing
#check S1875GaloisCategory_of_firstMissing
#check S1875PreGaloisCategory_of_coherentAffineEquiv
#check S1875PreGaloisCategory_of_S1868FirstMissing
#check S1875PreGaloisMissing_of_S1868FirstMissing
#check S1875GaloisCategory_of_coherentAffineEquiv
#check S1875CoherentGaloisInputs
#check S1875GaloisCategory_of_inputs
#check S1875GaloisCategory
#check S1875PreGaloisCategory_of_essSurj
#check S1875PreGaloisMissing_of_essSurj
#check S1875CoherentGaloisInputsEssSurj
#check S1875GaloisCategory_of_essSurj
#check S1875GaloisCategory_of_inputsEssSurj

#print axioms S1875TrivialActionHasColimit
#print axioms S1875MonoDirectSummand_of_initial
#print axioms S1875PreGaloisCategory_of_missing
#print axioms S1875PreGaloisCategory_iff
#print axioms S1875PreGaloisAvailable
#print axioms S1875GaloisCategory_of_missing
#print axioms S1875GaloisCategory_iff
#print axioms S1875GaloisCategory_iff_missing
#print axioms S1875PreGaloisCategory_of_firstMissing
#print axioms S1875GaloisCategory_of_firstMissing
#print axioms S1875PreGaloisCategory_of_coherentAffineEquiv
#print axioms S1875PreGaloisCategory_of_S1868FirstMissing
#print axioms S1875PreGaloisMissing_of_S1868FirstMissing
#print axioms S1875GaloisCategory_of_coherentAffineEquiv
#print axioms S1875GaloisCategory_of_inputs
#print axioms S1875GaloisCategory
#print axioms S1875PreGaloisCategory_of_essSurj
#print axioms S1875PreGaloisMissing_of_essSurj
#print axioms S1875GaloisCategory_of_essSurj
#print axioms S1875GaloisCategory_of_inputsEssSurj

end LeanFormal.IUT.XiFPaper.S1875CoherentGaloisAssemblyActual
