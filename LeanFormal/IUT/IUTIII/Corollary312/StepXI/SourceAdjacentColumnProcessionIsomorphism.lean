import LeanFormal.IUT.IUTIII.Theorem311.SourceMultiradialTwoActionEquivalence

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

/-!
# Adjacent-column procession isomorphism (reduced interface and supply card)

Reduced source-level interface of the procession isomorphisms of the
Theta-link neighbourhood of IUT III, Theorem 3.11, (i) -- "functorial with
respect to isomorphisms of processions of D-prime-strips" -- specialized to
the adjacent-column object needed by the APT transport supply
(`IUT-III.source-APT-transport-supply`, `StepXI/APT.lean`) at the two
north-wall assembly sites (`ContractSourceReduction.lean:212-213`,
`:270-271`).

## Original (paper) route

* IUT III, Theorem 3.11, (i): the collection `n,RLGP` is constructed "via an
  algorithm in the procession that is functorial with respect to
  isomorphisms of processions of D-prime-strips" (pagewise `:9434-9436`);
  see the API-4 header (`SourceMultiradialTwoActionEquivalence.lean`) for the
  quote range and for reduction R1 (the paper's `Prc(n,D_T)` is a sequence
  of systems of poly-isomorphic transition data).
* IUT III, Remark 3.11.1, (iv) (pagewise `:9923-9946`): the SHE property of
  (iii) is "a sort of 'parallel transport' mechanism for the Theta-pilot
  object ..., up to certain mild indeterminacies, from the [arithmetic
  holomorphic structure ... in the] domain of the Theta-link to the
  [arithmetic holomorphic structure ... in the] codomain of the Theta-link";
  the bullet "(Algorithmic parallel transport (APT))" (`:9931-9938`) states
  that this transport is not a set-theoretic function applied to a region
  but a construction algorithm valid on both sides; the bullet "(Hidden
  internal structures (HIS))" (`:9947-9958`) states that the theta-function
  and theta-value internals of the algorithm may be regarded as hidden
  internal structures, irrelevant to the end user of the algorithm.
* Corollary 3.12, Step (xi-b)/(xi-c); obligation `IUT-III.APT`
  (`Corollary312/Obligations.lean:19-24`); DSH-F report section API-2
  (`tmp/dsh-card-ipl-she-apt-20261016/REPORT.md:515-519`): the required API
  is `SourceProcessionIsomorphism n n'` (carrying stage/inclusion
  compatibility), `adjacentColumnIso n : SourceProcessionIsomorphism n
  (n+1)`, and functoriality of the multiradial algorithm along the
  procession.

## Reduced route and deviations

The object frozen here is the reduced source anchor
`SourceProcessionIsomorphism I n n'`: a level equivalence of the Int-indexed
columns of source prime-strips, transition-compatible components against the
family link system, and nothing else.

* (R-AP2-1) The components are core-layer `FPrimeStripEquiv`s.  The paper's
  procession carries a system of poly-isomorphic transition data at the
  F-times-mu-prime-strip layer, and `FPrimeStrip` carries no times-mu layer
  (DSH-F report, API-1), so that layer is not represented here.  The
  already-landed reduction `SourceFTimesMuPrimeStripPolyIsomorphism.lean`
  (SHA prefix 12F25145) is the alignment target; it was in flight during
  this round and was not read or imported, so the alignment is by name
  only.
* (R-AP2-2) Stage/inclusion compatibility (the H2 processions,
  `SourceH1H2Construction.lean:1109-1317`) is not part of this record: the
  H2 stages are level-indexed capsules of columns at a single level, and the
  tree contains no structure connecting column slices to the stages.  The
  gap is recorded, not substituted.
* (R-AP2-3) The level equivalence is unconstrained: neither the Theta-link
  level mismatch nor the automorphism action on the procession (API-4
  R1/R3) is modelled.
* (R-AP2-4) The functoriality of the multiradial algorithm with respect to
  these isomorphisms (the third API-2 item) remains unconstructed, the
  algorithm itself being API-4 R3.

## What is proved in this file

* Non-vacuity without empty premises: identity and composition gates for the
  interface, from the kernel groupoid laws of `FPrimeStripEquiv`
  (`SourceH1H2Construction.lean:559-599`).
* Route 1 (core-link construction): the family link system is transitive
  (`I.fLinkAt_trans`, `SourceH1H2Construction.lean:237-243`) and hence
  supplies a transition-compatible isomorphism for every pair of columns and
  every level equivalence (`sourceCoreLinkIsomorphism`,
  `sourceAdjacentCoreLinkIsomorphism`).  This is a genuine theorem, but it
  is uniform in the supplied abstract link system and carries no
  Theta/times-mu/Kummer content; it is therefore deliberately NOT registered
  as the API-2 supply.  Its role is diagnostic: it isolates the missing
  content as exactly the identification of the components with the actual
  transition data (R-AP2-1).
* The supply card (`IUT-III.source-adjacent-column-procession-isomorphism`)
  remains pending, with the minimal specification recorded in the audit
  section.

## Route log (three routes)

* Route 1, core-link construction: succeeds at the reduced core level
  (above); rejected as the supply because it substitutes the abstract family
  link system for the Theta-transition content -- the resulting statement is
  independent of Theorem 3.11, K1/K2, and SHE.
* Route 2, special case: instantiating with a single concrete source input
  (`SourceProcessionBoundary.concreteInput`) or with a canonical family
  only; rejected as a special case (impersonation).
* Route 3, wrong type: `H2SpokePermutation`
  (`SourceH1H2Construction.lean:1315-1398`) is an intra-family spoke
  automorphism; `translate`/`translateEquiv`
  (`SourceOriginalInput.lean:502-601`) relabel indices and return no
  `FPrimeStripEquiv` between distinct strips; the finite model
  (`ConcreteFiniteRouteColumns.lean`, `FiniteAPTData:475-532`) has a finite
  carrier (DSH-F trap A3).  All rejected as wrong type.

## Justified consumers

* `IUT-III.source-APT-transport-supply` (`StepXI/APT.lean`): its `dependsOn`
  lists this card as the adjacent-column procession polymorphism of DSH-F
  API-2.
* Future functoriality API: the groupoid gates are the interface along which
  the multiradial algorithm functoriality (Theorem 3.11, (i)) must be stated
  once the algorithm (API-4 R3) is constructed.

## Paper locations

IUT III, Theorem 3.11, (i): pagewise `:9324`; functoriality with respect to
procession isomorphisms `:9434-9436`.  Remark 3.11.1, (iv): `:9923-9946`;
(APT) `:9931-9938`; (HIS) `:9947-9958`.  Corollary 3.12, Step (xi-b)/(xi-c).
DSH-F report: section API-2 (`REPORT.md:515-519`); section API-1 for the
times-mu alignment.

## Not claimed here

The actual procession transition systems of the paper (poly-isomorphic
transition data), the times-mu layer, stage/inclusion compatibility, the
actual adjacent-column isomorphism of Theorem 3.11, the automorphism action
on the procession, the functoriality of the multiradial algorithm, any
K1/K2 or SHE content, and any IPL/SHE/APT conclusion.  The K1/K2 boundary
cards (`IUT-II.vertical-log-kummer`), the SHE landing card
(`IUT-III.source-SHE-landing-evidence`), and the two-side
(domain/codomain, A/A') identification remain independent obligations: this
file establishes no implication among them and closes none of them.
-/

namespace LeanFormal.IUT

universe uv ua upi umon ui

namespace Theorem311Source

variable {V : Type uv}
variable {l : PrimeGeFive}

/-! ## 1. The frozen reduced statement -/

/-- A reduced isomorphism of processions of D-prime-strips between the
columns `n` and `n'` of the source carrier `I`: a level equivalence of the
Int-indexed column families together with transition-compatible components.

Original: an isomorphism of processions of D-prime-strips, i.e. of the
sequences of systems of poly-isomorphic transition data of Theorem 3.11,
(i), with respect to which the construction algorithm of `n,RLGP` is
functorial.  Reduced form: transition compatibility is imposed against the
family link system of `I` (`I.fLinkAt`); the times-mu layer (R-AP2-1), the
stage/inclusion compatibility of the H2 processions (R-AP2-2), and any
constraint on the level equivalence (R-AP2-3) are not carried. -/
structure SourceProcessionIsomorphism
    (I : OriginalInput.{ua, uv, upi, umon, ui} l V) (n n' : Int) where
  /-- the level correspondence of the two procession columns -/
  levelEquiv : Equiv Int Int
  /-- the components: a prime-strip equivalence at every level -/
  component : (m : Int) -> FPrimeStripEquiv (I.fPrimeStripAt n m)
    (I.fPrimeStripAt n' (levelEquiv m))
  /-- transition compatibility: the components make the family link squares
  commute -/
  link_naturality : (m m' : Int) ->
    FPrimeStripEquiv.trans (component m)
        (I.fLinkAt n' (levelEquiv m) n' (levelEquiv m')) =
      FPrimeStripEquiv.trans (I.fLinkAt n m n m') (component m')

/-! Shared normalization helpers for level equalities on `Int`. -/

theorem intEquiv_trans_apply (e1 e2 : Equiv Int Int) (m : Int) :
    (e1.trans e2) m = e2 (e1 m) :=
  rfl

theorem intEquiv_refl_apply (m : Int) : (Equiv.refl Int) m = m :=
  rfl

namespace SourceProcessionIsomorphism

variable {I : OriginalInput.{ua, uv, upi, umon, ui} l V}

/-! ## 2. Gates: identity and composition -/

/-- The identity procession isomorphism. -/
def refl (n : Int) : SourceProcessionIsomorphism I n n where
  levelEquiv := Equiv.refl Int
  component := fun m => FPrimeStripEquiv.refl (I.fPrimeStripAt n m)
  link_naturality := fun m m' => by
    simp only [intEquiv_refl_apply,
      OriginalInput.FPrimeStripEquiv.trans_refl_left,
      OriginalInput.FPrimeStripEquiv.trans_refl_right]

/-- Composition of procession isomorphisms (kernel groupoid gate). -/
def comp {n n' n'' : Int} (e : SourceProcessionIsomorphism I n n')
    (f : SourceProcessionIsomorphism I n' n'') :
    SourceProcessionIsomorphism I n n'' where
  levelEquiv := e.levelEquiv.trans f.levelEquiv
  component := fun m =>
    FPrimeStripEquiv.trans (e.component m) (f.component (e.levelEquiv m))
  link_naturality := fun m m' => by
    simp only [intEquiv_trans_apply]
    rw [OriginalInput.FPrimeStripEquiv.trans_assoc,
      f.link_naturality (e.levelEquiv m) (e.levelEquiv m'),
      <- OriginalInput.FPrimeStripEquiv.trans_assoc,
      e.link_naturality m m',
      OriginalInput.FPrimeStripEquiv.trans_assoc]

@[simp] theorem refl_levelEquiv (n : Int) :
    (refl (I := I) n).levelEquiv = Equiv.refl Int :=
  rfl

@[simp] theorem refl_component (n m : Int) :
    (refl (I := I) n).component m =
      FPrimeStripEquiv.refl (I.fPrimeStripAt n m) :=
  rfl

@[simp] theorem comp_levelEquiv {n n' n'' : Int}
    (e : SourceProcessionIsomorphism I n n')
    (f : SourceProcessionIsomorphism I n' n'') :
    (comp e f).levelEquiv = e.levelEquiv.trans f.levelEquiv :=
  rfl

@[simp] theorem comp_component {n n' n'' : Int}
    (e : SourceProcessionIsomorphism I n n')
    (f : SourceProcessionIsomorphism I n' n'') (m : Int) :
    (comp e f).component m =
      FPrimeStripEquiv.trans (e.component m)
        (f.component (e.levelEquiv m)) :=
  rfl

end SourceProcessionIsomorphism

/-! ## 3. Route 1: the core-link construction (proved, diagnostic) -/

/-- Route 1: the transition-compatible isomorphism obtained from the
transitivity of the family link system (`I.fLinkAt_trans`), for an arbitrary
level equivalence; diagnostic only, see the module docstring. -/
def sourceCoreLinkIsomorphism (I : OriginalInput.{ua, uv, upi, umon, ui} l V)
    (n n' : Int) (e : Equiv Int Int) :
    SourceProcessionIsomorphism I n n' where
  levelEquiv := e
  component := fun m => I.fLinkAt n m n' (e m)
  link_naturality := fun m m' => by
    rw [I.fLinkAt_trans, I.fLinkAt_trans]

/-- Route 1, adjacent-column instance (level-wise, for `n' = n + 1`). -/
def sourceAdjacentCoreLinkIsomorphism
    (I : OriginalInput.{ua, uv, upi, umon, ui} l V) (n : Int) :
    SourceProcessionIsomorphism I n (n + 1) :=
  sourceCoreLinkIsomorphism I n (n + 1) (Equiv.refl Int)

@[simp] theorem sourceCoreLinkIsomorphism_levelEquiv
    (I : OriginalInput.{ua, uv, upi, umon, ui} l V)
    (n n' : Int) (e : Equiv Int Int) :
    (sourceCoreLinkIsomorphism I n n' e).levelEquiv = e :=
  rfl

@[simp] theorem sourceCoreLinkIsomorphism_component
    (I : OriginalInput.{ua, uv, upi, umon, ui} l V)
    (n n' : Int) (e : Equiv Int Int) (m : Int) :
    (sourceCoreLinkIsomorphism I n n' e).component m =
      I.fLinkAt n m n' (e m) :=
  rfl

@[simp] theorem sourceAdjacentCoreLinkIsomorphism_levelEquiv
    (I : OriginalInput.{ua, uv, upi, umon, ui} l V) (n : Int) :
    (sourceAdjacentCoreLinkIsomorphism I n).levelEquiv = Equiv.refl Int :=
  rfl

theorem sourceAdjacentCoreLinkIsomorphism_component
    (I : OriginalInput.{ua, uv, upi, umon, ui} l V) (n m : Int) :
    (sourceAdjacentCoreLinkIsomorphism I n).component m =
      I.fLinkAt n m (n + 1) m :=
  rfl

end Theorem311Source

/-! ## 4. Audit -/

namespace Audit

/-- Audit record: the frozen reduced interface of procession isomorphisms.
Status is interface, not proved for the actual object; the actual supply is
tracked by `sourceAdjacentColumnProcessionSupply`. -/
def sourceProcessionIsomorphismInterface : Obligation :=
  { id := "IUT-III.source-procession-isomorphism"
    source :=
      "IUT III, Theorem 3.11, (i) (pagewise :9434-9436); Remark 3.11.1, " ++
        "(iv) (:9923-9946); Corollary 3.12, Step (xi-b); DSH-F report " ++
        "section API-2 (REPORT.md:515-519)"
    status := VerificationStatus.interface
    note :=
      "Reduced source interface for isomorphisms of processions of " ++
        "D-prime-strips: the record SourceProcessionIsomorphism (level " ++
        "equivalence plus transition-compatible components against the " ++
        "family link system), the proved groupoid gates refl/comp, and the " ++
        "proved route-1 core-link construction sourceCoreLinkIsomorphism / " ++
        "sourceAdjacentCoreLinkIsomorphism (uniform in the supplied " ++
        "abstract link system; deliberately NOT registered as the supply). " ++
        "NOT constructed: the transition data at the F-times-mu layer " ++
        "(alignment target SourceFTimesMuPrimeStripPolyIsomorphism.lean, " ++
        "SHA prefix 12F25145; in flight during this round, not read or " ++
        "imported), the stage/inclusion compatibility of the H2 processions " ++
        "(SourceH1H2Construction.lean:1109-1317), the constraints of the " ++
        "Theta-link level mismatch, the automorphism action on the " ++
        "procession, and the functoriality of the multiradial algorithm " ++
        "along the procession. No IPL/SHE/APT conclusion is asserted."
    dependsOn :=
      [ "IUT-III.source-multiradial-two-action-equivalence" ] }

/-- Named card: the actual adjacent-column procession isomorphism for the
actual Theorem-3.11 instance, carrying the transition data. -/
def sourceAdjacentColumnProcessionSupply : Obligation :=
  { id := "IUT-III.source-adjacent-column-procession-isomorphism"
    source :=
      "IUT III, Remark 3.11.1, (iv) ((APT) pagewise :9931-9938; (HIS) " ++
        ":9947-9958); Theorem 3.11, (i) (pagewise :9434-9436); Corollary " ++
        "3.12, Step (xi-b)/(xi-c); DSH-F report section API-2"
    status := VerificationStatus.pending
    note :=
      "Named card: for the actual Theorem-3.11 instance (I, n), an " ++
        "adjacent-column procession isomorphism SourceProcessionIsomorphism " ++
        "I n (n + 1) whose components carry the actual transition data. " ++
        "Minimal specification: (D) a level equivalence of the two columns; " ++
        "(C) components identified with the systems of poly-isomorphic " ++
        "transition data of the procession at the F-times-mu layer, aligned " ++
        "with the read-only reduction SourceFTimesMuPrimeStripPolyIsomorphism " ++
        "(SHA prefix 12F25145), not wired this round; (S) stage/inclusion " ++
        "compatibility with the H2 processions; (T) the identification of " ++
        "the components with the Theta-link transport content of K1/K2 " ++
        "(IUT-II.vertical-log-kummer; repo counterpart " ++
        "SourceK1K2Construction.lean:666-689), itself a pending obligation " ++
        "independent of this card; (F) functoriality of the multiradial " ++
        "algorithm (API-4 R3), a separate independent obligation. Routes " ++
        "attempted: (1) core-link construction, proven in Section 3 -- " ++
        "succeeds only at the core level and is content-free with respect " ++
        "to the Theta-transition data, hence not the object; (2) special " ++
        "case via one concrete source input, rejected as impersonation; " ++
        "(3) wrong type -- H2SpokePermutation (intra-family spoke), " ++
        "translate/translateEquiv (index relabelling, no strip " ++
        "equivalences), finite model FiniteAPTData (DSH-F trap A3), all " ++
        "rejected. The K1/K2 boundary cards, the SHE landing card " ++
        "IUT-III.source-SHE-landing-evidence, and the two-side " ++
        "(domain/codomain, A/A') identification remain independent " ++
        "obligations: no implication among them and this card is " ++
        "established here, and the supply is not impersonated by the " ++
        "core-link instance. PARKED at this named card."
    dependsOn :=
      [ "IUT-II.vertical-log-kummer",
        "IUT-III.source-SHE-landing-evidence" ] }

end Audit

end LeanFormal.IUT
