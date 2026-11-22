import LeanFormal.IUT.IUTIII.Theorem311.SourceKummerEvaluationArrows

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

/-!
# Multiradial functor presentation and two-action equivalence (reduced interface)

This module freezes the reduced source-level interface of the multiradial
construction algorithm of IUT III, Theorem 3.11, (i), together with the
two-action (Ind1)/(Ind2) equivalence of its output data, so that output data
of algorithm instances can be compared and the quotient by the two actions
can be formed (the descent needed by the APT-style consumers).

## Original (paper) route

* IUT III, Theorem 3.11, (i): consider the procession of D-prime-strips
  `Prc(n,◦D_T)` obtained from the D-Theta-plus-minus-bridge of `n,◦HT_D`,
  together with the data (a) (topological modules and mono-analytic integral
  structures, with procession-normalized mono-analytic log-volumes),
  (b) (splitting monoids), (c) (number fields and natural isomorphisms of the
  associated global non-realified/realified Frobenioids). The collection
  `n,◦RLGP` of (a), (b), (c) is regarded up to indeterminacies of two types:
  (Ind1), induced by the automorphisms of the procession of
  D-prime-strips; and (Ind2), for each `v_Q`, induced by the action of
  independent copies of `Ism` on the direct summands of the `j+1` tensor
  factors. `n,◦RLGP` may be constructed via an algorithm in the procession
  that is functorial with respect to isomorphisms of processions of
  D-prime-strips; the etale-picture permutation symmetries induce compatible
  poly-isomorphisms `Prc(n) ~ Prc(n')` and `n,◦RLGP ~ n',◦RLGP`.
* IUT III, Remark 3.11.1, (i), (ii): the algorithm describes the LGP-monoids
  (= the theta values) of one vertical line in terms of the a priori alien
  arithmetic holomorphic structure of another; its functoriality is with
  respect to arbitrary isomorphisms of the F-prime-strips appearing as input
  data, while the codomain side (q-pilot strip) stays coric/fixed.
* IUT III, Remark 3.11.1, (iii), (iv): the output data satisfies the IPL and
  SHE properties; APT states that this output arises from a construction
  algorithm simultaneously valid relative to the arithmetic holomorphic
  structures in the domain and codomain of the Theta-link, not from a
  set-theoretic transport.
* IUT III, Remark 3.10.2: the Kummer-evaluation square whose two-path
  statement surface is landed in `SourceKummerEvaluationArrows.lean` (API-3).

## Reduced route (deviations)

R1. Procession. The paper`s `Prc(n,◦D_T)` is a sequence of systems of
    D-prime-strips `{D_0} -> {D_0, D_1} -> ...` with compatible
    poly-isomorphic transition data. The reduced anchor `sourceColumnProcession`
    keeps only the members `fPrimeStripAt n m`; the transition structure and
    the automorphism action on the procession itself are not constructed.
R2. Output. The data (a) (topological modules, log-shells), (b) (splitting
    monoids) and (c) (number fields, Frobenioid isomorphisms) are not
    constructed; the record`s `Output` is an abstract carrier (Card MP).
R3. Functoriality. The functoriality of the algorithm with respect to
    isomorphisms of processions is represented only by the carried (Ind1)
    action on the output; the functor on procession isomorphisms is not
    constructed.
R4. (Ind2). The independent copies of `Ism` acting on the individual direct
    summands of the tensor factors are collapsed into a single group action
    `G₂` on the output; the per-summand structure is not modelled.
R5. (Ind3). The upper-semi/log-Kummer portion of Theorem 3.11, (ii), is out
    of scope of this module (separate vertical log-Kummer contract).
R6. Group identification. A two-action equivalence is stated between two
    algorithm instances whose (Ind2) groups are the same group (the canonical
    `Ism` copies); the identification of the (Ind1) groups is carried as data
    `ind1GroupEquiv` rather than derived from the permutation bi-coric bridge
    of Theorem 1.5, (iii) (separate construction).
R7. Docking. The unit-layer two-path of a Kummer-evaluation square is frozen
    as the new card `SourceSquareUnitLayerTwoPath`; it is NOT implied by the
    strip-level `commutes` of API-3 (no coherence between the strip-level
    representative and the carried unit layer was frozen there, API-3 R5).
R8. No identification of the abstract `Output` with any existing local
    carrier (`AlgorithmOutput`/`runAlgorithm` are not strip-level objects,
    DSH-F trap T6; the finite models are not imported, trap T7); no
    identification with the paper`s q-pilot object (trap T5).

## Named source cards (not constructed here)

* Card MP: `SourceTheorem311MultiradialPresentation` (procession anchor,
  output data, (Ind1) action carrier).
* Card MA: `SourceTheorem311MultiradialAlgorithm` (the two actions and their
  equivariance/commutation; Theorem 3.11, (i)).
* Card TA: `SourceTheorem311TwoActionEquivalence` (the comparison of two
  algorithm instances preserving both actions; the quotient descent is
  constructed on top of it, not assumed).
* Card U2P: `SourceSquareUnitLayerTwoPath` (the unit-layer two-path coherence
  of the API-3 Kummer-evaluation square; SHE-relevant level at which the
  (Ind2) action lives).

## Proved here

One/mul laws for the carried actions; existence characterizations
(`nonempty_iff`); the trivial-action gate witnesses; inverse-action
preservation laws of a two-action equivalence; preservation of the generated
relation in both directions; the quotient maps, the descended quotient
equivalence `quotientEquiv`, and its `rfl`/`simp` compatibility lemmas; the
reflexivity gate `SourceTheorem311TwoActionEquivalence.refl`; the family-level
Kummer and evaluation-unit isomorphisms over all places with their pointwise
equivariance, and the two unit-layer path composites of a square.

## Not claimed here

The actual procession, the data (a), (b), (c), the actual (Ind1)/(Ind2)
actions of Theorem 3.11, (i), the (Ind3) content, the permutation bi-coric
bridge, any IPL/SHE/APT conclusion, the unit-layer two-path coherence (Card
U2P is a frozen hypothesis), and any identification with the supplied
Hodge-theater-family links or the q-pilot object.

## Paper locations

IUT III, Theorem 3.11: pagewise lines 9311 seqq. ((i): 9324; (a): 9336;
(b): 9352; (c): 9383; (Ind1): 9419; (Ind2): 9422; functoriality: 9434-9436;
permutation compatibility: 9437-9456; (ii): 9458; (iii): 9613). Remark
3.11.1: 9786 ((i)), 9803 ((ii), functoriality w.r.t. input prime-strips:
9817-9827), 9843 ((iii), IPL/SHE), 9923 ((iv), APT). Remark 3.10.2: 9225.
Corollary 3.12, Step (xi-b): 10950.
-/

namespace LeanFormal.IUT

universe uG uG' uG₂ uv ua upi umon ui uOut uOut₁ uOut₂

namespace Theorem311Source

variable {V : Type uv}
variable {l : PrimeGeFive}

/-! ## 1. The reduced procession presentation (Card MP) -/

/-- The reduced source anchor of the procession of D-prime-strips
`Prc(n,◦D_T)` of Theorem 3.11, (i): the column of source strips over `Int`.

Reduced form: only the members are kept; the transition systems and the
automorphism action on the procession are not constructed (R1). -/
def sourceColumnProcession (I : OriginalInput.{ua, uv, upi, umon, ui} l V)
    (n : Int) : Int → FPrimeStrip V :=
  fun m => I.fPrimeStripAt n m

/-- Card MP: the reduced multiradial presentation of Theorem 3.11, (i).

Original: the collection `n,◦RLGP` of the data (a), (b), (c) constructed via
an algorithm in the procession, regarded up to the indeterminacies (Ind1)
and (Ind2).  Reduced form: the output data is an abstract carrier `Output`
(the data (a), (b), (c) are not constructed, R2), and the procession action
is the permutation action on the output induced by the automorphisms of the
procession -- the (Ind1) carrier.  The functor itself is not constructed
(R3). -/
structure SourceTheorem311MultiradialPresentation (G : Type uG) [Group G]
    (I : OriginalInput.{ua, uv, upi, umon, ui} l V) (n : Int)
    (Output : Type uOut) where
  /-- the constructed output data (the paper`s `n,◦RLGP`, abstract here) -/
  output : Output
  /-- the (Ind1) action: automorphisms of the procession of D-prime-strips
  act on the output data -/
  processionAction : G →* Equiv.Perm Output

namespace SourceTheorem311MultiradialPresentation

variable {G : Type uG} [Group G]
variable {I : OriginalInput.{ua, uv, upi, umon, ui} l V} {n : Int}
variable {Output : Type uOut}

/-- The procession action is an action: the unit acts as the identity. -/
@[simp] theorem processionAction_one
    (P : SourceTheorem311MultiradialPresentation G I n Output) (o : Output) :
    P.processionAction 1 o = o := by
  rw [MonoidHom.map_one]
  rfl

/-- The procession action is an action: multiplication acts by composition. -/
theorem processionAction_mul
    (P : SourceTheorem311MultiradialPresentation G I n Output)
    (g h : G) (o : Output) :
    P.processionAction (g * h) o = P.processionAction g (P.processionAction h o) := by
  rw [MonoidHom.map_mul, Equiv.Perm.mul_apply]

/-- Gate/characterization: a presentation exists exactly when output data
exists; the procession action can always be supplied trivially. -/
theorem nonempty_iff :
    Nonempty (SourceTheorem311MultiradialPresentation G I n Output) ↔
      Nonempty Output :=
  ⟨fun ⟨P⟩ => ⟨P.output⟩,
    fun ⟨o⟩ => ⟨{ output := o, processionAction := 1 }⟩⟩

end SourceTheorem311MultiradialPresentation

/-! ## 2. The reduced multiradial algorithm (Card MA) -/

/-- Card MA: the reduced multiradial algorithm record of Theorem 3.11, (i):
the presentation together with the (Ind2) action and the equivariance of the
two actions (their commutation).

Original: the two types of indeterminacies on `n,◦RLGP`: (Ind1) (automorphisms
of the procession) and (Ind2) (independent copies of `Ism` on the tensor
direct summands); the algorithm is functorial, so these act on the output.
Reduced form: `ind2Action` is a single group action on the abstract output
(R4); the independence of the `Ism` copies is not modelled. -/
structure SourceTheorem311MultiradialAlgorithm (G₁ : Type uG) [Group G₁]
    (G₂ : Type uG₂) [Group G₂] (I : OriginalInput.{ua, uv, upi, umon, ui} l V)
    (n : Int) (Output : Type uOut) where
  /-- the presentation: procession anchor and output data with its (Ind1)
  action -/
  presentation : SourceTheorem311MultiradialPresentation G₁ I n Output
  /-- the (Ind2) action: the (collapsed) action of the copies of `Ism` on
  the output data -/
  ind2Action : G₂ →* Equiv.Perm Output
  /-- the equivariance of the two actions on the output: they commute -/
  ind1_ind2_commute : ∀ (g₁ : G₁) (g₂ : G₂) (o : Output),
    presentation.processionAction g₁ (ind2Action g₂ o) =
      ind2Action g₂ (presentation.processionAction g₁ o)

namespace SourceTheorem311MultiradialAlgorithm

variable {G₁ : Type uG} [Group G₁] {G₂ : Type uG₂} [Group G₂]
variable {I : OriginalInput.{ua, uv, upi, umon, ui} l V} {n : Int}
variable {Output : Type uOut}

/-- The (Ind1) action of an algorithm instance (the procession action of its
presentation). -/
def ind1Action (A : SourceTheorem311MultiradialAlgorithm G₁ G₂ I n Output) :
    G₁ →* Equiv.Perm Output :=
  A.presentation.processionAction

/-- The (Ind1) action sends the unit to the identity. -/
@[simp] theorem ind1Action_one
    (A : SourceTheorem311MultiradialAlgorithm G₁ G₂ I n Output) (o : Output) :
    A.ind1Action 1 o = o := by
  change A.presentation.processionAction 1 o = o
  rw [MonoidHom.map_one]
  rfl

/-- The (Ind1) action is an action. -/
theorem ind1Action_mul
    (A : SourceTheorem311MultiradialAlgorithm G₁ G₂ I n Output)
    (g h : G₁) (o : Output) :
    A.ind1Action (g * h) o = A.ind1Action g (A.ind1Action h o) := by
  change A.presentation.processionAction (g * h) o =
    A.presentation.processionAction g (A.presentation.processionAction h o)
  rw [MonoidHom.map_mul, Equiv.Perm.mul_apply]

/-- The (Ind2) action sends the unit to the identity. -/
@[simp] theorem ind2Action_one
    (A : SourceTheorem311MultiradialAlgorithm G₁ G₂ I n Output) (o : Output) :
    A.ind2Action 1 o = o := by
  rw [MonoidHom.map_one]
  rfl

/-- The (Ind2) action is an action. -/
theorem ind2Action_mul
    (A : SourceTheorem311MultiradialAlgorithm G₁ G₂ I n Output)
    (g h : G₂) (o : Output) :
    A.ind2Action (g * h) o = A.ind2Action g (A.ind2Action h o) := by
  rw [MonoidHom.map_mul, Equiv.Perm.mul_apply]

/-- Gate/characterization: an algorithm instance exists exactly when output
data exists; both actions can always be supplied trivially. -/
theorem nonempty_iff :
    Nonempty (SourceTheorem311MultiradialAlgorithm G₁ G₂ I n Output) ↔
      Nonempty Output :=
  ⟨fun ⟨A⟩ => ⟨A.presentation.output⟩,
    fun ⟨o⟩ =>
      ⟨{ presentation := { output := o, processionAction := 1 }
         ind2Action := 1
         ind1_ind2_commute := fun _ _ _ => by simp }⟩⟩

end SourceTheorem311MultiradialAlgorithm

/-! ## 3. The two-action equivalence and quotient descent (Card TA) -/

section TwoAction

variable {G₁ : Type uG} [Group G₁] {G₁' : Type uG'} [Group G₁']
variable {G₂ : Type uG₂} [Group G₂]
variable {I : OriginalInput.{ua, uv, upi, umon, ui} l V} {n n' : Int}
variable {Output₁ : Type uOut₁} {Output₂ : Type uOut₂}

/-- The single-step relation generated by the two indeterminacy actions of an
algorithm instance on its output: `o₂` is obtained from `o₁` by one (Ind1) or
one (Ind2) step. -/
def twoActionRel (A : SourceTheorem311MultiradialAlgorithm G₁ G₂ I n Output₁)
    (o₁ o₂ : Output₁) : Prop :=
  (∃ g : G₁, o₂ = A.ind1Action g o₁) ∨ (∃ g : G₂, o₂ = A.ind2Action g o₁)

/-- The equivalence relation on the output generated by the two actions. -/
inductive TwoActionGeneratedRel
    (A : SourceTheorem311MultiradialAlgorithm G₁ G₂ I n Output₁) :
    Output₁ → Output₁ → Prop
  | rel {o₁ o₂} : twoActionRel A o₁ o₂ → TwoActionGeneratedRel A o₁ o₂
  | refl (o) : TwoActionGeneratedRel A o o
  | symm {o₁ o₂} : TwoActionGeneratedRel A o₁ o₂ → TwoActionGeneratedRel A o₂ o₁
  | trans {o₁ o₂ o₃} : TwoActionGeneratedRel A o₁ o₂ →
      TwoActionGeneratedRel A o₂ o₃ → TwoActionGeneratedRel A o₁ o₃

/-- The setoid of the generated relation; the quotient of the output by the
two actions is taken with respect to it. -/
def twoActionSetoid (A : SourceTheorem311MultiradialAlgorithm G₁ G₂ I n Output₁) :
    Setoid Output₁ :=
  ⟨TwoActionGeneratedRel A, TwoActionGeneratedRel.refl,
    TwoActionGeneratedRel.symm, TwoActionGeneratedRel.trans⟩

/-- The quotient of the output data by the two actions (the reduced carrier of
the descended statement surface). -/
abbrev twoActionQuotient
    (A : SourceTheorem311MultiradialAlgorithm G₁ G₂ I n Output₁) :=
  Quotient (twoActionSetoid A)

/-- Card TA: the reduced two-action equivalence between two algorithm
instances (e.g. over two columns `n`, `n'`).

Original: for `n, n'` in Z, the etale-picture permutation symmetries induce
compatible poly-isomorphisms `Prc(n) ~ Prc(n')` and `n,◦RLGP ~ n',◦RLGP`
(Theorem 3.11, (i); Remark 3.11.1, (ii)).  Reduced form: an identification of
the two (Ind1) groups (`ind1GroupEquiv`), an equivalence of output data
(`outputEquiv`), preservation of both actions (the shared (Ind2) group `G₂`
acts on both sides, R6), and the descended quotient equivalence
`quotientEquiv` (constructed below, not a field). -/
structure SourceTheorem311TwoActionEquivalence
    (A : SourceTheorem311MultiradialAlgorithm G₁ G₂ I n Output₁)
    (A' : SourceTheorem311MultiradialAlgorithm G₁' G₂ I n' Output₂) where
  /-- the identification of the two (Ind1) groups -/
  ind1GroupEquiv : G₁ ≃* G₁'
  /-- the equivalence of the output data of the two instances -/
  outputEquiv : Output₁ ≃ Output₂
  /-- preservation of the (Ind1) action -/
  preserves_ind1 : ∀ (g : G₁) (o : Output₁),
    outputEquiv (A.ind1Action g o) =
      A'.ind1Action (ind1GroupEquiv g) (outputEquiv o)
  /-- preservation of the (Ind2) action -/
  preserves_ind2 : ∀ (g : G₂) (o : Output₁),
    outputEquiv (A.ind2Action g o) = A'.ind2Action g (outputEquiv o)

namespace SourceTheorem311TwoActionEquivalence

variable {A : SourceTheorem311MultiradialAlgorithm G₁ G₂ I n Output₁}
variable {A' : SourceTheorem311MultiradialAlgorithm G₁' G₂ I n' Output₂}
variable (E : SourceTheorem311TwoActionEquivalence A A')

/-- The inverse action law for (Ind1): the inverse output equivalence
intertwines the inverse (Ind1) group identification. -/
theorem preserves_ind1_symm (g : G₁') (o : Output₂) :
    E.outputEquiv.symm (A'.ind1Action g o) =
      A.ind1Action (E.ind1GroupEquiv.symm g) (E.outputEquiv.symm o) := by
  apply E.outputEquiv.injective
  rw [Equiv.apply_symm_apply, E.preserves_ind1, MulEquiv.apply_symm_apply,
    Equiv.apply_symm_apply]

/-- The inverse action law for (Ind2). -/
theorem preserves_ind2_symm (g : G₂) (o : Output₂) :
    E.outputEquiv.symm (A'.ind2Action g o) = A.ind2Action g (E.outputEquiv.symm o) := by
  apply E.outputEquiv.injective
  rw [Equiv.apply_symm_apply, E.preserves_ind2, Equiv.apply_symm_apply]

/-- The output equivalence preserves one (Ind1) or (Ind2) step. -/
theorem twoActionRel_map {o₁ o₂ : Output₁} (h : twoActionRel A o₁ o₂) :
    twoActionRel A' (E.outputEquiv o₁) (E.outputEquiv o₂) := by
  rcases h with ⟨g, rfl⟩ | ⟨g, rfl⟩
  · exact Or.inl ⟨E.ind1GroupEquiv g, E.preserves_ind1 g o₁⟩
  · exact Or.inr ⟨g, E.preserves_ind2 g o₁⟩

/-- The inverse output equivalence preserves one (Ind1) or (Ind2) step. -/
theorem twoActionRel_map_symm {o₁ o₂ : Output₂} (h : twoActionRel A' o₁ o₂) :
    twoActionRel A (E.outputEquiv.symm o₁) (E.outputEquiv.symm o₂) := by
  rcases h with ⟨g, rfl⟩ | ⟨g, rfl⟩
  · exact Or.inl ⟨E.ind1GroupEquiv.symm g, E.preserves_ind1_symm g o₁⟩
  · exact Or.inr ⟨g, E.preserves_ind2_symm g o₁⟩

/-- The output equivalence preserves the generated relation. -/
theorem twoActionGeneratedRel_map :
    ∀ {o₁ o₂ : Output₁}, TwoActionGeneratedRel A o₁ o₂ →
      TwoActionGeneratedRel A' (E.outputEquiv o₁) (E.outputEquiv o₂) := by
  intro o₁ o₂ h
  induction h with
  | rel h => exact TwoActionGeneratedRel.rel (E.twoActionRel_map h)
  | refl o => exact TwoActionGeneratedRel.refl _
  | symm _ ih => exact ih.symm
  | trans _ _ ih₁ ih₂ => exact ih₁.trans ih₂

/-- The inverse output equivalence preserves the generated relation. -/
theorem twoActionGeneratedRel_map_symm :
    ∀ {o₁ o₂ : Output₂}, TwoActionGeneratedRel A' o₁ o₂ →
      TwoActionGeneratedRel A (E.outputEquiv.symm o₁) (E.outputEquiv.symm o₂) := by
  intro o₁ o₂ h
  induction h with
  | rel h => exact TwoActionGeneratedRel.rel (E.twoActionRel_map_symm h)
  | refl o => exact TwoActionGeneratedRel.refl _
  | symm _ ih => exact ih.symm
  | trans _ _ ih₁ ih₂ => exact ih₁.trans ih₂

/-- The quotient map induced by the output equivalence. -/
def quotientMap : Quotient (twoActionSetoid A) → Quotient (twoActionSetoid A') :=
  Quotient.map E.outputEquiv (fun _ _ h => E.twoActionGeneratedRel_map h)

/-- The quotient map induced by the inverse output equivalence. -/
def quotientMapSymm : Quotient (twoActionSetoid A') → Quotient (twoActionSetoid A) :=
  Quotient.map E.outputEquiv.symm (fun _ _ h => E.twoActionGeneratedRel_map_symm h)

/-- Computation law for the quotient map. -/
@[simp] theorem quotientMap_mk (o : Output₁) :
    E.quotientMap (Quotient.mk (twoActionSetoid A) o) =
      Quotient.mk (twoActionSetoid A') (E.outputEquiv o) :=
  Quotient.map_mk E.outputEquiv _ o

/-- Computation law for the inverse quotient map. -/
@[simp] theorem quotientMapSymm_mk (o : Output₂) :
    E.quotientMapSymm (Quotient.mk (twoActionSetoid A') o) =
      Quotient.mk (twoActionSetoid A) (E.outputEquiv.symm o) :=
  Quotient.map_mk E.outputEquiv.symm _ o

/-- The descended quotient equivalence: the two-action equivalence descends
to the quotients of the outputs by the two actions. -/
def quotientEquiv : Quotient (twoActionSetoid A) ≃ Quotient (twoActionSetoid A') where
  toFun := E.quotientMap
  invFun := E.quotientMapSymm
  left_inv := fun q => Quotient.inductionOn q fun o => by
    show E.quotientMapSymm (E.quotientMap (Quotient.mk (twoActionSetoid A) o)) =
      Quotient.mk (twoActionSetoid A) o
    rw [E.quotientMap_mk, E.quotientMapSymm_mk, Equiv.symm_apply_apply]
  right_inv := fun q => Quotient.inductionOn q fun o => by
    show E.quotientMap (E.quotientMapSymm (Quotient.mk (twoActionSetoid A') o)) =
      Quotient.mk (twoActionSetoid A') o
    rw [E.quotientMapSymm_mk, E.quotientMap_mk, Equiv.apply_symm_apply]

/-- Computation law for the descended quotient equivalence. -/
@[simp] theorem quotientEquiv_mk (o : Output₁) :
    E.quotientEquiv (Quotient.mk (twoActionSetoid A) o) =
      Quotient.mk (twoActionSetoid A') (E.outputEquiv o) :=
  E.quotientMap_mk o

/-- Computation law for the inverse of the descended quotient equivalence. -/
@[simp] theorem quotientEquiv_symm_mk (o : Output₂) :
    E.quotientEquiv.symm (Quotient.mk (twoActionSetoid A') o) =
      Quotient.mk (twoActionSetoid A) (E.outputEquiv.symm o) := by
  rw [Equiv.symm_apply_eq]
  rw [E.quotientEquiv_mk, Equiv.apply_symm_apply]

/-- The reflexivity gate: any algorithm instance is two-action equivalent to
itself. -/
def refl (A : SourceTheorem311MultiradialAlgorithm G₁ G₂ I n Output₁) :
    SourceTheorem311TwoActionEquivalence A A where
  ind1GroupEquiv := MulEquiv.refl G₁
  outputEquiv := Equiv.refl Output₁
  preserves_ind1 := fun _ _ => rfl
  preserves_ind2 := fun _ _ => rfl

end SourceTheorem311TwoActionEquivalence

end TwoAction

/-! ## 4. Docking with the API-3 Kummer-evaluation square -/

section EvaluationSquareDocking

variable {G : Type uG} [Group G] [TopologicalSpace G]
variable {upper lower upperLeft upperRight lowerLeft lowerRight : FPrimeStrip V}

/-- The pointwise action of a family of per-place unit actions on the family
of unit-layer torsion quotients of a strip. -/
def unitLayerFamilyAction {S : FPrimeStrip V}
    (act : ∀ v : V, G →* MulAut ((S.Mon v)ˣ)) :
    G →* MulAut (∀ v : V, TimesMuQuotient ((S.Mon v)ˣ)) where
  toFun g :=
    { toFun := fun x v => TimesMuQuotient.action (act v) g (x v)
      invFun := fun x v => TimesMuQuotient.action (act v) g⁻¹ (x v)
      left_inv := fun x => funext fun v => by
        change TimesMuQuotient.action (act v) g⁻¹
            (TimesMuQuotient.action (act v) g (x v)) = x v
        rw [← TimesMuQuotient.action_mul, inv_mul_cancel,
          TimesMuQuotient.action_one]
      right_inv := fun x => funext fun v => by
        change TimesMuQuotient.action (act v) g
            (TimesMuQuotient.action (act v) g⁻¹ (x v)) = x v
        rw [← TimesMuQuotient.action_mul, mul_inv_cancel,
          TimesMuQuotient.action_one]
      map_mul' := fun x y => funext fun v =>
        map_mul ((TimesMuQuotient.action (act v)) g) (x v) (y v) }
  map_one' := by
    apply MulEquiv.ext
    intro x
    funext v
    exact TimesMuQuotient.action_one (act v) (x v)
  map_mul' := fun g h => by
    apply MulEquiv.ext
    intro x
    funext v
    exact TimesMuQuotient.action_mul (act v) g h (x v)

namespace SourceTimesMuKummerLayer

/-- The family-level Kummer isomorphism at all places at once (the reduced
`x`-mu layer of Card LK of API-3, bundled over `V`). -/
def familyEquiv (L : SourceTimesMuKummerLayer G upper lower) :
    (∀ v : V, TimesMuQuotient ((upper.Mon v)ˣ)) ≃*
      (∀ v : V, TimesMuQuotient ((lower.Mon v)ˣ)) where
  toFun x v := (L.kummer v).equiv (x v)
  invFun x v := (L.kummer v).equiv.symm (x v)
  left_inv x := funext fun v => (L.kummer v).equiv.symm_apply_apply (x v)
  right_inv x := funext fun v => (L.kummer v).equiv.apply_symm_apply (x v)
  map_mul' x y := funext fun v => map_mul ((L.kummer v).equiv) (x v) (y v)

/-- The family-level Kummer isomorphism is equivariant with respect to the
family actions induced by the two carried per-place actions. -/
theorem familyEquiv_equivariant (L : SourceTimesMuKummerLayer G upper lower)
    (g : G) (x : ∀ v : V, TimesMuQuotient ((upper.Mon v)ˣ)) :
    L.familyEquiv (unitLayerFamilyAction (S := upper) L.sourceAction g x) =
      unitLayerFamilyAction (S := lower) L.targetAction g (L.familyEquiv x) := by
  funext v
  exact (L.kummer v).equivariant g (x v)

end SourceTimesMuKummerLayer

namespace SourceEvaluationUnitPortion

/-- The family-level unit-layer isomorphism of the evaluation unit portion
(Card EV of API-3), bundled over `V`. -/
def familyEquiv (P : SourceEvaluationUnitPortion G upper lower) :
    (∀ v : V, TimesMuQuotient ((upper.Mon v)ˣ)) ≃*
      (∀ v : V, TimesMuQuotient ((lower.Mon v)ˣ)) where
  toFun x v := P.unitLayer v (x v)
  invFun x v := (P.unitLayer v).symm (x v)
  left_inv x := funext fun v => (P.unitLayer v).symm_apply_apply (x v)
  right_inv x := funext fun v => (P.unitLayer v).apply_symm_apply (x v)
  map_mul' x y := funext fun v => map_mul (P.unitLayer v) (x v) (y v)

/-- The family-level unit-layer isomorphism is equivariant with respect to the
family actions induced by the two carried per-place actions. -/
theorem familyEquiv_equivariant (P : SourceEvaluationUnitPortion G upper lower)
    (g : G) (x : ∀ v : V, TimesMuQuotient ((upper.Mon v)ˣ)) :
    P.familyEquiv (unitLayerFamilyAction (S := upper) P.sourceAction g x) =
      unitLayerFamilyAction (S := lower) P.targetAction g (P.familyEquiv x) := by
  funext v
  exact P.unitLayer_equivariant v g (x v)

end SourceEvaluationUnitPortion

namespace SourceKummerEvaluationSquare

/-- The domain-side unit-layer composite of the Kummer-evaluation square: the
inverse of the left Kummer layer followed by the lower evaluation unit
portion. -/
def unitLayerDomainComposite
    (S : SourceKummerEvaluationSquare G upperLeft upperRight lowerLeft lowerRight) :
    (∀ v : V, TimesMuQuotient ((upperLeft.Mon v)ˣ)) ≃*
      (∀ v : V, TimesMuQuotient ((lowerRight.Mon v)ˣ)) :=
  (SourceTimesMuKummerLayer.familyEquiv S.leftKummer.layer).symm.trans
    (SourceEvaluationUnitPortion.familyEquiv S.lowerHorizontal.unitPortion)

/-- The codomain-side unit-layer composite of the Kummer-evaluation square:
the upper evaluation unit portion followed by the inverse of the right Kummer
layer. -/
def unitLayerCodomainComposite
    (S : SourceKummerEvaluationSquare G upperLeft upperRight lowerLeft lowerRight) :
    (∀ v : V, TimesMuQuotient ((upperLeft.Mon v)ˣ)) ≃*
      (∀ v : V, TimesMuQuotient ((lowerRight.Mon v)ˣ)) :=
  (SourceEvaluationUnitPortion.familyEquiv S.upperHorizontal.unitPortion).trans
    (SourceTimesMuKummerLayer.familyEquiv S.rightKummer.layer).symm

end SourceKummerEvaluationSquare

/-- Card U2P: the unit-layer two-path coherence of a Kummer-evaluation square
(the SHE-relevant level, where the (Ind2) indeterminacy lives).

Original: IUT III, Theorem 3.11, (iii), (c), (d): the Kummer isomorphisms and
the evaluation maps are compatible with the horizontal arrows.  This card
freezes the equality of the two unit-layer composites of the square.  It is
NOT implied by the strip-level `commutes` of API-3 (no coherence between the
strip-level representative and the unit layer was frozen there, API-3 R5);
the coherence is an unproved hypothesis (R7). -/
structure SourceSquareUnitLayerTwoPath
    (S : SourceKummerEvaluationSquare G upperLeft upperRight lowerLeft lowerRight) where
  /-- the two unit-layer composites of the square agree -/
  coherence : S.unitLayerDomainComposite = S.unitLayerCodomainComposite

end EvaluationSquareDocking

end Theorem311Source

namespace Audit

def sourceMultiradialTwoActionEquivalence : Obligation :=
  { id := "IUT-III.source-multiradial-two-action-equivalence"
    source :=
      "IUT III, Theorem 3.11, (i), (ii); Remark 3.11.1, (i), (ii), (iii), " ++
        "(iv); Remark 3.10.2 (via the API-3 Kummer-evaluation square)"
    status := VerificationStatus.interface
    note :=
      "Reduced source interface for the multiradial functor presentation and " ++
        "the two-action (Ind1)/(Ind2) equivalence over the source input: " ++
        "frozen records SourceTheorem311MultiradialPresentation (procession " ++
        "anchor, abstract output, Ind1 action), " ++
        "SourceTheorem311MultiradialAlgorithm (the two actions and their " ++
        "commutation), SourceTheorem311TwoActionEquivalence (Ind1 group " ++
        "identification, output equivalence, preservation of both actions), " ++
        "and the unit-layer docking to API-3: family-level Kummer/evaluation " ++
        "isomorphisms with proved equivariance, the two unit-layer path " ++
        "composites, and the frozen card SourceSquareUnitLayerTwoPath. " ++
        "Proved: action application laws, existence characterizations, " ++
        "inverse preservation laws, generated-relation preservation, the " ++
        "quotient maps and the descended quotientEquiv with its rfl/simp " ++
        "laws, reflexivity, and the family equivariances. NOT constructed: " ++
        "the procession transition structure, the output data (a), (b), (c), " ++
        "the actual (Ind1)/(Ind2) actions of Theorem 3.11, (i), the (Ind3) " ++
        "content, the permutation bi-coric bridge, and the unit-layer " ++
        "two-path coherence; no IPL/SHE/APT conclusion is asserted."
    dependsOn :=
      [ "IUT-III.source-kummer-evaluation-arrows",
        "IUT-III.theorem-3.11-output",
        "IUT-III.multiradial-algorithm" ] }

end Audit

end LeanFormal.IUT
