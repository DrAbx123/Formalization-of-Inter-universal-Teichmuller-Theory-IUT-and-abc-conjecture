import tmp.sheaf.xif.paper.S1850RefuteS1756Actual
import tmp.sheaf.xif.paper.S1809SmallCarrierCategoryActual

/-!
# S1882: S1766CoverMapDiscrete and the doubled / terminal cover 2-isomorphism classes

## Question

S1766 isolated the exact residual of raw R2a:

  S1766CoverMapDiscrete :
    forall (A B : S1728Cover) (f g : S1728CoverMap A B),
      S1728CoverMapRel f g -> f = g

where S1728CoverMapRel f g says that the underlying strong transformations of
f and g are 2-isomorphic.  S1766 proved that this is equivalent to raw
injectivity of the canonical identity-point action and that the 2-isomorphism
quotient alone is always small.  S1809 then showed that S1766CoverMapDiscrete
is exactly the missing input for the raw small cover data
S1728SmallRawCoverDataRequired.

S1850 constructed the doubled cover S1850DoubledCover, a legal S1728Cover whose
identity-point presentation is the doubled square with pullback scheme T coprod
T and projection fold, although its source and map are the same as the terminal
cover.  Its identity-point self-endomorphism is fold ; inl, not the identity,
which refutes S1756FirstMissing.

The task is to prove or refute S1766CoverMapDiscrete using the doubled and
terminal covers, and to record whether raw small cover data is feasible, or
else to identify the exact first missing statement.

## Result

1. The doubled cover does not refute S1766CoverMapDiscrete.  In fact
   discreteness holds at every target cover whose source fiber is a
   representable etale stack:

     S1882CoverMapDiscreteAtTarget B, for B.source.fiber = S1742YS S.

   The key new lemma is S1882StrongTrans_eq_of_modification: for a
   representable target stack Y S, any modification eta -> theta between
   strong transformations into Y S forces eta = theta.  No hypothesis on the
   source stack is used.  Hence the hom category of strong transformations into
   a representable stack is discrete, so two 2-isomorphic cover maps with such
   a target are equal.  This is applied to the terminal cover and to the
   doubled cover:

     S1882TerminalCover_targetDiscrete
     S1882DoubledCover_targetDiscrete
     S1882TerminalCover_rel_iff
     S1882DoubledCover_rel_iff

   In particular the 2-isomorphism relation on hom types into the doubled or
   terminal cover is literally equality; there is no non-trivial 2-iso class
   there.  This is compatible with S1850End_ne: the failure of the unit 2-cell
   of the doubled presentation is not a 2-isomorphism between two distinct
   cover maps.  The two facts are recorded together in
   S1882DoubledCover_structure.

2. Raw small cover data is feasible, unconditionally, for these targets:

     S1882RawSmallDataTerminal : forall A, Nonempty (S1728ActualSmallRawCoverData A terminal)
     S1882RawSmallDataDoubled  : forall A, Nonempty (S1728ActualSmallRawCoverData A doubled)

   The carrier is the Type-0 S1766QuotSmallCarrier; the equivalence is obtained
   from the quotient equivalence S1882QuotEquivRawOfTargetDiscrete composed
   with S1766QuotSmallEquiv.

3. The residual for the universal statement is exactly target-local
   discreteness.  S1882CoverMapDiscrete_iff_targets decomposes
   S1766CoverMapDiscrete as

     forall B, S1882CoverMapDiscreteAtTarget B,

   and S1882FirstMissing is exactly this target-local form.  A precise
   sufficient geometric input is

     S1882AllTargetsSourceRepresentable :
       forall B : S1728Cover, exists S, B.source.fiber = S1742YS S,

   which implies S1766CoverMapDiscrete
   (S1882AllTargetsSourceRepresentable_implies_discrete) and hence, through
   S1809, the raw small cover data
   (S1882RawSmallCoverDataRequired_of_sourceRepresentable).  The present file
   constructs no cover beyond the terminal and doubled ones, and the generic
   pullback/coherence constructions leave their non-representable-source
   covers conditional on data.  Any actual counterexample must target a cover
   whose source fiber is not representable
   (S1882Counterexample_target_notSourceRepresentable); in particular neither
   the terminal nor the doubled cover can be the target of a counterexample
   (S1882NoCounterexampleAtDoubledOrTerminal).

No sorry, no new axiom, no Shrink/ULift/PUnit, and no fake data.  The only
axioms used are propext, Classical.choice and Quot.sound; see the audit block
at the end.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 1000000

namespace LeanFormal.IUT.XiFPaper.S1882CoverMapDiscreteActual

open CategoryTheory
open CategoryTheory.Bicategory
open scoped Pseudofunctor.StrongTrans
open AlgebraicGeometry
open Iut
open LeanFormal.IUT.XiFPaper.S1726OrbicurveFPrimeActual
open LeanFormal.IUT.XiFPaper.S1728CoverCategoryActual
open LeanFormal.IUT.XiFPaper.S1728CoverCategoryActual.S1728Paper
open LeanFormal.IUT.XiFPaper.S1733EssentiallySmallCoversActual
open LeanFormal.IUT.XiFPaper.S1742TwoYonedaActual
open LeanFormal.IUT.XiFPaper.S1743CoverSliceActual
open LeanFormal.IUT.XiFPaper.S1744Category01AssemblyActual
open LeanFormal.IUT.XiFPaper.S1756CoverSourceRepresentabilityActual
open LeanFormal.IUT.XiFPaper.S1766CanonicalModelInjectivityActual
open LeanFormal.IUT.XiFPaper.S1809SmallCarrierCategoryActual
open LeanFormal.IUT.XiFPaper.S1839SliceFillingActual
open LeanFormal.IUT.XiFPaper.S1850RefuteS1756Actual

/-- An isomorphism type is a subsingleton whenever its hom type is. -/
local instance S1882IsoSubsingletonOfHomSubsingleton {C : Type*} [Category C]
    {X Y : C} [Subsingleton (X ⟶ Y)] : Subsingleton (X ≅ Y) where
  allEq e1 e2 := by
    apply Iso.ext
    exact Subsingleton.elim _ _

/-- 2-cells between morphisms of etale stacks with discrete target are
subsingletons, with no hypothesis on the source. -/
local instance S1882CatHom₂Subsingleton {C D : Cat} [IsDiscrete (↑D)]
    (phi psi : C ⟶ D) : Subsingleton (phi ⟶ psi) := by
  constructor
  intro a b
  apply Cat.Hom₂.ext
  apply CategoryTheory.NatTrans.ext
  funext X
  exact Subsingleton.elim _ _

/-- A natural transformation between functors into a discrete category forces
the two functors to be equal. -/
theorem S1882Functor_eq_of_natTrans_discrete {C D : Type*} [Category C] [Category D]
    [IsDiscrete D] {F G : C ⥤ D} (tau : F ⟶ G) : F = G := by
  refine CategoryTheory.Functor.ext (fun X => IsDiscrete.eq_of_hom (tau.app X)) ?_
  intro X Y f
  exact Subsingleton.elim _ _


/-- **Any modification into a representable etale stack forces equality of the
strong transformations.** -/
theorem S1882StrongTrans_eq_of_modification_representableTarget
    {W : EtaleStackPseudofunctor S1726K} {S : SchemeOverField S1726K}
    (eta theta : Pseudofunctor.StrongTrans W (S1742YS (F := S1726K) S))
    (h : ∀ a, eta.app a = theta.app a) : eta = theta := by
  haveI : ∀ U : LocallyDiscrete (SchemeOverField S1726K)ᵒᵖ,
      IsDiscrete (↑((S1742YS (F := S1726K) S).obj U)) := by
    intro U
    change IsDiscrete (Discrete (Opposite.unop U.as ⟶ S))
    infer_instance
  cases eta with
  | mk app nat natn natid natcomp =>
    cases theta with
    | mk app' nat' natn' natid' natcomp' =>
      simp only at h
      have h' : app = app' := funext h
      subst h'
      congr 1
      funext a b f
      exact Subsingleton.elim _ _

/-- The componentwise computation behind the previous theorem. -/
theorem S1882App_eq_of_modification
    {W : EtaleStackPseudofunctor S1726K} {S : SchemeOverField S1726K}
    {eta theta : Pseudofunctor.StrongTrans W (S1742YS (F := S1726K) S)}
    (e : eta ⟶ theta) : ∀ a, eta.app a = theta.app a := by
  haveI : ∀ U : LocallyDiscrete (SchemeOverField S1726K)ᵒᵖ,
      IsDiscrete (↑((S1742YS (F := S1726K) S).obj U)) := by
    intro U
    change IsDiscrete (Discrete (Opposite.unop U.as ⟶ S))
    infer_instance
  intro U
  apply Cat.Hom.ext
  exact S1882Functor_eq_of_natTrans_discrete
    (F := (eta.app U).toFunctor) (G := (theta.app U).toFunctor)
    (e.as.app U).toNatTrans

/-- **The main discreteness lemma.** -/
theorem S1882StrongTrans_eq_of_modification
    {W : EtaleStackPseudofunctor S1726K} {S : SchemeOverField S1726K}
    {eta theta : Pseudofunctor.StrongTrans W (S1742YS (F := S1726K) S)}
    (e : eta ⟶ theta) : eta = theta :=
  S1882StrongTrans_eq_of_modification_representableTarget eta theta
    (S1882App_eq_of_modification e)

/-- Sharp form: for a representable target, two strong transformations are
2-isomorphic iff they are equal. -/
theorem S1882StrongTrans_iso_iff
    {W : EtaleStackPseudofunctor S1726K} {S : SchemeOverField S1726K}
    (eta theta : Pseudofunctor.StrongTrans W (S1742YS (F := S1726K) S)) :
    Nonempty (eta ≅ theta) ↔ eta = theta := by
  constructor
  · rintro ⟨e⟩
    exact S1882StrongTrans_eq_of_modification e.hom
  · intro h
    exact ⟨h ▸ Iso.refl eta⟩

/-- The same statement for a target stack that is only equal to a
representable stack. -/
theorem S1882StrongTrans_eq_of_modification_targetEq
    {W T : EtaleStackPseudofunctor S1726K} {S : SchemeOverField S1726K}
    (hT : T = S1742YS (F := S1726K) S)
    {eta theta : Pseudofunctor.StrongTrans W T}
    (e : eta ⟶ theta) : eta = theta := by
  subst hT
  exact S1882StrongTrans_eq_of_modification e

/-- **Target-local discreteness.** -/
theorem S1882CoverMapDiscrete_of_targetEq
    (A B : S1728Cover) (S : SchemeOverField S1726K)
    (hB : B.source.fiber = S1742YS (F := S1726K) S)
    (f g : S1728CoverMap A B) (h : S1728CoverMapRel f g) : f = g := by
  apply S1766_coverMap_ext A B
  let T := B.source.fiber
  have hT : T = S1742YS (F := S1726K) S := hB
  have e : f.map ⟶ g.map := h.some.hom
  exact S1882StrongTrans_eq_of_modification_targetEq (W := A.source.fiber) (T := T) hT e

/-- The target-local form of S1766CoverMapDiscrete. -/
def S1882CoverMapDiscreteAtTarget (B : S1728Cover) : Prop :=
  ∀ (A : S1728Cover) (f g : S1728CoverMap A B),
    S1728CoverMapRel f g → f = g

/-- Sufficient structural form: the strong-transformation hom category of the
target source is discrete. -/
def S1882TargetStackDiscrete (B : S1728Cover) : Prop :=
  ∀ (W : EtaleStackPseudofunctor S1726K)
    (eta theta : Pseudofunctor.StrongTrans W B.source.fiber),
    Nonempty (eta ⟶ theta) → eta = theta

/-- The target source fiber is representable. -/
def S1882TargetSourceRepresentable (B : S1728Cover) : Prop :=
  ∃ S : SchemeOverField S1726K, B.source.fiber = S1742YS (F := S1726K) S

/-- Representability of the target source implies stack discreteness. -/
theorem S1882TargetStackDiscrete_of_sourceRepresentable
    (B : S1728Cover) (hB : S1882TargetSourceRepresentable B) :
    S1882TargetStackDiscrete B := by
  obtain ⟨S, hS⟩ := hB
  intro W eta theta hmod
  obtain ⟨e⟩ := hmod
  let T := B.source.fiber
  have hT : T = S1742YS (F := S1726K) S := hS
  exact S1882StrongTrans_eq_of_modification_targetEq (W := W) (T := T) hT e

/-- Stack discreteness implies target-local cover-map discreteness. -/
theorem S1882CoverMapDiscreteAtTarget_of_stackDiscrete
    (B : S1728Cover) (hB : S1882TargetStackDiscrete B) :
    S1882CoverMapDiscreteAtTarget B := by
  intro A f g hrel
  apply S1766_coverMap_ext A B
  obtain ⟨e⟩ := hrel
  exact hB A.source.fiber f.map g.map ⟨e.hom⟩

/-- Representability of the target source gives target-local discreteness. -/
theorem S1882CoverMapDiscreteAtTarget_of_sourceRepresentable
    (B : S1728Cover) (hB : S1882TargetSourceRepresentable B) :
    S1882CoverMapDiscreteAtTarget B :=
  S1882CoverMapDiscreteAtTarget_of_stackDiscrete B
    (S1882TargetStackDiscrete_of_sourceRepresentable B hB)



/-! ## 3. The terminal and doubled covers -/

/-- The terminal cover's source fiber is the representable stack of the affine
base. -/
theorem S1882TerminalCover_sourceRepresentable :
    S1882TargetSourceRepresentable S1839TerminalCover :=
  ⟨S1726AffineOver, rfl⟩

/-- The doubled cover has the same source as the terminal cover, hence its
source fiber is the representable stack of the affine base.  This is the point
that rules out the doubled cover as a counterexample: its model is doubled, but
its source stack is representable. -/
theorem S1882DoubledCover_sourceRepresentable :
    S1882TargetSourceRepresentable S1850DoubledCover :=
  ⟨S1726AffineOver, rfl⟩

/-- **The doubled cover does not refute S1766CoverMapDiscrete.** -/
theorem S1882DoubledCover_targetDiscrete :
    S1882CoverMapDiscreteAtTarget S1850DoubledCover :=
  S1882CoverMapDiscreteAtTarget_of_sourceRepresentable _
    S1882DoubledCover_sourceRepresentable

/-- The same statement for the terminal cover. -/
theorem S1882TerminalCover_targetDiscrete :
    S1882CoverMapDiscreteAtTarget S1839TerminalCover :=
  S1882CoverMapDiscreteAtTarget_of_sourceRepresentable _
    S1882TerminalCover_sourceRepresentable

/-- Explicit form: 2-isomorphic cover maps into the doubled cover are equal. -/
theorem S1882DoubledCover_discrete (A : S1728Cover)
    (f g : S1728CoverMap A S1850DoubledCover)
    (h : S1728CoverMapRel f g) : f = g :=
  S1882DoubledCover_targetDiscrete A f g h

/-- Explicit form for the terminal cover. -/
theorem S1882TerminalCover_discrete (A : S1728Cover)
    (f g : S1728CoverMap A S1839TerminalCover)
    (h : S1728CoverMapRel f g) : f = g :=
  S1882TerminalCover_targetDiscrete A f g h

/-- At the doubled target the 2-isomorphism relation is exactly equality. -/
theorem S1882DoubledCover_rel_iff (A : S1728Cover)
    (f g : S1728CoverMap A S1850DoubledCover) :
    S1728CoverMapRel f g ↔ f = g :=
  ⟨S1882DoubledCover_discrete A f g, fun h => h ▸ S1728CoverMapRel_refl f⟩

/-- At the terminal target the 2-isomorphism relation is exactly equality. -/
theorem S1882TerminalCover_rel_iff (A : S1728Cover)
    (f g : S1728CoverMap A S1839TerminalCover) :
    S1728CoverMapRel f g ↔ f = g :=
  ⟨S1882TerminalCover_discrete A f g, fun h => h ▸ S1728CoverMapRel_refl f⟩

/-- The essential diagnosis: the doubled cover has a representable source (hence
discrete raw hom types) even though its chosen identity-point self-endomorphism
is not the identity.  The failure of the unit 2-cell of S1850 is therefore not
a 2-isomorphism between distinct cover maps. -/
theorem S1882DoubledCover_structure :
    S1882TargetSourceRepresentable S1850DoubledCover ∧
      S1756End S1850DoubledCover ≠ 𝟙 (S1733Model S1850DoubledCover) :=
  ⟨S1882DoubledCover_sourceRepresentable, S1850End_ne⟩

/-! ## 4. Raw small cover data at the constructed targets -/

/-- Under target-local discreteness the 2-isomorphism quotient is equivalent to
the raw cover maps. -/
noncomputable def S1882QuotEquivRawOfTargetDiscrete
    (B : S1728Cover) (hB : S1882CoverMapDiscreteAtTarget B) (A : S1728Cover) :
    Quot (fun f g : S1728CoverMap A B => S1728CoverMapRel f g) ≃
      S1728CoverMap A B where
  toFun := Quot.lift id (fun f g hrel => hB A f g hrel)
  invFun := Quot.mk _
  left_inv q := by
    induction q using Quot.inductionOn with
    | h f => rfl
  right_inv f := rfl

/-- The Type-0 raw small cover datum for a target on which the 2-isomorphism
relation is equality. -/
noncomputable def S1882RawSmallDataOfTargetDiscrete
    (B : S1728Cover) (hB : S1882CoverMapDiscreteAtTarget B) (A : S1728Cover) :
    S1728ActualSmallRawCoverData A B where
  Carrier := S1766QuotSmallCarrier A B
  equiv := (S1766QuotSmallEquiv A B).symm.trans
    (S1882QuotEquivRawOfTargetDiscrete B hB A)

/-- **Raw small cover data is feasible for the terminal target.** -/
theorem S1882RawSmallDataTerminal (A : S1728Cover) :
    Nonempty (S1728ActualSmallRawCoverData A S1839TerminalCover) :=
  ⟨S1882RawSmallDataOfTargetDiscrete S1839TerminalCover
    S1882TerminalCover_targetDiscrete A⟩

/-- **Raw small cover data is feasible for the doubled target.** -/
theorem S1882RawSmallDataDoubled (A : S1728Cover) :
    Nonempty (S1728ActualSmallRawCoverData A S1850DoubledCover) :=
  ⟨S1882RawSmallDataOfTargetDiscrete S1850DoubledCover
    S1882DoubledCover_targetDiscrete A⟩

/-! ## 5. The exact residual of the universal statement -/

/-- **Decomposition of S1766CoverMapDiscrete.** -/
theorem S1882CoverMapDiscrete_iff_targets :
    S1766CoverMapDiscrete ↔ ∀ B, S1882CoverMapDiscreteAtTarget B := by
  constructor
  · intro h B A f g hrel
    exact h A B f g hrel
  · intro h A B f g hrel
    exact h B A f g hrel

/-- The exact first missing statement, in target-local form. -/
def S1882FirstMissing : Prop := ∀ B : S1728Cover, S1882CoverMapDiscreteAtTarget B

/-- The target-local form is exactly S1766's residual. -/
theorem S1882FirstMissing_iff_S1766 : S1882FirstMissing ↔ S1766CoverMapDiscrete :=
  S1882CoverMapDiscrete_iff_targets.symm

/-- The sufficient geometric input: every cover source fiber is representable. -/
def S1882AllTargetsSourceRepresentable : Prop :=
  ∀ B : S1728Cover, S1882TargetSourceRepresentable B

/-- Source representability gives stack discreteness at every target. -/
theorem S1882AllTargetsStackDiscrete_of_sourceRepresentable
    (h : S1882AllTargetsSourceRepresentable) :
    ∀ B : S1728Cover, S1882TargetStackDiscrete B :=
  fun B => S1882TargetStackDiscrete_of_sourceRepresentable B (h B)

/-- **The sufficient geometric input proves S1766CoverMapDiscrete.** -/
theorem S1882AllTargetsSourceRepresentable_implies_discrete
    (h : S1882AllTargetsSourceRepresentable) : S1766CoverMapDiscrete :=
  S1882CoverMapDiscrete_iff_targets.mpr fun B =>
    S1882CoverMapDiscreteAtTarget_of_stackDiscrete B
      (S1882TargetStackDiscrete_of_sourceRepresentable B (h B))

/-- Consequently it gives the raw small cover data required by S1728 through
the S1809 reduction. -/
theorem S1882RawSmallCoverDataRequired_of_sourceRepresentable
    (h : S1882AllTargetsSourceRepresentable) : S1728SmallRawCoverDataRequired :=
  S1809SmallRawCoverDataRequired_of_firstMissing
    (S1882AllTargetsSourceRepresentable_implies_discrete h)

/-- Any actual counterexample to raw R2a must target a cover whose source fiber
is not representable. -/
theorem S1882Counterexample_target_notSourceRepresentable
    (h : S1766ActualCounterexample) :
    ∃ B : S1728Cover, ¬ S1882TargetSourceRepresentable B := by
  obtain ⟨A, B, f, g, hne, hrel⟩ := h
  refine ⟨B, ?_⟩
  intro hB
  exact hne (S1882CoverMapDiscreteAtTarget_of_sourceRepresentable B hB A f g hrel)

/-- The constructed targets are not counterexamples. -/
theorem S1882NoCounterexampleAtDoubledOrTerminal :
    S1882CoverMapDiscreteAtTarget S1850DoubledCover ∧
      S1882CoverMapDiscreteAtTarget S1839TerminalCover :=
  ⟨S1882DoubledCover_targetDiscrete, S1882TerminalCover_targetDiscrete⟩



/-! ## 6. Checks and axiom audit -/

#check S1882Functor_eq_of_natTrans_discrete
#check S1882StrongTrans_eq_of_modification_representableTarget
#check S1882StrongTrans_eq_of_modification
#check S1882StrongTrans_iso_iff
#check S1882StrongTrans_eq_of_modification_targetEq
#check S1882CoverMapDiscrete_of_targetEq
#check S1882CoverMapDiscreteAtTarget
#check S1882TargetStackDiscrete
#check S1882TargetSourceRepresentable
#check S1882CoverMapDiscreteAtTarget_of_sourceRepresentable
#check S1882TerminalCover_sourceRepresentable
#check S1882DoubledCover_sourceRepresentable
#check S1882DoubledCover_targetDiscrete
#check S1882TerminalCover_targetDiscrete
#check S1882DoubledCover_discrete
#check S1882TerminalCover_discrete
#check S1882DoubledCover_rel_iff
#check S1882TerminalCover_rel_iff
#check S1882DoubledCover_structure
#check S1882QuotEquivRawOfTargetDiscrete
#check S1882RawSmallDataOfTargetDiscrete
#check S1882RawSmallDataTerminal
#check S1882RawSmallDataDoubled
#check S1882CoverMapDiscrete_iff_targets
#check S1882FirstMissing
#check S1882FirstMissing_iff_S1766
#check S1882AllTargetsSourceRepresentable
#check S1882AllTargetsStackDiscrete_of_sourceRepresentable
#check S1882AllTargetsSourceRepresentable_implies_discrete
#check S1882RawSmallCoverDataRequired_of_sourceRepresentable
#check S1882Counterexample_target_notSourceRepresentable
#check S1882NoCounterexampleAtDoubledOrTerminal

#print axioms S1882Functor_eq_of_natTrans_discrete
#print axioms S1882StrongTrans_eq_of_modification_representableTarget
#print axioms S1882StrongTrans_eq_of_modification
#print axioms S1882StrongTrans_iso_iff
#print axioms S1882CoverMapDiscrete_of_targetEq
#print axioms S1882CoverMapDiscreteAtTarget_of_sourceRepresentable
#print axioms S1882TerminalCover_sourceRepresentable
#print axioms S1882DoubledCover_sourceRepresentable
#print axioms S1882DoubledCover_targetDiscrete
#print axioms S1882TerminalCover_targetDiscrete
#print axioms S1882DoubledCover_rel_iff
#print axioms S1882TerminalCover_rel_iff
#print axioms S1882DoubledCover_structure
#print axioms S1882QuotEquivRawOfTargetDiscrete
#print axioms S1882RawSmallDataOfTargetDiscrete
#print axioms S1882RawSmallDataTerminal
#print axioms S1882RawSmallDataDoubled
#print axioms S1882CoverMapDiscrete_iff_targets
#print axioms S1882FirstMissing_iff_S1766
#print axioms S1882AllTargetsSourceRepresentable_implies_discrete
#print axioms S1882RawSmallCoverDataRequired_of_sourceRepresentable
#print axioms S1882Counterexample_target_notSourceRepresentable
#print axioms S1882NoCounterexampleAtDoubledOrTerminal


end LeanFormal.IUT.XiFPaper.S1882CoverMapDiscreteActual
