import tmp.sheaf.xif.paper.S2024LocalReciprocityActual
import Mathlib.Topology.Algebra.Group.TopologicalAbelianization
import Mathlib.FieldTheory.Galois.Abelian
import Mathlib.Topology.Algebra.Category.ProfiniteGrp.Completion

/-!
# S2027: the local Artin map for one finite L / Q_p, L^ab as an
intermediate field, and the exact first missing

Layer: **O** (original Theta-link / q-pilot).  Consumer: the S2024 package
(tmp/sheaf/xif/paper/S2024LocalReciprocityActual.lean) and through it the
S2017 package (muQZComparison, muHatComparison) and the [AbsTopIII]
Corollary 1.10 interface of S2000/S2011.

S2024 reduced S2017's two remaining comparison propositions to the datum
LocalReciprocityData p and located its first missing input as (M2a): for
every open subgroup U of G_v = Gal(Qbar_p/Q_p),

  torsion (Abelianization U)  ~=  torsion (FixedField U)^x ,

the levelwise identification (U^ab)_tors = mu(L_U) of local class field
theory, together with (M2b) transfer compatibility and the (M2c)
abstract-vs-profinite caveat.  S2024 recorded that Mathlib (v4.32.2) has no
reciprocity map, no L^ab, and no Gal(L^ab/L) ~= L^x-hat.

This file attacks exactly that item for **one** finite L / Q_p.

## What is constructed and proved here (unconditional, no sorry, no axiom)

1.  **L^ab is no longer missing.**  For U : Index p and L = FixedField U, the
    absolute Galois group of L is localGaloisGroup U = Gal(Qbar_p / L)
    (Mathlib's AlgEquiv), and L^ab is defined as an intermediate field of
    Qbar_p / L:

      maximalAbelianExtension U
        = fixedField (closure of the commutator subgroup of Gal(Qbar_p/L)).

    In particular Gal(L^ab/L) is a genuine, constructed group.

2.  **Gal(L^ab/L) is the profinite abelianization.**  Mathlib's
    TopologicalAbelianization G = G / closure [G,G] is exactly the source's
    (G^ab) (the closed-commutator abelianization).  The infinite Galois
    correspondence gives

      galoisGroupMaximalAbelian U :
        TopologicalAbelianization (localGaloisGroup U) ~= Gal(L^ab / L)

    (InfiniteGalois.normalAutEquivQuotient).  This is the identification
    "Gal(L^ab/L) is the profinite abelianization of Gal(Qbar_p/L), i.e. of U",
    which S2024 recorded as non-existent in the tree.

3.  **L^ab is the maximal abelian extension.**  Every finite abelian extension
    M / L inside Qbar_p (IsAbelianGalois, i.e. finite Galois with commutative
    Galois group) is contained in L^ab
    (le_maximalAbelianExtension_of_isAbelianGalois), and Gal(L^ab/L) is
    commutative (galoisGroupMaximalAbelian_commGroup).  The proof uses the
    kernel of the restriction map Gal(Qbar_p/L) ->* Gal(M/L) being
    M.fixingSubgroup, the inclusion [G,G] <= ker forced by commutativity of
    Gal(M/L), and the closedness of M.fixingSubgroup.

4.  **mu(L).**  mu U = torsion (L^x) is Mathlib's torsion subgroup,
    muInGlobal U : mu U ->* torsion (Qbar_p^x) is injective, and the norm of a
    root of unity is a root of unity (isOfFinOrder_norm,
    isOfFinOrder_norm_fixedField): the mu-side of the norm/transfer
    compatibility (M2b) is well defined.  torsionMulEquiv records that a
    multiplicative equivalence induces an equivalence of torsion subgroups.
    mu(L) is nontrivial (mu_nontrivial: +1 and -1 are roots of unity), so the
    missing identifications are *not* statements about trivial groups.

5.  **The profinite completion exists in Mathlib.**  Contrary to the S2024
    record, Mathlib v4.32.2 *does* contain the profinite completion of a group
    with its universal property (ProfiniteGrp.ProfiniteCompletion).  Hence
    L^x-hat is available (unitProfiniteCompletion, unitToCompletion), and the
    reciprocity isomorphism of local class field theory is *statable*:
    localReciprocityIsomorphism below.  (Mathlib also has
    IsNonarchimedeanLocalField, but no reciprocity/Artin map, no Hilbert
    symbol and no norm limitation theorem.)

## The exact first missing (stated, never assumed, never faked)

After 1-5 the obstruction is *localized* to two statements about the
constructed object L^ab, and one about the transfer.

(M2a) **Local reciprocity for one L/Q_p.**  The local Artin map
     rec_L : L^x -> Gal(L^ab/L) of local class field theory is still absent
     from Mathlib.  After items 1-5 the missing input splits into two
     statements and one torsion form:

     (M2a-core)  localReciprocityIsomorphism U : Nonempty
                   (L^x-hat  ~=  Gal(L^ab/L)),
                 the reciprocity isomorphism itself.  Both sides now exist
                 (item 2 and item 5), so this is statable; it is not provable
                 from Mathlib, which has neither the Artin map nor the local
                 existence theorem nor the norm limitation theorem.

     (M2a-torsion)  the group-theoretic identification
                   torsion (L^x-hat)  ~=  mu(L),
                 which requires the structure of L^x as
                 mu(L) x (pro-p part) x Z; no such decomposition of the units
                 of a local field exists in Mathlib or in the tree.

     (M2a)  localArtinTorsion U : Nonempty (mu U ~= torsion (Gal(L^ab/L))),
            the torsion form needed by S2024.

     The passage (M2a-core) + (M2a-torsion) => (M2a) is *not* formalised here:
     it would require a CommGroup instance on the profinite completion
     (Mathlib's ProfiniteCompletion is a limit of arbitrary finite quotients
     and carries no commutativity instance) together with the structure theory
     of L^x.  Both are recorded, neither is assumed.  (M2a) remains the first
     missing input in dependency order.

(M2c) **Abstract vs. profinite abelianization, now sharp.**  S2011/S2024
     state the levelwise identification on Abelianization U, Mathlib's
     *abstract* abelianization U / [U,U], while the source (and local CFT)
     speak about the *profinite* abelianization
     TopologicalAbelianization U = U / closure [U,U].  Item 2 identifies the
     profinite carrier with Gal(L^ab/L); the remaining comparison is

       profiniteTorsionComparison U : Nonempty
         (torsion (Abelianization U) ~= torsion (TopologicalAbelianization U)).

     There is a canonical surjection
     Abelianization U ->> TopologicalAbelianization U ->> Gal(L^ab/L)
     (abelianizationToTopological, proved here, surjectivity proved), but no
     reason for it to be injective on torsion in general; the comparison is not
     derivable from the tree and is stated as a proposition.  Its canonical
     form is canonicalTorsionComparison U: the induced map on torsion
     subgroups is bijective; the existential form profiniteTorsionComparison
     follows from it (profiniteTorsionComparison_of_bijective).

(M2b) **Transfer/norm compatibility.**  For H <= K the Verlagerung K^ab -> H^ab
     must correspond, under the levelwise identifications, to the inclusion of
     the roots of unity of the two fixed fields.  This is the hypothesis
     htransfer of localReciprocityData_of_source; it is precisely the field
     transfer_compat of S2024's LocalReciprocityData.  It remains a separate
     missing theorem: in local CFT it is the norm-compatibility
     rec_H . N_{L_H/L_K} = V . rec_K of the reciprocity map, again absent.

The reduction proved here makes the dependency order precise:
LocalArtinSourceData p = ((M2a) for all U) + ((M2c) for all U) yields,
together with (M2b), S2024's LocalReciprocityData p
(localReciprocityData_of_source), hence S2011's localReciprocityOnTorsion and
S2017's muQZComparison / muHatComparison (muQZComparison_of_source,
muHatComparison_of_source).  Conversely no statement here is assumed:
LocalArtinSourceData is only ever a hypothesis.

## Not run

Full Project build, target comparator, independent review, and the [AbsTopIII]
H^2 construction.  The local Artin map itself is not constructed: it cannot
be, with the current Mathlib.
-/

set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 800000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.checkUnivs false

noncomputable section
open scoped DirectSum commutatorElement
open LeanFormal.IUT
open LeanFormal.IUT.LocalMLFModelTMPair
open LeanFormal.IUT.XiFPaper.S2000CohomologicalPsiCnsActual
open LeanFormal.IUT.XiFPaper.S2011Cor110bActual
open LeanFormal.IUT.XiFPaper.S2017VerlagerungActual
open LeanFormal.IUT.XiFPaper.S2024LocalReciprocityActual

namespace LeanFormal.IUT.XiFPaper.S2027LocalArtinActual

variable (p : Nat) [Fact (Nat.Prime p)]

/-! ## 1. The local field and its absolute Galois group -/

/-- The finite extension L / Q_p attached to an open subgroup U of
G_v = Gal(Qbar_p/Q_p): L = FixedField U. -/
abbrev localField (U : Index p) : Type :=
  ↥(LocalIntegralUnitKummerInjectivity.FixedField p U)

/-- The absolute Galois group Gal(Qbar_p / L) of the local field L. -/
abbrev localGaloisGroup (U : Index p) : Type :=
  AlgebraicClosure ℚ_[p] ≃ₐ[localField p U] AlgebraicClosure ℚ_[p]

/-- U is the subgroup of G_v fixing its own fixed field. -/
theorem fixingSubgroup_fixedField_eq (U : Index p) :
    (LocalIntegralUnitKummerInjectivity.FixedField p U).fixingSubgroup = U.toSubgroup :=
  InfiniteGalois.fixingSubgroup_fixedField ⟨U.toSubgroup, U.isClosed⟩

/-- **The absolute Galois group of L = FixedField U is U.**  This is the
infinite Galois correspondence: U = Gal(Qbar_p/L). -/
noncomputable def localGaloisGroupEquiv (U : Index p) : ↥U ≃* localGaloisGroup p U :=
  (MulEquiv.subgroupCongr (fixingSubgroup_fixedField_eq p U).symm).trans
    (IntermediateField.fixingSubgroupEquiv
      (LocalIntegralUnitKummerInjectivity.FixedField p U))

/-! ## 2. L^ab as an intermediate field -/

/-- The closure of the commutator subgroup of Gal(Qbar_p/L); a closed normal
subgroup whose fixed field is the maximal abelian extension of L. -/
def commutatorClosed (U : Index p) : ClosedSubgroup (localGaloisGroup p U) :=
  ⟨(commutator (localGaloisGroup p U)).topologicalClosure,
    Subgroup.isClosed_topologicalClosure _⟩

instance commutatorClosed_normal (U : Index p) : (commutatorClosed p U).Normal :=
  Subgroup.is_normal_topologicalClosure (commutator (localGaloisGroup p U))

/-- **L^ab, the maximal abelian extension of L inside Qbar_p**, realised as the
fixed field of the closure of the commutator subgroup of Gal(Qbar_p/L).  This
is a genuine intermediate field of Qbar_p / L; no input of local class field
theory is used in its construction. -/
def maximalAbelianExtension (U : Index p) :
    IntermediateField (localField p U) (AlgebraicClosure ℚ_[p]) :=
  IntermediateField.fixedField (commutator (localGaloisGroup p U)).topologicalClosure

/-- The subgroup of Gal(Qbar_p/L) fixing L^ab is the closed commutator
subgroup. -/
theorem fixingSubgroup_maximalAbelianExtension (U : Index p) :
    (maximalAbelianExtension p U).fixingSubgroup =
      (commutator (localGaloisGroup p U)).topologicalClosure :=
  InfiniteGalois.fixingSubgroup_fixedField (commutatorClosed p U)

/-- **Gal(L^ab/L) is the profinite abelianization of Gal(Qbar_p/L).**

Mathlib's TopologicalAbelianization G is the quotient of G by the closure of
its commutator subgroup, i.e. exactly the source's G^ab.  The infinite Galois
correspondence (InfiniteGalois.normalAutEquivQuotient) identifies the quotient
of Gal(Qbar_p/L) by a closed normal subgroup with the Galois group of the
corresponding fixed field. -/
noncomputable def galoisGroupMaximalAbelian (U : Index p) :
    TopologicalAbelianization (localGaloisGroup p U) ≃*
      Gal(↥(maximalAbelianExtension p U) / localField p U) :=
  InfiniteGalois.normalAutEquivQuotient (commutatorClosed p U)

/-- The Galois group of the maximal abelian extension is commutative: L^ab/L is
abelian.  (The group is a quotient of Gal(Qbar_p/L) by a subgroup containing
the commutator subgroup.) -/
instance galoisGroupMaximalAbelian_commGroup (U : Index p) :
    CommGroup (Gal(↥(maximalAbelianExtension p U) / localField p U)) where
  mul_comm x y := by
    obtain ⟨a, rfl⟩ := (galoisGroupMaximalAbelian p U).surjective x
    obtain ⟨b, rfl⟩ := (galoisGroupMaximalAbelian p U).surjective y
    rw [← map_mul, ← map_mul, mul_comm]
  __ : Group (Gal(↥(maximalAbelianExtension p U) / localField p U)) := inferInstance

/-- **Maximality of L^ab.**  Every finite abelian extension M / L inside
Qbar_p is contained in L^ab.  This is the mathematical content of the name
"maximal abelian extension": the commutator subgroup of Gal(Qbar_p/L) lies in
the kernel of the restriction to Gal(M/L), because Gal(M/L) is commutative. -/
theorem le_maximalAbelianExtension_of_isAbelianGalois (U : Index p)
    (M : IntermediateField (localField p U) (AlgebraicClosure ℚ_[p]))
    [FiniteDimensional (localField p U) M]
    [IsAbelianGalois (localField p U) M] :
    M ≤ maximalAbelianExtension p U := by
  haveI hNormal : Normal (localField p U) M := IsGalois.to_normal
  haveI hcomm : IsMulCommutative (Gal(M / localField p U)) :=
    IsAbelianGalois.toIsMulCommutative
  have hker : (AlgEquiv.restrictNormalHom M).ker = M.fixingSubgroup :=
    IntermediateField.restrictNormalHom_ker M
  have hle : commutator (localGaloisGroup p U) ≤ M.fixingSubgroup := by
    rw [commutator_def, Subgroup.commutator_le]
    intro a _ b _
    have h1 : ⁅a, b⁆ ∈ (AlgEquiv.restrictNormalHom M).ker := by
      rw [MonoidHom.mem_ker]
      have hmap : AlgEquiv.restrictNormalHom M ⁅a, b⁆ =
          ⁅AlgEquiv.restrictNormalHom M a, AlgEquiv.restrictNormalHom M b⁆ :=
        map_commutatorElement _ a b
      rw [hmap]
      exact commutatorElement_eq_one_iff_mul_comm.mpr
        (mul_comm' (AlgEquiv.restrictNormalHom M a) (AlgEquiv.restrictNormalHom M b))
    rwa [hker] at h1
  have hclosed : IsClosed (M.fixingSubgroup : Set (localGaloisGroup p U)) :=
    InfiniteGalois.fixingSubgroup_isClosed M
  have hclosure : (commutator (localGaloisGroup p U)).topologicalClosure ≤ M.fixingSubgroup :=
    Subgroup.topologicalClosure_minimal _ hle hclosed
  rw [maximalAbelianExtension, ← InfiniteGalois.fixedField_fixingSubgroup M]
  exact IntermediateField.fixedField_antitone hclosure

/-- L itself is contained in L^ab. -/
theorem localField_le_maximalAbelianExtension (U : Index p) :
    (⊥ : IntermediateField (localField p U) (AlgebraicClosure ℚ_[p])) ≤
      maximalAbelianExtension p U :=
  bot_le

/-! ## 3. The roots of unity mu(L) and the norm on them -/

/-- **mu(L)**, the group of roots of unity of the local field L, i.e. the
torsion subgroup of L^x.  This is the group identified with torsion (U^ab) by
local reciprocity on torsion. -/
abbrev mu (U : Index p) : Type := CommGroup.torsion (localField p U)ˣ

/-- The roots of unity of L inside the roots of unity of Qbar_p. -/
noncomputable def muInGlobal (U : Index p) :
    mu p U →* CommGroup.torsion (AlgebraicClosure ℚ_[p])ˣ :=
  RationalCircleCyclotome.torsionUnitsMap
    (IntermediateField.val (LocalIntegralUnitKummerInjectivity.FixedField p U)).toRingHom

/-- The roots of unity of L embed in those of Qbar_p. -/
theorem muInGlobal_injective (U : Index p) : Function.Injective (muInGlobal p U) :=
  S2024LocalReciprocityActual.torsionUnitsMap_injective _
    (fun a b hab => Subtype.ext hab)

/-- A multiplicative equivalence of commutative groups induces an equivalence
of their torsion subgroups. -/
noncomputable def torsionMulEquiv {A B : Type*} [CommGroup A] [CommGroup B]
    (e : A ≃* B) : CommGroup.torsion A ≃* CommGroup.torsion B where
  toFun x := ⟨e x, e.toMonoidHom.isOfFinOrder x.2⟩
  invFun y := ⟨e.symm y, e.symm.toMonoidHom.isOfFinOrder y.2⟩
  left_inv x := by ext; simp
  right_inv y := by ext; simp
  map_mul' x y := by ext; simp

/-- **The norm of a root of unity is a root of unity.**  For a field extension
E / F, the norm N_{E/F} carries torsion elements of E to torsion elements of
F.  This makes the mu-side of the norm/transfer compatibility (M2b) well
defined. -/
theorem isOfFinOrder_norm {F E : Type*} [Field F] [Field E] [Algebra F E]
    (u : Eˣ) (hu : IsOfFinOrder u) :
    IsOfFinOrder (Algebra.norm F (u : E)) := by
  obtain ⟨n, hn, hun⟩ := isOfFinOrder_iff_pow_eq_one.mp hu
  refine isOfFinOrder_iff_pow_eq_one.mpr ⟨n, hn, ?_⟩
  have hval : ((u : E) ^ n) = 1 := by
    rw [← Units.val_pow_eq_pow_val u n, hun]
    rfl
  rw [← map_pow, hval, map_one]

/-- The smaller local field L_K = FixedField K as a subfield of
L_H = FixedField H, for H <= K. -/
@[reducible] noncomputable def localFieldAlgebra {H K : Index p} (h : H ≤ K) :
    Algebra (localField p K) (localField p H) :=
  RingHom.toAlgebra (IntermediateField.inclusion (fixedField_le p h)).toRingHom

/-- **Norm compatibility on roots of unity.**  For H <= K the norm N_{L_H/L_K}
carries a root of unity of L_H to a root of unity of L_K.  This is the
field-theoretic half of (M2b); the missing half is the commutativity of the
square with the local Artin map. -/
theorem isOfFinOrder_norm_fixedField {H K : Index p} (h : H ≤ K)
    (u : (localField p H)ˣ) (hu : IsOfFinOrder u) :
    IsOfFinOrder
      (letI : Algebra (localField p K) (localField p H) := localFieldAlgebra p h;
        Algebra.norm (localField p K) (u : localField p H)) := by
  letI : Algebra (localField p K) (localField p H) := localFieldAlgebra p h
  exact isOfFinOrder_norm u hu

/-- **Non-vacuity of mu(L).**  Every local field of characteristic zero contains
the roots of unity +1 and -1, so mu(L) has at least two elements.  Hence the
missing identifications (M2a) are not statements about trivial groups: they
assert a nontrivial isomorphism onto torsion (Gal(L^ab/L)). -/
theorem mu_nontrivial (U : Index p) : Nontrivial (mu p U) := by
  refine ⟨⟨⟨-1, ?_⟩, ⟨1, ?_⟩, ?_⟩⟩
  · rw [CommGroup.mem_torsion, isOfFinOrder_iff_pow_eq_one]
    exact ⟨2, by norm_num, by simp⟩
  · rw [CommGroup.mem_torsion, isOfFinOrder_iff_pow_eq_one]
    exact ⟨1, by norm_num, by simp⟩
  · intro h
    have h1 : (-1 : (localField p U)ˣ) = 1 := congrArg Subtype.val h
    have h2 : (-1 : localField p U) = 1 := congrArg Units.val h1
    have h3 : (2 : localField p U) = 0 := by
      have := congrArg (fun x : localField p U => x + 1) h2
      simpa using this.symm
    exact two_ne_zero h3

/-! ## 4. The two carriers of the abelianization -/

/-- The canonical map from Mathlib's abstract abelianization to the profinite
(topological) abelianization, both quotients of the same group.  It is
surjective (abelianizationToTopological_surjective); whether it is injective
on torsion is exactly the (M2c) comparison. -/
noncomputable def abelianizationToTopological (U : Index p) :
    Abelianization ↥U →* TopologicalAbelianization (localGaloisGroup p U) :=
  Abelianization.lift
    ((QuotientGroup.mk' ((commutator (localGaloisGroup p U)).topologicalClosure)).comp
      (localGaloisGroupEquiv p U).toMonoidHom)

/-- The comparison map is surjective: both sides are quotients of U, and the
abstract commutator subgroup is contained in its closure. -/
theorem abelianizationToTopological_surjective (U : Index p) :
    Function.Surjective (abelianizationToTopological p U) := by
  intro x
  obtain ⟨y, hy⟩ := QuotientGroup.mk'_surjective
    ((commutator (localGaloisGroup p U)).topologicalClosure) x
  obtain ⟨g, rfl⟩ := (localGaloisGroupEquiv p U).surjective y
  exact ⟨Abelianization.of g, hy⟩

/-- The canonical-map form of (M2c): the map induced by
abelianizationToTopological on torsion subgroups is bijective.  This is the
precise content of the comparison; profiniteTorsionComparison is its
"some equivalence exists" weakening. -/
def canonicalTorsionComparison (U : Index p) : Prop :=
  Function.Bijective (torsionMap (abelianizationToTopological p U))

/-- **The profinite completion of L^x.**  Mathlib v4.32.2 *does* contain the
profinite completion of a group together with its universal property
(ProfiniteGrp.ProfiniteCompletion), so the target of the reciprocity
isomorphism is available, contrary to what S2024 recorded. -/
abbrev unitProfiniteCompletion (U : Index p) : Type :=
  ↥(ProfiniteGrp.ProfiniteCompletion.completion (GrpCat.of (localField p U)ˣ))

/-- The canonical map L^x -> L^x-hat. -/
noncomputable def unitToCompletion (U : Index p) :
    (localField p U)ˣ →* unitProfiniteCompletion p U :=
  (ProfiniteGrp.ProfiniteCompletion.eta (GrpCat.of (localField p U)ˣ)).hom

/-! ## 5. The local Artin map: the datum and the exact first missing -/

/-- **(M2a-core): the reciprocity isomorphism of local class field theory**,
for one finite L / Q_p:

  L^x-hat  ~=  Gal(L^ab / L),

where L^x-hat = unitProfiniteCompletion U is Mathlib's profinite completion of
L^x and Gal(L^ab/L) is the group constructed in item 2 above.  This is the
sharpest statement of the first missing input: the target exists (item 2), the
source exists in Mathlib, and what is missing is the isomorphism itself, i.e.
the local Artin map together with its injectivity and surjectivity.  Nothing in
Mathlib constructs it. -/
def localReciprocityIsomorphism (U : Index p) : Prop :=
  Nonempty (unitProfiniteCompletion p U ≃*
    Gal(↥(maximalAbelianExtension p U) / localField p U))

/-- **(M2a): local reciprocity on torsion for one L / Q_p.**

The local Artin map of local class field theory gives an isomorphism
L^x-hat ~= Gal(L^ab/L), hence an identification of the torsion subgroups
mu(L) ~= torsion (Gal(L^ab/L)).  Neither the reciprocity map nor this
identification exists in Mathlib v4.32.2; this proposition is *recorded*, not
assumed, and no inhabitant is fabricated. -/
def localArtinTorsion (U : Index p) : Prop :=
  Nonempty (mu p U ≃*
    CommGroup.torsion (Gal(↥(maximalAbelianExtension p U) / localField p U)))

/-- The same statement, on the profinite abelianization carrier.  Equivalent to
localArtinTorsion through galoisGroupMaximalAbelian. -/
def localArtinTorsionTopological (U : Index p) : Prop :=
  Nonempty (mu p U ≃*
    CommGroup.torsion (TopologicalAbelianization (localGaloisGroup p U)))

theorem localArtinTorsion_iff_topological (U : Index p) :
    localArtinTorsion p U ↔ localArtinTorsionTopological p U := by
  constructor
  · rintro ⟨e⟩
    exact ⟨e.trans (torsionMulEquiv (galoisGroupMaximalAbelian p U)).symm⟩
  · rintro ⟨e⟩
    exact ⟨e.trans (torsionMulEquiv (galoisGroupMaximalAbelian p U))⟩

/-- **(M2c): abstract versus profinite abelianization on torsion.**

S2011/S2024 state the levelwise identification on Mathlib's abstract
Abelianization U = U / [U,U]; the source, and local class field theory (item 2
above), speak about the profinite abelianization
TopologicalAbelianization U = U / closure [U,U].  This proposition is the
precise comparison between the two carriers.  It is not derivable from the
tree: abelianizationToTopological is only known to be surjective. -/
def profiniteTorsionComparison (U : Index p) : Prop :=
  Nonempty (CommGroup.torsion (Abelianization ↥U) ≃*
    CommGroup.torsion (TopologicalAbelianization (localGaloisGroup p U)))

/-- profiniteTorsionComparison in terms of the Galois group of L^ab. -/
theorem profiniteTorsionComparison_iff_galois (U : Index p) :
    profiniteTorsionComparison p U ↔
      Nonempty (CommGroup.torsion (Abelianization ↥U) ≃*
        CommGroup.torsion
          (Gal(↥(maximalAbelianExtension p U) / localField p U))) := by
  constructor
  · rintro ⟨e⟩
    exact ⟨e.trans (torsionMulEquiv (galoisGroupMaximalAbelian p U))⟩
  · rintro ⟨e⟩
    exact ⟨e.trans (torsionMulEquiv (galoisGroupMaximalAbelian p U)).symm⟩

/-- The canonical comparison implies the existential form used in the
reduction. -/
theorem profiniteTorsionComparison_of_bijective (U : Index p)
    (h : canonicalTorsionComparison p U) : profiniteTorsionComparison p U :=
  ⟨MulEquiv.ofBijective (torsionMap (abelianizationToTopological p U)) h⟩

/-- **(M2a)+(M2c) imply S2011's levelwise statement** at one level: the
abstract-carrier identification torsion (Ab U) ~= mu(L) follows from the
source-faithful reciprocity on torsion together with the carrier comparison.
This is the formal reduction; it introduces no assumption. -/
theorem levelwiseLocalReciprocity_of_artin_and_comparison (U : Index p)
    (hartin : localArtinTorsion p U) (hcomp : profiniteTorsionComparison p U) :
    levelwiseLocalReciprocity p U := by
  obtain ⟨eartin⟩ := hartin
  obtain ⟨ecomp⟩ := hcomp
  exact ⟨ecomp.trans
    ((torsionMulEquiv (galoisGroupMaximalAbelian p U)).trans eartin.symm)⟩

/-! ## 6. The source datum and the reduction to S2024/S2017 -/

/-- **The local Artin source datum.**  Exactly the two missing inputs (M2a) and
(M2c), levelwise, in the form needed to produce S2024's LocalReciprocityData
once (M2b) -- the transfer compatibility -- is supplied.  No field of this
structure is inhabited in this file; it is a hypothesis object. -/
structure LocalArtinSourceData : Type where
  /-- (M2a) local reciprocity on torsion, levelwise. -/
  artin : ∀ U : Index p, mu p U ≃*
    CommGroup.torsion (TopologicalAbelianization (localGaloisGroup p U))
  /-- (M2c) comparison of the abstract and the profinite abelianizations on
  torsion, levelwise. -/
  carrier : ∀ U : Index p, CommGroup.torsion (Abelianization ↥U) ≃*
    CommGroup.torsion (TopologicalAbelianization (localGaloisGroup p U))

/-- The levelwise identification torsion (Ab U) ~= mu(L) produced by the source
datum.  This has exactly the shape required by S2024. -/
noncomputable def levelwiseEquiv (d : LocalArtinSourceData p) (U : Index p) :
    CommGroup.torsion (Abelianization ↥U) ≃* mu p U :=
  (d.carrier U).trans (d.artin U).symm

/-- The source datum, together with the transfer compatibility (M2b), produces
S2024's LocalReciprocityData.  The hypothesis htransfer is literally S2024's
transfer_compat field. -/
noncomputable def localReciprocityData_of_source (d : LocalArtinSourceData p)
    (htransfer : ∀ {H K : Index p} (h : H ≤ K)
      (v : CommGroup.torsion (Abelianization K)),
      levelwiseEquiv p d H (torsionMap (verlagerungOpen p h) v) =
        fixedFieldTorsionUnitsInclusion p h (levelwiseEquiv p d K v)) :
    LocalReciprocityData p where
  equiv := levelwiseEquiv p d
  transfer_compat := htransfer

/-- **The source datum gives S2011's local reciprocity on torsion.** -/
theorem localReciprocityOnTorsion_of_source (d : LocalArtinSourceData p) :
    localReciprocityOnTorsion p :=
  fun U => ⟨levelwiseEquiv p d U⟩

/-- **The source datum together with (M2b) gives S2017's muQZComparison.** -/
theorem muQZComparison_of_source (d : LocalArtinSourceData p)
    (htransfer : ∀ {H K : Index p} (h : H ≤ K)
      (v : CommGroup.torsion (Abelianization K)),
      levelwiseEquiv p d H (torsionMap (verlagerungOpen p h) v) =
        fixedFieldTorsionUnitsInclusion p h (levelwiseEquiv p d K v)) :
    muQZComparison p :=
  muQZComparison_of_data p (localReciprocityData_of_source p d htransfer)

/-- **The source datum together with (M2b) gives S2017's muHatComparison.** -/
theorem muHatComparison_of_source (d : LocalArtinSourceData p)
    (htransfer : ∀ {H K : Index p} (h : H ≤ K)
      (v : CommGroup.torsion (Abelianization K)),
      levelwiseEquiv p d H (torsionMap (verlagerungOpen p h) v) =
        fixedFieldTorsionUnitsInclusion p h (levelwiseEquiv p d K v)) :
    muHatComparison p :=
  muHatComparison_of_data p (localReciprocityData_of_source p d htransfer)

/-- The missing datum, as a proposition.  Not proved, not assumed. -/
def localArtinSourceDataMissing : Prop := Nonempty (LocalArtinSourceData p)

/-- The missing datum in particular supplies the levelwise (M2a) statements. -/
theorem localArtinTorsion_of_dataMissing (h : localArtinSourceDataMissing p)
    (U : Index p) : localArtinTorsionTopological p U := by
  obtain ⟨d⟩ := h
  exact ⟨d.artin U⟩

/-! ## 7. Axiom probes -/

#print axioms localGaloisGroupEquiv
#print axioms fixingSubgroup_maximalAbelianExtension
#print axioms galoisGroupMaximalAbelian
#print axioms galoisGroupMaximalAbelian_commGroup
#print axioms le_maximalAbelianExtension_of_isAbelianGalois
#print axioms muInGlobal_injective
#print axioms torsionMulEquiv
#print axioms isOfFinOrder_norm
#print axioms isOfFinOrder_norm_fixedField
#print axioms abelianizationToTopological_surjective
#print axioms mu_nontrivial
#print axioms profiniteTorsionComparison_of_bijective
#print axioms unitToCompletion
#print axioms localArtinTorsion_iff_topological
#print axioms profiniteTorsionComparison_iff_galois
#print axioms levelwiseLocalReciprocity_of_artin_and_comparison
#print axioms localReciprocityOnTorsion_of_source
#print axioms muQZComparison_of_source
#print axioms muHatComparison_of_source
#print axioms localArtinTorsion_of_dataMissing

end LeanFormal.IUT.XiFPaper.S2027LocalArtinActual
