import Mathlib.Algebra.Category.Grp.FiniteGrp
import Mathlib.FieldTheory.Galois.Profinite
import Mathlib.GroupTheory.GroupExtension.Basic
import Mathlib.NumberTheory.Padics.PadicNumbers
import Mathlib.Topology.Algebra.Category.ProfiniteGrp.Basic
import Mathlib.Topology.Algebra.ContinuousMonoidHom
import Iut.Foundations.SourceContinuousAnabelioid
import LeanFormal.IUT.IUTII.Frobenioid.PrimeStripFrobenioidCategorySkeleton
import LeanFormal.IUT.IUTI.HodgeTheater.LocalPrimePlaces

/-!
# Etale-pi-one geometric-kernel realization for local D-prime-strips (reduced anabelioid layer)

Source anchor: IUT II, Sections 3-6, boundary item (1) of the prime-strip
Frobenioid category contract; consumers IUT III, Proposition 3.5 / Theorem
3.11(ii) and the vertical log-Kummer / K1-K2 inputs.  The frozen interface is
the obligation LeanFormal.IUT.Audit.geometricPiOneBoundary
(Foundations/NumberField/PlaceCompletionCarrier.lean:287), whose note records
that the geometric fundamental group of the base curve is not constructed.

## What the source boundary item demands

For a smooth, proper, geometrically connected curve X over a number field (or
local field) K with a geometric base point, the etale fundamental group
pi_1^et(X) is a profinite group which surjects onto the absolute Galois group
Gal(Kbar/K), and the kernel of that functorial surjection is the geometric
fundamental group pi_1^geo = pi_1^et(X x_K Kbar).  A local D-prime-strip has to
realize its projection with this kernel:

  DPrimeStrip.proj : Pi v = pi_1^et(X) --> Gal(Kbar/K) = G v,
  DPrimeStrip.geometric v = (DPrimeStrip.proj v).ker = pi_1^geo.

## What is in the tree, and what is not

The concrete local D-prime-strips of IUTI/HodgeTheater/LocalPrimePlaces.lean use
the actual local absolute Galois group Gal(Qbar_p/Q_p) on both sides and the
*identity* projection; hence their geometric kernel is trivial.  This is
evaluated in Theorem311/PrimeStripFrobenioidCategorySkeleton.lean
(localDPrimeStrip_geometric_eq_bot, cited and reused below).

Mathlib 4.32.2 has no smooth proper geometrically connected curve, no etale
fundamental group of a curve, and no geometric base point, so the source group
pi_1^geo cannot be built from Mathlib.  The existing anabelioid machinery
(Iut/Foundations/SourceAnabelioid.lean, SourceContinuousAnabelioid.lean, and the
semi-graph/anabelioid files it builds on) does supply:
* the structure Iut.EtaleFundamentalGroup: a Galois category of finite etale
  covers with a chosen fiber functor, a profinite group, and Mathlib's
  PreGaloisCategory.IsFundamentalGroup certificate;
* the construction Iut.continuousActionEtaleFundamentalGroup G = B(G), the
  connected anabelioid of finite continuous G-sets, whose certified
  fundamental group is definitionally G;
* for every continuous morphism f : H --> K of profinite groups, the pointed
  anabelioid morphism Iut.continuousActionPointedHom f : B(H) --> B(K), whose
  induced map on certified fundamental groups is f.
It does NOT supply a functor curve |-> anabelioid, so a curve's pi_1^et cannot
be obtained from it.

## What this file proves

1. The actual local absolute Galois group as a profinite group:
   localAbsoluteGaloisProfinite p = InfiniteGalois.profiniteGalGrp Q_p (AlgebraicClosure Q_p),
   with underlying type definitionally equal to the LocalAbsoluteGalois p used
   by the concrete local strips (localAbsoluteGaloisProfinite_coe, and the
   place-indexed localAbsoluteGaloisProfiniteAt_coe).
2. A reduced geometric kernel model reducedGeometricKernelModel = Z/2 (a
   profinite cyclic group of order two), and the reduced total group
   localAnabelioidTotalGroup p = Gal(Qbar_p/Q_p) x Z/2, together with the
   genuine continuous first projection localAnabelioidProjection p.  The kernel
   of this projection is multiplicatively equivalent to the reduced model
   (localAnabelioidProjection_kerMulEquiv), and the projection is surjective.
3. The anabelioid realization: localGeometricAnabelioid p = B(Gal(Qbar_p/Q_p)),
   localTotalAnabelioid p = B(localAnabelioidTotalGroup p), and the pointed
   anabelioid morphism localAnabelioidMorphism p induced by the projection.
   The induced map on certified fundamental groups is proved to be the
   projection itself (localAnabelioidMorphism_fundamentalGroup_apply), and it is
   surjective, so the reduced strip is not faked through an abstract transport.
4. The place-indexed local anabelioid D-prime-strip
   localAnabelioidDPrimeStrip : DPrimeStrip RationalPrimePlace, whose Pi and G
   are the certified fundamental groups of the two anabelioids and whose
   projection is the induced map on certified fundamental groups.  At every
   rational prime place:
   * the Galois group G v is the *same type* as the fundamental group of the
     concrete local strip (localAnabelioidDPrimeStrip_G_eq_concretePi);
   * the geometric kernel equals the kernel of the genuine projection
     (localAnabelioidDPrimeStrip_geometric_eq_projectionKernel);
   * the geometric kernel is multiplicatively equivalent to Z/2
     (localAnabelioidDPrimeStrip_geometricMulEquiv), is nontrivial
     (localAnabelioidDPrimeStrip_geometric_ne_bot, with an explicit nontrivial
     element) and has cardinality two
     (localAnabelioidDPrimeStrip_geometric_card).
5. The obstruction that rules out the identity-projection substitute: the
   geometric kernel of any D-prime-strip is trivial exactly when its projection
   is injective (geometric_eq_bot_iff_injective); consequently an identity or
   injective projection can never realize a nontrivial geometric fundamental
   group (ker_eq_bot_of_hom_eq_id, not_forall_injective_of_nontrivial_geometric_kernel).
   The concrete local strip of LocalPrimePlaces has the identity projection
   (concreteLocalDPrimeStrip_proj_eq_id) and no nontrivial geometric kernel
   (concreteLocalDPrimeStrip_not_hasNontrivialGeometricKernel), and it is not
   equivalent as a D-prime-strip to the anabelioid realization
   (no_stripEquiv_concreteLocalStrip_anabelioid, using the transfer theorem
   geometric_eq_bot_of_stripEquiv).

## Honest boundary: what is NOT proved here

* The reduced model Z/2 is a *parameter* of the construction; it is NOT claimed
  to be the geometric fundamental group of a curve.  No curve, no etale
  fundamental group of a curve, and no geometric base point are constructed.
* The exact missing source construction is: (i) a concrete smooth, proper,
  geometrically connected curve X over K with a geometric base point; (ii) its
  etale fundamental group as an anabelioid, identified with a B(G); (iii) the
  functorial surjection onto Gal(Kbar/K) with kernel the curve's pi_1^geo, and
  the identification of this exact sequence with a D-prime-strip.  None of
  (i)-(iii) exists in Mathlib 4.32.2 or in this tree: the anabelioid API builds
  B(G) only from an already given profinite G, and no curve-to-anabelioid
  functor is available.  Therefore boundary item (1) is NOT discharged here;
  this file supplies the reduced anabelioid realization of the exact-sequence
  shape and the formal obstruction of the identity-projection model.
* Why no identity-projection substitute is allowed: DPrimeStrip.geometric is
  defined as the kernel of the projection, so an identity (or merely injective)
  projection forces the geometric kernel to be trivial; the source demands the
  nontrivial arithmetic group pi_1^geo.  This is not a convention that could be
  repaired by renaming: the formal statements above show that any strip with
  identity projection is trivial-kernel and is not equivalent to a strip with a
  nontrivial geometric kernel.
* No theta / q-pilot / Tate claims are made; no arithmetic degree or log-volume
  statement is used or claimed.

## Additions (Layer-1 build, 2026-10-20): semidirect strip and anabelioid assignment

Section 9 replaces the split direct-product shape by the genuine *semidirect*
realization of the exact sequence.  For an abstract group `G`, a group `N` and
an action `φ : G →* MulAut N`:

* `semidirectDPrimeStrip φ` is a D-prime-strip whose local group is the
  semidirect product `N ⋊[φ] G`, whose arithmetic group is `G`, and whose
  projection is the canonical `SemidirectProduct.rightHom`;
* `semidirectGeometricMulEquiv` identifies the geometric kernel with `N`, so the
  kernel is a `G`-module and not an unrelated second group;
* `semidirectDPrimeStrip_geometric_nontrivial` and
  `semidirectDPrimeStrip_geometric_card` transfer nontriviality and cardinality
  of `N` to the kernel, and `semidirectDPrimeStrip_hasNontrivialGeometricKernel`
  records the resulting nontrivial-kernel property;
* `semidirectGeometric_conj` proves that conjugation by the arithmetic part is
  exactly the given action: this is the module structure that the source
  requires of the geometric fundamental group;
* `semidirectDPrimeStrip_quotientGeometricMulEquiv` identifies the quotient by
  the geometric kernel with `G` (the mono-analytic quotient is `G` itself, not a
  cardinality placeholder);
* `semidirectAffineMulAction` is the affine action of the total group on the
  geometric fiber, `semidirectAffineAction_exists_smul_eq` proves that the
  translation part is transitive (the fiber is a torsor),
  `semidirectAffineAction_inl_injective` proves that it acts freely, and
  `semidirectAffineOrbitSetoid_subsingleton` proves that the explicit orbit
  equivalence relation has a single class.

Section 10 constructs the anabelioid-to-strip assignment.  `DPrimeStripHom`
packages compatible morphisms of D-prime-strips with the projection
commutation law `DPrimeStripHom.compat_apply`.
`anabelioidDPrimeStripOf φ hφ` turns a pointed anabelioid morphism whose induced
map on certified fundamental groups is surjective into a D-prime-strip indexed
by `Unit`: its local group is the certified fundamental group of the source
anabelioid, its arithmetic group that of the target, and its projection the
induced morphism.  Its domain is the connected anabelioids with pointed exact
morphisms, its codomain the D-prime-strips with `DPrimeStripHom`, and it is
functorial: `anabelioidDPrimeStripOf_proj_identity` states the identity law,
reusing `SourcePointedAnabelioidHom.fundamentalGroupHom_identity`, and
`anabelioidDPrimeStripOf_continuousActionPointedHom` computes the assignment on
the concrete restriction morphisms `B(H) -> B(K)` as the given group morphism.
A bundled `CategoryTheory.Functor` is not declared, because the surjectivity
hypothesis is a proof field of the assignment and not a morphism property of
`SourcePointedAnabelioidHom`.  The composition law on arbitrary pointed
morphisms is not stated here either: passing the composite surjectivity
hypothesis and rewriting through `fundamentalGroupHom_comp` requires unfolding
the categorical composite `SourcePointedAnabelioidHom.comp`, which exceeds the
elaboration budget of this module.  The unidentified part is unchanged:
no curve-to-anabelioid functor and no curve `pi_1` are constructed, so applying
the assignment to the concrete local anabelioid gives only the arithmetic
`B(Gal)`-strip, and the geometric strip is supplied only through the abstract
module `N` of Section 9.

## Reused files

* IUTI/HodgeTheater/LocalPrimePlaces.lean: the concrete local D-prime-strips
  and the actual local absolute Galois group type.
* Theorem311/PrimeStripFrobenioidCategorySkeleton.lean: the boundary evaluation
  localDPrimeStrip_geometric_eq_bot, reused in the obstruction theorem.
* Iut/Foundations/SourceAnabelioid.lean and SourceContinuousAnabelioid.lean: the
  certified anabelioid B(G), its fundamental-group certificate, and pointed
  morphisms.
* Mathlib GroupTheory/SemidirectProduct.lean and GroupTheory/GroupExtension:
  `SemidirectProduct`, `rightHom`, `range_inl_eq_ker_rightHom`, `inl_aut`,
  `GroupExtension.quotientKerRightHomEquivRight`.
* IUTII/Frobenioid/PrimeStripCore.lean (transitively): the DPrimeStrip carrier
  and DPrimeStripEquiv.
-/

noncomputable section

namespace LeanFormal.IUT.IUTII.Frobenioid.Example36

universe u

/-! ## 1. The local absolute Galois group as a profinite group -/

/-- The absolute Galois group of Q_p as a profinite group. -/
noncomputable abbrev localAbsoluteGaloisProfinite (p : Nat) [Fact (Nat.Prime p)] :
    ProfiniteGrp :=
  InfiniteGalois.profiniteGalGrp ℚ_[p] (AlgebraicClosure ℚ_[p])

/-- The underlying type is the actual local absolute Galois group used by the
concrete local D-prime-strips of LocalPrimePlaces. -/
theorem localAbsoluteGaloisProfinite_coe (p : Nat) [Fact (Nat.Prime p)] :
    (localAbsoluteGaloisProfinite p : Type) = LeanFormal.IUT.LocalAbsoluteGalois p :=
  rfl

/-! ## 2. The reduced geometric kernel model -/

/-- The reduced model of the geometric fundamental group: the cyclic group of
order two.  This is a parameter of the reduced realization, not the geometric
fundamental group of a curve. -/
noncomputable abbrev reducedGeometricKernelModel : ProfiniteGrp :=
  ProfiniteGrp.ofFiniteGrp (FiniteGrp.of (Multiplicative (ZMod 2)))

theorem reducedGeometricKernelModel_coe :
    (reducedGeometricKernelModel : Type) = Multiplicative (ZMod 2) :=
  rfl

/-- The reduced geometric kernel model has an element distinct from the
identity. -/
theorem reducedGeometricKernelModel_exists_ne_one :
    ∃ x : (reducedGeometricKernelModel : Type), x ≠ 1 :=
  ⟨(Multiplicative.ofAdd (1 : ZMod 2) : (reducedGeometricKernelModel : Type)),
    fun h => one_ne_zero (congrArg Multiplicative.toAdd h)⟩

/-! ## 3. Products of profinite groups and the first projection -/

/-- The product of two profinite groups, as a profinite group with the product
topology. -/
noncomputable def profiniteProduct (G H : ProfiniteGrp.{u}) : ProfiniteGrp.{u} :=
  ProfiniteGrp.of (G × H)

/-- The first projection of the product, as a morphism of profinite groups. -/
noncomputable def profiniteProductFst (G H : ProfiniteGrp.{u}) :
    profiniteProduct G H ⟶ G :=
  ProfiniteGrp.ofHom
    { toMonoidHom := MonoidHom.fst G H
      continuous_toFun := continuous_fst }

theorem profiniteProductFst_surjective (G H : ProfiniteGrp.{u}) :
    Function.Surjective (profiniteProductFst G H).hom.toMonoidHom := by
  intro g
  exact ⟨(g, 1), rfl⟩

/-- The kernel of the first projection of a product group is multiplicatively
equivalent to the second factor. -/
noncomputable def prodFstKerMulEquiv (G H : Type*) [Group G] [Group H] :
    (MonoidHom.fst G H).ker ≃* H where
  toFun x := x.1.2
  invFun h := ⟨(1, h), rfl⟩
  left_inv x := by
    apply Subtype.ext
    exact Prod.ext x.2.symm rfl
  right_inv h := rfl
  map_mul' x y := rfl

/-! ## 4. The local anabelioid groups and the projection -/

/-- The total fundamental group of the reduced local anabelioid: the actual
local absolute Galois group times the reduced geometric kernel model. -/
noncomputable abbrev localAnabelioidTotalGroup (p : Nat) [Fact (Nat.Prime p)] :
    ProfiniteGrp :=
  profiniteProduct (localAbsoluteGaloisProfinite p) reducedGeometricKernelModel

/-- The projection from the total group onto the local absolute Galois group. -/
noncomputable abbrev localAnabelioidProjection (p : Nat) [Fact (Nat.Prime p)] :
    localAnabelioidTotalGroup p ⟶ localAbsoluteGaloisProfinite p :=
  profiniteProductFst _ _

theorem localAnabelioidProjection_surjective (p : Nat) [Fact (Nat.Prime p)] :
    Function.Surjective (localAnabelioidProjection p).hom.toMonoidHom :=
  profiniteProductFst_surjective _ _

/-- The kernel of the genuine projection is the reduced geometric kernel model. -/
noncomputable def localAnabelioidProjection_kerMulEquiv
    (p : Nat) [Fact (Nat.Prime p)] :
    (localAnabelioidProjection p).hom.toMonoidHom.ker ≃*
      (reducedGeometricKernelModel : Type) :=
  prodFstKerMulEquiv (localAbsoluteGaloisProfinite p)
    (reducedGeometricKernelModel : Type)

/-! ## 5. The anabelioid realization -/

/-- The connected anabelioid B(Gal(Qbar_p/Q_p)) of the local absolute Galois
group, with its certified fundamental group. -/
noncomputable abbrev localGeometricAnabelioid (p : Nat) [Fact (Nat.Prime p)] :
    Iut.EtaleFundamentalGroup :=
  Iut.continuousActionEtaleFundamentalGroup (localAbsoluteGaloisProfinite p)

/-- The connected anabelioid of the total group. -/
noncomputable abbrev localTotalAnabelioid (p : Nat) [Fact (Nat.Prime p)] :
    Iut.EtaleFundamentalGroup :=
  Iut.continuousActionEtaleFundamentalGroup (localAnabelioidTotalGroup p)

/-- The pointed anabelioid morphism induced by the projection. -/
noncomputable abbrev localAnabelioidMorphism (p : Nat) [Fact (Nat.Prime p)] :
    Iut.SourcePointedAnabelioidHom (localTotalAnabelioid p) (localGeometricAnabelioid p) :=
  Iut.continuousActionPointedHom (localAnabelioidProjection p)

theorem localTotalAnabelioid_group (p : Nat) [Fact (Nat.Prime p)] :
    (localTotalAnabelioid p).group = localAnabelioidTotalGroup p :=
  rfl

theorem localGeometricAnabelioid_group (p : Nat) [Fact (Nat.Prime p)] :
    (localGeometricAnabelioid p).group = localAbsoluteGaloisProfinite p :=
  rfl

/-- The map on certified fundamental groups induced by the anabelioid morphism
is the original projection. -/
theorem localAnabelioidMorphism_fundamentalGroup_apply
    (p : Nat) [Fact (Nat.Prime p)] (x : (localTotalAnabelioid p).group) :
    (Iut.SourcePointedAnabelioidHom.fundamentalGroupHom
        (localAnabelioidMorphism p)).hom.toMonoidHom x =
      (localAnabelioidProjection p).hom.toMonoidHom x :=
  Iut.continuousActionPointedHom_fundamentalGroupHom (localAnabelioidProjection p) x

theorem localAnabelioidMorphism_fundamentalGroup_surjective
    (p : Nat) [Fact (Nat.Prime p)] :
    Function.Surjective (Iut.SourcePointedAnabelioidHom.fundamentalGroupHom
      (localAnabelioidMorphism p)).hom.toMonoidHom := by
  intro y
  obtain ⟨x, hx⟩ := localAnabelioidProjection_surjective p y
  exact ⟨x, by rw [localAnabelioidMorphism_fundamentalGroup_apply]; exact hx⟩

/-! ## 6. Place-indexed versions -/

/-- The local absolute Galois group at a rational prime place. -/
noncomputable abbrev localAbsoluteGaloisProfiniteAt (v : RationalPrimePlace) :
    ProfiniteGrp :=
  @localAbsoluteGaloisProfinite v.1 (Fact.mk v.2)

/-- The type of the local absolute Galois group at a place is the same type as
the fundamental group of the concrete local D-prime-strip. -/
theorem localAbsoluteGaloisProfiniteAt_coe (v : RationalPrimePlace) :
    (localAbsoluteGaloisProfiniteAt v : Type) =
      LeanFormal.IUT.localDPrimeStrip.Pi v :=
  rfl

noncomputable abbrev localAnabelioidTotalGroupAt (v : RationalPrimePlace) :
    ProfiniteGrp :=
  @localAnabelioidTotalGroup v.1 (Fact.mk v.2)

noncomputable abbrev localAnabelioidProjectionAt (v : RationalPrimePlace) :
    localAnabelioidTotalGroupAt v ⟶ localAbsoluteGaloisProfiniteAt v :=
  @localAnabelioidProjection v.1 (Fact.mk v.2)

theorem localAnabelioidProjectionAt_surjective (v : RationalPrimePlace) :
    Function.Surjective (localAnabelioidProjectionAt v).hom.toMonoidHom :=
  @localAnabelioidProjection_surjective v.1 (Fact.mk v.2)

noncomputable def localAnabelioidProjection_kerMulEquivAt (v : RationalPrimePlace) :
    (localAnabelioidProjectionAt v).hom.toMonoidHom.ker ≃*
      (reducedGeometricKernelModel : Type) :=
  @localAnabelioidProjection_kerMulEquiv v.1 (Fact.mk v.2)

noncomputable abbrev localTotalAnabelioidAt (v : RationalPrimePlace) :
    Iut.EtaleFundamentalGroup :=
  @localTotalAnabelioid v.1 (Fact.mk v.2)

noncomputable abbrev localGeometricAnabelioidAt (v : RationalPrimePlace) :
    Iut.EtaleFundamentalGroup :=
  @localGeometricAnabelioid v.1 (Fact.mk v.2)

noncomputable abbrev localAnabelioidMorphismAt (v : RationalPrimePlace) :
    Iut.SourcePointedAnabelioidHom (localTotalAnabelioidAt v) (localGeometricAnabelioidAt v) :=
  @localAnabelioidMorphism v.1 (Fact.mk v.2)

theorem localAnabelioidMorphismAt_fundamentalGroup_apply
    (v : RationalPrimePlace) (x : (localTotalAnabelioidAt v).group) :
    (Iut.SourcePointedAnabelioidHom.fundamentalGroupHom
        (localAnabelioidMorphismAt v)).hom.toMonoidHom x =
      (localAnabelioidProjectionAt v).hom.toMonoidHom x :=
  @localAnabelioidMorphism_fundamentalGroup_apply v.1 (Fact.mk v.2) x

theorem localAnabelioidMorphismAt_fundamentalGroup_surjective
    (v : RationalPrimePlace) :
    Function.Surjective (Iut.SourcePointedAnabelioidHom.fundamentalGroupHom
      (localAnabelioidMorphismAt v)).hom.toMonoidHom :=
  @localAnabelioidMorphism_fundamentalGroup_surjective v.1 (Fact.mk v.2)

/-! ## 7. The local anabelioid D-prime-strip -/

/-- The place-indexed anabelioid realization of the local D-prime-strip: its
fundamental groups are the certified fundamental groups of the anabelioids
B(Gal(Qbar_p/Q_p) x Z/2) and B(Gal(Qbar_p/Q_p)), and the projection is the
map induced by the pointed anabelioid morphism. -/
noncomputable def localAnabelioidDPrimeStrip : DPrimeStrip RationalPrimePlace where
  Pi := fun v => (localTotalAnabelioidAt v).group
  groupPi := fun _ => inferInstance
  G := fun v => (localGeometricAnabelioidAt v).group
  groupG := fun _ => inferInstance
  proj := fun v =>
    (Iut.SourcePointedAnabelioidHom.fundamentalGroupHom
      (localAnabelioidMorphismAt v)).hom.toMonoidHom
  proj_surjective := fun v => localAnabelioidMorphismAt_fundamentalGroup_surjective v

/-- The Galois group of the anabelioid strip at a place is the same type as the
fundamental group of the concrete local D-prime-strip. -/
theorem localAnabelioidDPrimeStrip_G_eq_concretePi (v : RationalPrimePlace) :
    localAnabelioidDPrimeStrip.G v = LeanFormal.IUT.localDPrimeStrip.Pi v :=
  rfl

/-- Pointwise: the projection of the anabelioid strip is the genuine projection
of the product group. -/
theorem localAnabelioidDPrimeStrip_proj_apply (v : RationalPrimePlace)
    (x : localAnabelioidDPrimeStrip.Pi v) :
    localAnabelioidDPrimeStrip.proj v x =
      (localAnabelioidProjectionAt v).hom.toMonoidHom x :=
  localAnabelioidMorphismAt_fundamentalGroup_apply v x

/-- The geometric kernel of the anabelioid strip is the kernel of the genuine
projection of the underlying reduced exact sequence. -/
theorem localAnabelioidDPrimeStrip_geometric_eq_projectionKernel
    (v : RationalPrimePlace) :
    localAnabelioidDPrimeStrip.geometric v =
      (localAnabelioidProjectionAt v).hom.toMonoidHom.ker := by
  ext x
  rw [DPrimeStrip.geometric_carrier, localAnabelioidDPrimeStrip_proj_apply]
  exact Iff.rfl

/-- The geometric kernel of the anabelioid strip is multiplicatively equivalent
to the reduced geometric kernel model. -/
noncomputable def localAnabelioidDPrimeStrip_geometricMulEquiv
    (v : RationalPrimePlace) :
    (localAnabelioidDPrimeStrip.geometric v) ≃*
      (reducedGeometricKernelModel : Type) :=
  (MulEquiv.subgroupCongr
      (localAnabelioidDPrimeStrip_geometric_eq_projectionKernel v)).trans
    (localAnabelioidProjection_kerMulEquivAt v)

/-- The reduced geometric kernel model has cardinality two. -/
theorem reducedGeometricKernelModel_card :
    Nat.card (reducedGeometricKernelModel : Type) = 2 := by
  rw [reducedGeometricKernelModel_coe]
  simp [Nat.card_eq_fintype_card, ZMod.card]

/-- The geometric kernel of the anabelioid strip is a group of order two. -/
theorem localAnabelioidDPrimeStrip_geometric_card (v : RationalPrimePlace) :
    Nat.card (localAnabelioidDPrimeStrip.geometric v) = 2 := by
  rw [Nat.card_congr (localAnabelioidDPrimeStrip_geometricMulEquiv v).toEquiv,
    reducedGeometricKernelModel_card]

theorem localAnabelioidDPrimeStrip_geometric_nontrivialElement
    (v : RationalPrimePlace) :
    ∃ x : localAnabelioidDPrimeStrip.Pi v,
      x ∈ localAnabelioidDPrimeStrip.geometric v ∧ x ≠ 1 := by
  obtain ⟨x, hx⟩ := reducedGeometricKernelModel_exists_ne_one
  let y : localAnabelioidDPrimeStrip.geometric v :=
    (localAnabelioidDPrimeStrip_geometricMulEquiv v).symm x
  refine ⟨y.1, y.2, ?_⟩
  intro hy
  have h1 : localAnabelioidDPrimeStrip_geometricMulEquiv v y = x :=
    (localAnabelioidDPrimeStrip_geometricMulEquiv v).apply_symm_apply x
  have hy1 : y = 1 := Subtype.ext hy
  rw [hy1, map_one] at h1
  exact hx h1.symm

theorem localAnabelioidDPrimeStrip_geometric_ne_bot (v : RationalPrimePlace) :
    localAnabelioidDPrimeStrip.geometric v ≠ ⊥ := by
  obtain ⟨x, hxmem, hxne⟩ :=
    localAnabelioidDPrimeStrip_geometric_nontrivialElement v
  intro hbot
  rw [hbot] at hxmem
  exact hxne (by simpa using hxmem)

/-- A D-prime-strip has a nontrivial geometric kernel at some place. -/
def HasNontrivialGeometricKernel {V : Type*} (D : DPrimeStrip V) : Prop :=
  ∃ v, D.geometric v ≠ ⊥

theorem localAnabelioidDPrimeStrip_hasNontrivialGeometricKernel :
    HasNontrivialGeometricKernel localAnabelioidDPrimeStrip :=
  ⟨⟨2, Nat.prime_two⟩, localAnabelioidDPrimeStrip_geometric_ne_bot _⟩

/-! ## 8. Obstruction: identity projection versus nontrivial geometric kernel -/

/-- Trivial geometric kernel is equivalent to injectivity of the projection. -/
theorem geometric_eq_bot_iff_injective {V : Type*} (D : DPrimeStrip V) (v : V) :
    D.geometric v = ⊥ ↔ Function.Injective (D.proj v) :=
  MonoidHom.ker_eq_bot_iff (D.proj v)

theorem geometric_ne_bot_iff_not_injective {V : Type*} (D : DPrimeStrip V) (v : V) :
    D.geometric v ≠ ⊥ ↔ ¬ Function.Injective (D.proj v) :=
  not_congr (geometric_eq_bot_iff_injective D v)

/-- A strip with injective projections has trivial geometric kernel
everywhere. -/
theorem geometric_eq_bot_of_injective_proj {V : Type*} (D : DPrimeStrip V)
    (h : ∀ v, Function.Injective (D.proj v)) : ∀ v, D.geometric v = ⊥ :=
  fun v => (geometric_eq_bot_iff_injective D v).mpr (h v)

/-- The projection of the anabelioid strip is not injective: its kernel is the
nontrivial reduced geometric kernel model. -/
theorem localAnabelioidDPrimeStrip_proj_not_injective (v : RationalPrimePlace) :
    ¬ Function.Injective (localAnabelioidDPrimeStrip.proj v) :=
  (geometric_ne_bot_iff_not_injective localAnabelioidDPrimeStrip v).mp
    (localAnabelioidDPrimeStrip_geometric_ne_bot v)

/-- A strip with a nontrivial geometric kernel at some place has a non-injective
projection at that place. -/
theorem not_forall_injective_of_nontrivial_geometric_kernel {V : Type*}
    {D : DPrimeStrip V} (h : HasNontrivialGeometricKernel D) :
    ¬ ∀ v, Function.Injective (D.proj v) := by
  rintro hinj
  obtain ⟨v, hv⟩ := h
  exact hv (geometric_eq_bot_of_injective_proj D hinj v)

/-- The kernel of a monoid homomorphism that is the identity is trivial. -/
theorem ker_eq_bot_of_hom_eq_id {M : Type*} [Group M] (f : M →* M)
    (h : f = MonoidHom.id M) : f.ker = ⊥ := by
  rw [h]
  exact (MonoidHom.ker_eq_bot_iff (MonoidHom.id M)).mpr (fun _ _ hxy => hxy)

/-- The concrete local D-prime-strip of LocalPrimePlaces has the identity
projection. -/
theorem concreteLocalDPrimeStrip_proj_eq_id (v : RationalPrimePlace) :
    LeanFormal.IUT.localDPrimeStrip.proj v =
      MonoidHom.id (LeanFormal.IUT.localDPrimeStrip.Pi v) :=
  rfl

/-- The projection of the concrete local D-prime-strip is injective. -/
theorem concreteLocalDPrimeStrip_proj_injective (v : RationalPrimePlace) :
    Function.Injective (LeanFormal.IUT.localDPrimeStrip.proj v) := by
  rw [concreteLocalDPrimeStrip_proj_eq_id]
  exact fun _ _ h => h

/-- Transfer of a trivial geometric kernel across an equivalence of D-prime-strips. -/
theorem geometric_eq_bot_of_stripEquiv {V : Type*} {D D' : DPrimeStrip V}
    (e : DPrimeStripEquiv D D') (h : ∀ v, D.geometric v = ⊥) :
    ∀ v, D'.geometric v = ⊥ := by
  intro v
  have hDinj : Function.Injective (D.proj v) :=
    (geometric_eq_bot_iff_injective D v).mp (h v)
  refine (geometric_eq_bot_iff_injective D' v).mpr ?_
  intro x y hxy
  obtain ⟨x₀, rfl⟩ := (e.isoPi v).surjective x
  obtain ⟨y₀, rfl⟩ := (e.isoPi v).surjective y
  have hx1 : D'.proj v (e.isoPi v x₀) = e.isoG v (D.proj v x₀) :=
    DPrimeStripEquiv.compat_apply e v x₀
  have hy1 : D'.proj v (e.isoPi v y₀) = e.isoG v (D.proj v y₀) :=
    DPrimeStripEquiv.compat_apply e v y₀
  have hGeq : e.isoG v (D.proj v x₀) = e.isoG v (D.proj v y₀) := by
    rw [← hx1, ← hy1]
    exact hxy
  have hDEq : D.proj v x₀ = D.proj v y₀ := (e.isoG v).injective hGeq
  have hxy₀ : x₀ = y₀ := hDinj hDEq
  rw [hxy₀]

/-- The concrete local D-prime-strip of LocalPrimePlaces has no nontrivial
geometric kernel. -/
theorem concreteLocalDPrimeStrip_not_hasNontrivialGeometricKernel :
    ¬ HasNontrivialGeometricKernel LeanFormal.IUT.localDPrimeStrip := by
  rintro ⟨v, hv⟩
  exact hv (LeanFormal.IUT.localDPrimeStrip_geometric_eq_bot v)

/-- The identity-projection local carrier is not equivalent, as a D-prime-strip,
to the anabelioid realization with its nontrivial geometric kernel. -/
theorem no_stripEquiv_concreteLocalStrip_anabelioid :
    ¬ Nonempty (DPrimeStripEquiv LeanFormal.IUT.localDPrimeStrip
        localAnabelioidDPrimeStrip) := by
  rintro ⟨e⟩
  have hbot : ∀ v, LeanFormal.IUT.localDPrimeStrip.geometric v = ⊥ :=
    fun v => LeanFormal.IUT.localDPrimeStrip_geometric_eq_bot v
  have h' : ∀ v, localAnabelioidDPrimeStrip.geometric v = ⊥ :=
    geometric_eq_bot_of_stripEquiv e hbot
  exact localAnabelioidDPrimeStrip_geometric_ne_bot ⟨2, Nat.prime_two⟩
    (h' ⟨2, Nat.prime_two⟩)

/-! ## 9. Semidirect (affine) realizations: a genuine module geometric kernel

The reduced strip of Section 7 and the mod-two/mod-four strips of the
elliptic-curve modules are split direct products `Gal x M`.  A source local
anabelioid, however, has a geometric kernel on which the arithmetic group acts,
and the total group is the corresponding semidirect product.  The constructions
below provide that shape for an arbitrary group `N` with an action of `G`. -/

section SemidirectRealization

variable {M A : Type u} [Group M] [Group A]

/-- The affine D-prime-strip attached to an `A`-module `M`: the local group is the
semidirect product `M ⋊[φ] A`, the arithmetic group is `A`, and the projection
is the canonical map onto `A`. -/
noncomputable def semidirectDPrimeStrip (φ : A →* MulAut M) : DPrimeStrip Unit where
  Pi _ := M ⋊[φ] A
  groupPi := fun _ => inferInstance
  G _ := A
  groupG := fun _ => inferInstance
  proj _ := SemidirectProduct.rightHom
  proj_surjective _ := SemidirectProduct.rightHom_surjective

@[simp] theorem semidirectDPrimeStrip_Pi (φ : A →* MulAut M) :
    (semidirectDPrimeStrip φ).Pi () = (M ⋊[φ] A) :=
  rfl

@[simp] theorem semidirectDPrimeStrip_G (φ : A →* MulAut M) :
    (semidirectDPrimeStrip φ).G () = A :=
  rfl

theorem semidirectDPrimeStrip_proj_apply (φ : A →* MulAut M) (x : M ⋊[φ] A) :
    (semidirectDPrimeStrip φ).proj () x = x.right :=
  rfl

/-- The geometric kernel of the affine strip is the range of the canonical
inclusion of the module. -/
theorem semidirectDPrimeStrip_geometric_eq_range_inl (φ : A →* MulAut M) :
    (semidirectDPrimeStrip φ).geometric () =
      (SemidirectProduct.inl : M →* M ⋊[φ] A).range := by
  rw [DPrimeStrip.geometric]
  exact SemidirectProduct.range_inl_eq_ker_rightHom.symm

/-- The geometric kernel of the affine strip is multiplicatively equivalent to
the module `M`, through the inclusion of the module into the semidirect
product. -/
noncomputable def semidirectGeometricMulEquiv (φ : A →* MulAut M) :
    (semidirectDPrimeStrip φ).geometric () ≃* M :=
  (MulEquiv.subgroupCongr (semidirectDPrimeStrip_geometric_eq_range_inl φ)).trans
    (MonoidHom.ofInjective (SemidirectProduct.inl_injective (φ := φ))).symm

theorem semidirectGeometricMulEquiv_inl (φ : A →* MulAut M) (m : M) :
    (semidirectGeometricMulEquiv φ).symm m =
      ⟨SemidirectProduct.inl m, by
        rw [semidirectDPrimeStrip_geometric_eq_range_inl]
        exact ⟨m, rfl⟩⟩ :=
  rfl

/-- A nontrivial module gives a nontrivial geometric kernel. -/
theorem semidirectDPrimeStrip_geometric_nontrivial (φ : A →* MulAut M)
    (hM : Nontrivial M) :
    (semidirectDPrimeStrip φ).geometric () ≠ ⊥ := by
  obtain ⟨m, hm⟩ := exists_ne (1 : M)
  intro hbot
  have hmem : (SemidirectProduct.inl m : M ⋊[φ] A) ∈
      (semidirectDPrimeStrip φ).geometric () := by
    rw [semidirectDPrimeStrip_geometric_eq_range_inl]
    exact ⟨m, rfl⟩
  rw [hbot] at hmem
  have h1 : (SemidirectProduct.inl m : M ⋊[φ] A) = 1 := Subgroup.mem_bot.mp hmem
  exact hm (SemidirectProduct.inl_injective (by simpa using h1))

/-- The affine strip of a nontrivial module has a nontrivial geometric kernel. -/
theorem semidirectDPrimeStrip_hasNontrivialGeometricKernel (φ : A →* MulAut M)
    (hM : Nontrivial M) :
    HasNontrivialGeometricKernel (semidirectDPrimeStrip φ) :=
  ⟨(), semidirectDPrimeStrip_geometric_nontrivial φ hM⟩

/-- The cardinality of the geometric kernel is the cardinality of the module. -/
theorem semidirectDPrimeStrip_geometric_card (φ : A →* MulAut M) {k : ℕ}
    (hk : Nat.card M = k) :
    Nat.card ((semidirectDPrimeStrip φ).geometric ()) = k := by
  rw [Nat.card_congr (semidirectGeometricMulEquiv φ).toEquiv, hk]

/-- Conjugation by the arithmetic part is the given action on the geometric
kernel: the kernel is an `A`-module, not an unrelated second group. -/
theorem semidirectGeometric_conj (φ : A →* MulAut M) (a : A) (m : M) :
    (SemidirectProduct.inr a * SemidirectProduct.inl m *
        (SemidirectProduct.inr a)⁻¹ : M ⋊[φ] A) =
      SemidirectProduct.inl (φ a m) := by
  simpa using (SemidirectProduct.inl_aut (φ := φ) a m).symm

/-- The exact sequence of the affine strip as a group extension. -/
noncomputable def semidirectGroupExtension (φ : A →* MulAut M) :
    GroupExtension M (M ⋊[φ] A) A :=
  SemidirectProduct.toGroupExtension φ

/-- The mono-analytic quotient: the local group modulo the geometric kernel is
the arithmetic group `A`, an actual group isomorphism and not a cardinality
placeholder. -/
noncomputable def semidirectLocalQuotientMulEquiv (φ : A →* MulAut M) :
    (M ⋊[φ] A) ⧸ (SemidirectProduct.rightHom : M ⋊[φ] A →* A).ker ≃* A :=
  QuotientGroup.quotientKerEquivOfSurjective
    (SemidirectProduct.rightHom : M ⋊[φ] A →* A) SemidirectProduct.rightHom_surjective

/-- The geometric kernel of the affine strip is the kernel of the canonical
projection, so the quotient above is exactly the quotient of the strip by its
geometric kernel. -/
theorem semidirectDPrimeStrip_geometric_eq_rightHom_ker (φ : A →* MulAut M) :
    (semidirectDPrimeStrip φ).geometric () =
      (SemidirectProduct.rightHom : M ⋊[φ] A →* A).ker :=
  rfl

/-- The affine action of the total group on the geometric fiber: `(m, a)` sends
`x` to `m * a x`. -/
noncomputable instance semidirectAffineMulAction (φ : A →* MulAut M) :
    MulAction (M ⋊[φ] A) M where
  smul x m := x.left * φ x.right m
  one_smul m := by
    change (1 : M ⋊[φ] A).left * φ (1 : M ⋊[φ] A).right m = m
    simp
  mul_smul x y m := by
    change (x * y).left * φ (x * y).right m =
      x.left * φ x.right (y.left * φ y.right m)
    rw [SemidirectProduct.mul_left, SemidirectProduct.mul_right]
    simp only [map_mul, MulAut.mul_apply, mul_assoc]

theorem semidirectAffineAction_apply (φ : A →* MulAut M) (x : M ⋊[φ] A) (m : M) :
    x • m = x.left * φ x.right m :=
  rfl

/-- The geometric part acts transitively on the fiber by translations. -/
theorem semidirectAffineAction_exists_smul_eq (φ : A →* MulAut M) (x y : M) :
    ∃ a : M ⋊[φ] A, a • x = y := by
  refine ⟨(SemidirectProduct.mk (y * x⁻¹) (1 : A) : M ⋊[φ] A), ?_⟩
  rw [semidirectAffineAction_apply]
  simp [mul_assoc]

/-- The translation part acts freely on the fiber. -/
theorem semidirectAffineAction_inl_injective (φ : A →* MulAut M) (x : M) {m n : M}
    (h : (SemidirectProduct.inl (N := M) (G := A) (φ := φ) m : M ⋊[φ] A) • x =
      (SemidirectProduct.inl (N := M) (G := A) (φ := φ) n : M ⋊[φ] A) • x) :
    m = n := by
  rw [semidirectAffineAction_apply, semidirectAffineAction_apply] at h
  have h' : m * x = n * x := by simpa using h
  exact mul_right_cancel h'

/-- The inverse of an affine transformation returns the point. -/
theorem semidirectAffineAction_inv_smul (φ : A →* MulAut M) (a : M ⋊[φ] A) (m : M) :
    a⁻¹ • (a • m) = m := by
  rw [← mul_smul, inv_mul_cancel, one_smul]

/-- The explicit orbit equivalence relation of the affine action on the
geometric fiber. -/
def semidirectAffineOrbitSetoid (φ : A →* MulAut M) : Setoid M where
  r x y := ∃ a : M ⋊[φ] A, a • x = y
  iseqv :=
    { refl := fun x => ⟨1, one_smul (M ⋊[φ] A) x⟩
      symm := fun {x y} ⟨a, ha⟩ =>
        ⟨a⁻¹, by rw [← ha, semidirectAffineAction_inv_smul]⟩
      trans := fun {x y z} ⟨a, ha⟩ ⟨b, hb⟩ =>
        ⟨b * a, by rw [mul_smul, ha, hb]⟩ }

/-- The orbit quotient of the geometric fiber is a single point: the fiber is a
torsor under the geometric part, so the mono-analytic (D-)quotient retains only
the arithmetic group `A`. -/
theorem semidirectAffineOrbitSetoid_subsingleton (φ : A →* MulAut M) :
    Subsingleton (Quotient (semidirectAffineOrbitSetoid φ)) := by
  refine ⟨fun p q => ?_⟩
  induction p using Quotient.inductionOn with
  | h x =>
    induction q using Quotient.inductionOn with
    | h y =>
      exact Quotient.sound (semidirectAffineAction_exists_smul_eq φ x y)

end SemidirectRealization

/-! ## 10. The anabelioid-to-strip assignment -/

/-- A morphism of D-prime-strips: compatible maps on the local and arithmetic
groups. -/
structure DPrimeStripHom {V : Type*} (D D' : DPrimeStrip V) where
  mapPi : ∀ v, D.Pi v →* D'.Pi v
  mapG : ∀ v, D.G v →* D'.G v
  compat : ∀ v, (D'.proj v).comp (mapPi v) = (mapG v).comp (D.proj v)

namespace DPrimeStripHom

variable {V : Type*} {D D' D'' : DPrimeStrip V}

/-- The commutation law of a D-prime-strip morphism, applied to an element. -/
theorem compat_apply (φ : DPrimeStripHom D D') (v : V) (x : D.Pi v) :
    D'.proj v (φ.mapPi v x) = φ.mapG v (D.proj v x) :=
  DFunLike.congr_fun (φ.compat v) x

def id (D : DPrimeStrip V) : DPrimeStripHom D D where
  mapPi _ := MonoidHom.id _
  mapG _ := MonoidHom.id _
  compat _ := rfl

def comp (φ : DPrimeStripHom D D') (ψ : DPrimeStripHom D' D'') :
    DPrimeStripHom D D'' where
  mapPi v := (ψ.mapPi v).comp (φ.mapPi v)
  mapG v := (ψ.mapG v).comp (φ.mapG v)
  compat v := by
    ext x
    exact (compat_apply ψ v (φ.mapPi v x)).trans
      (congrArg (ψ.mapG v) (compat_apply φ v x))

end DPrimeStripHom

section AnabelioidStrip

/-- The D-prime-strip attached to a pointed morphism of connected anabelioids
whose induced map on certified fundamental groups is surjective: the local group
is the certified fundamental group of the source anabelioid, the arithmetic
group that of the target, and the projection the induced morphism. -/
noncomputable def anabelioidDPrimeStripOf {X Y : Iut.EtaleFundamentalGroup}
    (φ : Iut.SourcePointedAnabelioidHom X Y)
    (hφ : Function.Surjective
      (Iut.SourcePointedAnabelioidHom.fundamentalGroupHom φ).hom.toMonoidHom) :
    DPrimeStrip Unit where
  Pi _ := X.group
  groupPi _ := inferInstance
  G _ := Y.group
  groupG _ := inferInstance
  proj _ := (Iut.SourcePointedAnabelioidHom.fundamentalGroupHom φ).hom.toMonoidHom
  proj_surjective _ := hφ

/-- The place-indexed instance of the assignment, applied to the local
anabelioid morphism of Section 6. -/
noncomputable def anabelioidDPrimeStripOfAt (v : RationalPrimePlace) :
    DPrimeStrip Unit :=
  anabelioidDPrimeStripOf (localAnabelioidMorphismAt v)
    (localAnabelioidMorphismAt_fundamentalGroup_surjective v)

theorem anabelioidDPrimeStripOfAt_Pi (v : RationalPrimePlace) :
    (anabelioidDPrimeStripOfAt v).Pi () = localAnabelioidDPrimeStrip.Pi v :=
  rfl

theorem anabelioidDPrimeStripOfAt_G (v : RationalPrimePlace) :
    (anabelioidDPrimeStripOfAt v).G () = localAnabelioidDPrimeStrip.G v :=
  rfl

theorem anabelioidDPrimeStripOfAt_proj_apply (v : RationalPrimePlace)
    (x : localAnabelioidDPrimeStrip.Pi v) :
    (anabelioidDPrimeStripOfAt v).proj () x = localAnabelioidDPrimeStrip.proj v x :=
  rfl

/-- The identity pointed morphism induces a strip whose projection is the
identity: the identity law of the assignment. -/
theorem anabelioidIdentity_fundamentalGroup_surjective
    (X : Iut.EtaleFundamentalGroup) :
    Function.Surjective
      (Iut.SourcePointedAnabelioidHom.fundamentalGroupHom
        (Iut.SourcePointedAnabelioidHom.identity X)).hom.toMonoidHom := by
  intro y
  exact ⟨y, Iut.SourcePointedAnabelioidHom.fundamentalGroupHom_identity X y⟩

theorem anabelioidDPrimeStripOf_proj_identity (X : Iut.EtaleFundamentalGroup)
    (x : X.group) :
    (anabelioidDPrimeStripOf (Iut.SourcePointedAnabelioidHom.identity X)
        (anabelioidIdentity_fundamentalGroup_surjective X)).proj () x = x :=
  Iut.SourcePointedAnabelioidHom.fundamentalGroupHom_identity X x

/-- On the concrete restriction morphisms `B(H) → B(K)` the assignment is the
given morphism of profinite groups itself: the object formula agrees with
`SourcePointedAnabelioidHom.fundamentalGroupHom`. -/
theorem anabelioidDPrimeStripOf_continuousActionPointedHom {H K : ProfiniteGrp.{u}}
    (f : H ⟶ K)
    (hf : Function.Surjective
      (Iut.SourcePointedAnabelioidHom.fundamentalGroupHom
        (Iut.continuousActionPointedHom f)).hom.toMonoidHom)
    (x : H) :
    (anabelioidDPrimeStripOf (Iut.continuousActionPointedHom f) hf).proj () x = f x :=
  Iut.continuousActionPointedHom_fundamentalGroupHom f x

end AnabelioidStrip

end LeanFormal.IUT.IUTII.Frobenioid.Example36
