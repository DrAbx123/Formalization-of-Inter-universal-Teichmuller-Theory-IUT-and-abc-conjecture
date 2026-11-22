import Iut.Foundations.SourceContinuousAnabelioid
import LeanFormal.IUT.IUTII.Frobenioid.Example36EllipticCurveSourcePiCard
import LeanFormal.IUT.IUTII.Frobenioid.Example36CurveEtaleCovers
import Mathlib.Topology.Algebra.Category.ProfiniteGrp.Completion
import Mathlib.GroupTheory.FreeGroup.Basic
import Mathlib.Tactic

/-!
# The free profinite group on two generators and its certified anabelioid

Source anchor: IUT II, Sections 3-6, boundary item (1) (the geometric
fundamental group of the base curve); Group-1 continuation of the mod-2 and
mod-4 finite-level files.

The standard theorem that the geometric etale fundamental group of a
ONCE-PUNCTURED elliptic curve over a separably closed field of characteristic
zero is the free profinite group on two generators is NOT available in this
tree.  (This statement is specific to the punctured affine curve; it is not the
free-profinite-group statement for proper curves.)  This file therefore does not
construct the geometric pi1 of any curve.  What it does construct is the actual
free profinite group on two generators, as the Mathlib profinite completion of
the abstract free group on two generators, together with its universal property
and concrete finite quotients; it identifies this group only as the CANDIDATE
group for the once-punctured curve, in a frozen card, and makes no curve
identification claim.

## Main content

* freeProfiniteGroupTwo is defined as the Mathlib profinite completion of
  FreeGroup (Fin 2) (the profiniteCompletion functor of
  Mathlib/Topology/Algebra/Category/ProfiniteGrp/Completion.lean).
* freeProfiniteGroupTwo_homEquiv is the universal property: continuous
  morphisms from the free profinite group to any profinite group P correspond
  to ordinary group morphisms from FreeGroup (Fin 2) to the underlying group of
  P.  For finite or discrete P this is exactly the correspondence between
  continuous maps and choices of two elements of P.  The canonical dense map
  freeProfiniteGroupTwo_etaFn_dense and the pointwise form
  freeProfiniteGroupTwo_lift_etaFn are recorded, together with uniqueness
  (freeProfiniteGroupTwo_lift_unique).
* Finite quotients: freeProfiniteGroupTwo_finiteQuotient sends a group
  homomorphism FreeGroup (Fin 2) ->* H with H finite to a continuous morphism
  into the finite profinite group attached to H.  Concrete instances are the
  abelian mod-2 quotient freeProfiniteGroupTwo_modTwoQuotient, the abelianization
  maps to the finite quotients (Z/n)^2 of Z^2
  (freeProfiniteGroupTwo_abelianizationQuotient), and the nonabelian
  symmetric-group quotient freeProfiniteGroupTwo_symmetricThreeQuotient to
  S_3 = Equiv.Perm (Fin 3).
* Nontriviality and nonabelianity: freeProfiniteGroupTwo_exists_ne_one and
  freeProfiniteGroupTwo_nontrivial, and freeProfiniteGroupTwo_not_commutative
  proved through the nonabelian finite quotient to S_3 (the two generator images
  are the transpositions (0 1) and (1 2), which do not commute).  Hence the
  group is neither trivial, nor abelian, nor procyclic.
* The certified anabelioid freeProfinitePiGeometricAnabelioid = B(Pi_geo) is
  built with Iut.continuousActionEtaleFundamentalGroup; its stored group is
  freeProfiniteGroupTwo and its certified fundamental-group property is restated
  (freeProfinitePiGeometricAnabelioid_group,
  freeProfinitePiGeometricAnabelioid_certified).  Its cover category is the
  category of finite continuous Pi_geo-sets by construction.
* The frozen card PuncturedCurveGeometricPiCard / FreeProfinitePiCurveIdentificationCard
  records the candidate identification of the once-punctured curve geometric pi1
  with the free profinite group on two generators.  The card is NOT a bare
  group-plus-MulEquiv record: it is bound to the actual once-punctured curve
  scheme via scheme isomorphisms, to an actual geometric base-change scheme with
  a map to that base scheme, to the actual finite etale cover category of the
  geometric base change and its fiber functor/fundamental-group property, to the
  geometric fiber at the terminal cover and its automorphism group, to a
  profinite topological group isomorphism between the candidate pi1 and the
  actual fundamental group, and to a proof of actual geometric connectedness
  (IsConnected) of the geometric base change.  The card is a frozen obligation
  with no inhabitant; there is no Realized proposition and no refl realization.
  No fake curve group is introduced: the file contains no definition of a curve
  fundamental group.

## Honest boundary (not claimed)

* The once-punctured-curve geometric pi1 is not constructed, and the free
  profinite group is not identified with it.  The standard free-group theorem
  for punctured curves is not in the tree; the card records the candidate.
* No source claim, no theta / q-pilot / Tate identification, and no arithmetic
  degree, log-volume or comparison statement is made.
-/

noncomputable section

namespace LeanFormal.IUT.IUTII.Frobenioid
namespace Example36

open CategoryTheory
open AlgebraicGeometry
open EtaleCoverFoundations

/-! ## 1. The free profinite group on two generators -/

/-- The free profinite group on two generators: the Mathlib profinite
completion of the abstract free group on the two-element generating set Fin 2. -/
def freeProfiniteGroupTwo : ProfiniteGrp :=
  ProfiniteGrp.ProfiniteCompletion.completion (GrpCat.of (FreeGroup (Fin 2)))

/-- The universal property of the free profinite group on two generators:
continuous morphisms to a profinite group P correspond to ordinary group
morphisms from FreeGroup (Fin 2) to the underlying group of P. -/
noncomputable def freeProfiniteGroupTwo_homEquiv (P : ProfiniteGrp) :
    (freeProfiniteGroupTwo ⟶ P) ≃
      (GrpCat.of (FreeGroup (Fin 2)) ⟶ GrpCat.of P) :=
  ProfiniteGrp.ProfiniteCompletion.homEquiv (GrpCat.of (FreeGroup (Fin 2))) P

/-- The canonical morphism from the abstract free group to its profinite
completion. -/
noncomputable def freeProfiniteGroupTwo_eta :
    GrpCat.of (FreeGroup (Fin 2)) ⟶ GrpCat.of freeProfiniteGroupTwo :=
  ProfiniteGrp.ProfiniteCompletion.eta (GrpCat.of (FreeGroup (Fin 2)))

/-- The image of the abstract free group is dense in its profinite completion. -/
theorem freeProfiniteGroupTwo_etaFn_dense :
    DenseRange (ProfiniteGrp.ProfiniteCompletion.etaFn
      (GrpCat.of (FreeGroup (Fin 2)))) :=
  ProfiniteGrp.ProfiniteCompletion.denseRange _

/-- Pointwise form of the universal property: the continuous lift of a group
morphism sends the canonical dense image of g to f g. -/
theorem freeProfiniteGroupTwo_lift_etaFn (P : ProfiniteGrp)
    (f : GrpCat.of (FreeGroup (Fin 2)) ⟶ GrpCat.of P) (g : FreeGroup (Fin 2)) :
    (ProfiniteGrp.ProfiniteCompletion.lift f).hom
        (ProfiniteGrp.ProfiniteCompletion.etaFn
          (GrpCat.of (FreeGroup (Fin 2))) g) = f.hom g := by
  have h := ProfiniteGrp.ProfiniteCompletion.lift_eta f
  have hg := congrArg (fun φ : GrpCat.of (FreeGroup (Fin 2)) ⟶ GrpCat.of P => φ.hom g) h
  rw [show (forget₂ ProfiniteGrp GrpCat).map (ProfiniteGrp.ProfiniteCompletion.lift f) =
      GrpCat.ofHom ((ProfiniteGrp.ProfiniteCompletion.lift f).hom.toMonoidHom) from rfl] at hg
  have heta : (GrpCat.Hom.hom (ProfiniteGrp.ProfiniteCompletion.eta
      (GrpCat.of (FreeGroup (Fin 2))))) =
      ProfiniteGrp.ProfiniteCompletion.etaFn (GrpCat.of (FreeGroup (Fin 2))) := rfl
  simpa [heta] using hg

/-- Uniqueness part of the universal property: two continuous morphisms out of
the free profinite group are equal once they agree on the dense image of the
abstract free group. -/
theorem freeProfiniteGroupTwo_lift_unique {P : ProfiniteGrp}
    (f g : freeProfiniteGroupTwo ⟶ P)
    (h : (ProfiniteGrp.ProfiniteCompletion.eta (GrpCat.of (FreeGroup (Fin 2)))) ≫
        (forget₂ ProfiniteGrp GrpCat).map f =
      (ProfiniteGrp.ProfiniteCompletion.eta (GrpCat.of (FreeGroup (Fin 2)))) ≫
        (forget₂ ProfiniteGrp GrpCat).map g) : f = g :=
  ProfiniteGrp.ProfiniteCompletion.lift_unique f g h

/-! ## 2. Finite quotients of the free profinite group -/

/-- A finite quotient: a group morphism from FreeGroup (Fin 2) to a finite group
H gives a continuous morphism from the free profinite group to the finite
profinite group attached to H. -/
noncomputable def freeProfiniteGroupTwo_finiteQuotient
    (H : Type) [Group H] [Finite H] (f : FreeGroup (Fin 2) →* H) :
    freeProfiniteGroupTwo ⟶
      ProfiniteGrp.ofFiniteGrp (FiniteGrp.of H) :=
  ProfiniteGrp.ProfiniteCompletion.lift (GrpCat.ofHom f)

/-- The abelian mod-two quotient map, defined by sending the first generator to
1 and the second to 0. -/
def freeProfiniteGroupTwo_modTwoMap : FreeGroup (Fin 2) →* Multiplicative (ZMod 2) :=
  FreeGroup.lift (fun i => Multiplicative.ofAdd (if (i : Fin 2) = 0 then 1 else 0))

noncomputable def freeProfiniteGroupTwo_modTwoQuotient :
    freeProfiniteGroupTwo ⟶
      ProfiniteGrp.ofFiniteGrp (FiniteGrp.of (Multiplicative (ZMod 2))) :=
  ProfiniteGrp.ProfiniteCompletion.lift
    (GrpCat.ofHom freeProfiniteGroupTwo_modTwoMap)

theorem freeProfiniteGroupTwo_modTwoMap_of_zero :
    freeProfiniteGroupTwo_modTwoMap (FreeGroup.of (0 : Fin 2)) =
      Multiplicative.ofAdd (1 : ZMod 2) := by
  rw [show freeProfiniteGroupTwo_modTwoMap = FreeGroup.lift
    (fun i => Multiplicative.ofAdd (if (i : Fin 2) = 0 then 1 else 0)) from rfl]
  rw [FreeGroup.lift_apply_of]
  simp

theorem freeProfiniteGroupTwo_modTwoQuotient_eta_generator :
    (freeProfiniteGroupTwo_modTwoQuotient).hom
        (ProfiniteGrp.ProfiniteCompletion.etaFn
          (GrpCat.of (FreeGroup (Fin 2)))
          (FreeGroup.of (0 : Fin 2))) = Multiplicative.ofAdd (1 : ZMod 2) := by
  have h := freeProfiniteGroupTwo_lift_etaFn
    (ProfiniteGrp.ofFiniteGrp (FiniteGrp.of (Multiplicative (ZMod 2))))
    (GrpCat.ofHom freeProfiniteGroupTwo_modTwoMap) (FreeGroup.of (0 : Fin 2))
  have hmap : (GrpCat.ofHom freeProfiniteGroupTwo_modTwoMap).hom
      (FreeGroup.of (0 : Fin 2)) = Multiplicative.ofAdd (1 : ZMod 2) :=
    freeProfiniteGroupTwo_modTwoMap_of_zero
  exact h.trans hmap

/-- The abelianization map to the finite quotient (Z/n)^2 of Z^2: the two free
generators are sent to the two standard basis vectors modulo n. -/
def freeProfiniteGroupTwo_abelianizationMap (n : ℕ) [NeZero n] :
    FreeGroup (Fin 2) →* (Multiplicative (ZMod n) × Multiplicative (ZMod n)) :=
  FreeGroup.lift (fun i =>
    if (i : Fin 2) = 0 then (Multiplicative.ofAdd 1, 1)
    else (1, Multiplicative.ofAdd 1))

noncomputable def freeProfiniteGroupTwo_abelianizationQuotient
    (n : ℕ) [NeZero n] :
    freeProfiniteGroupTwo ⟶
      ProfiniteGrp.ofFiniteGrp (FiniteGrp.of
        (Multiplicative (ZMod n) × Multiplicative (ZMod n))) :=
  ProfiniteGrp.ProfiniteCompletion.lift
    (GrpCat.ofHom (freeProfiniteGroupTwo_abelianizationMap n))

/-- The nonabelian finite quotient map to S_3 = Equiv.Perm (Fin 3): the two
generators are sent to the adjacent transpositions (0 1) and (1 2). -/
def freeProfiniteGroupTwo_symmetricThreeMap :
    FreeGroup (Fin 2) →* Equiv.Perm (Fin 3) :=
  FreeGroup.lift (fun i =>
    if (i : Fin 2) = 0 then Equiv.swap (0 : Fin 3) 1 else Equiv.swap (1 : Fin 3) 2)

noncomputable def freeProfiniteGroupTwo_symmetricThreeQuotient :
    freeProfiniteGroupTwo ⟶
      ProfiniteGrp.ofFiniteGrp (FiniteGrp.of (Equiv.Perm (Fin 3))) :=
  ProfiniteGrp.ProfiniteCompletion.lift
    (GrpCat.ofHom freeProfiniteGroupTwo_symmetricThreeMap)

theorem freeProfiniteGroupTwo_symmetricThreeMap_of_zero :
    freeProfiniteGroupTwo_symmetricThreeMap (FreeGroup.of (0 : Fin 2)) =
      Equiv.swap (0 : Fin 3) 1 := by
  rw [show freeProfiniteGroupTwo_symmetricThreeMap = FreeGroup.lift
    (fun i => if (i : Fin 2) = 0 then Equiv.swap (0 : Fin 3) 1
      else Equiv.swap (1 : Fin 3) 2) from rfl]
  rw [FreeGroup.lift_apply_of]
  simp

theorem freeProfiniteGroupTwo_symmetricThreeMap_of_one :
    freeProfiniteGroupTwo_symmetricThreeMap (FreeGroup.of (1 : Fin 2)) =
      Equiv.swap (1 : Fin 3) 2 := by
  rw [show freeProfiniteGroupTwo_symmetricThreeMap = FreeGroup.lift
    (fun i => if (i : Fin 2) = 0 then Equiv.swap (0 : Fin 3) 1
      else Equiv.swap (1 : Fin 3) 2) from rfl]
  rw [FreeGroup.lift_apply_of]
  simp

theorem freeProfiniteGroupTwo_symmetricThreeQuotient_eta_generator_zero :
    (freeProfiniteGroupTwo_symmetricThreeQuotient).hom
        (ProfiniteGrp.ProfiniteCompletion.etaFn
          (GrpCat.of (FreeGroup (Fin 2)))
          (FreeGroup.of (0 : Fin 2))) = Equiv.swap (0 : Fin 3) 1 := by
  have h := freeProfiniteGroupTwo_lift_etaFn
    (ProfiniteGrp.ofFiniteGrp (FiniteGrp.of (Equiv.Perm (Fin 3))))
    (GrpCat.ofHom freeProfiniteGroupTwo_symmetricThreeMap) (FreeGroup.of (0 : Fin 2))
  have hmap : (GrpCat.ofHom freeProfiniteGroupTwo_symmetricThreeMap).hom
      (FreeGroup.of (0 : Fin 2)) = Equiv.swap (0 : Fin 3) 1 :=
    freeProfiniteGroupTwo_symmetricThreeMap_of_zero
  exact h.trans hmap

theorem freeProfiniteGroupTwo_symmetricThreeQuotient_eta_generator_one :
    (freeProfiniteGroupTwo_symmetricThreeQuotient).hom
        (ProfiniteGrp.ProfiniteCompletion.etaFn
          (GrpCat.of (FreeGroup (Fin 2)))
          (FreeGroup.of (1 : Fin 2))) = Equiv.swap (1 : Fin 3) 2 := by
  have h := freeProfiniteGroupTwo_lift_etaFn
    (ProfiniteGrp.ofFiniteGrp (FiniteGrp.of (Equiv.Perm (Fin 3))))
    (GrpCat.ofHom freeProfiniteGroupTwo_symmetricThreeMap) (FreeGroup.of (1 : Fin 2))
  have hmap : (GrpCat.ofHom freeProfiniteGroupTwo_symmetricThreeMap).hom
      (FreeGroup.of (1 : Fin 2)) = Equiv.swap (1 : Fin 3) 2 :=
    freeProfiniteGroupTwo_symmetricThreeMap_of_one
  exact h.trans hmap

/-! ## 3. Nontriviality and nonabelianity -/

theorem freeProfiniteGroupTwo_exists_ne_one :
    ∃ x : freeProfiniteGroupTwo, x ≠ 1 := by
  refine ⟨ProfiniteGrp.ProfiniteCompletion.etaFn
    (GrpCat.of (FreeGroup (Fin 2))) (FreeGroup.of (0 : Fin 2)), ?_⟩
  intro h
  have hq := congrArg (fun x => freeProfiniteGroupTwo_modTwoQuotient.hom x) h
  rw [map_one] at hq
  rw [freeProfiniteGroupTwo_modTwoQuotient_eta_generator] at hq
  have hz : (1 : ZMod 2) = 0 := ofAdd_eq_one.mp hq
  exact one_ne_zero hz

theorem freeProfiniteGroupTwo_nontrivial : Nontrivial freeProfiniteGroupTwo :=
  let ⟨x, hx⟩ := freeProfiniteGroupTwo_exists_ne_one
  ⟨x, 1, hx⟩

theorem symmetricThreeSwaps_noncommute :
    Equiv.swap (0 : Fin 3) 1 * Equiv.swap (1 : Fin 3) 2 ≠
      Equiv.swap (1 : Fin 3) 2 * Equiv.swap (0 : Fin 3) 1 := by
  decide

/-- The free profinite group on two generators is not commutative: its finite
quotient to S_3 sends the two dense generator images to the noncommuting
transpositions (0 1) and (1 2). -/
theorem freeProfiniteGroupTwo_not_commutative :
    ¬ ∀ a b : freeProfiniteGroupTwo, a * b = b * a := by
  intro hcomm
  let Q : freeProfiniteGroupTwo ⟶
      ProfiniteGrp.ofFiniteGrp (FiniteGrp.of (Equiv.Perm (Fin 3))) :=
    freeProfiniteGroupTwo_symmetricThreeQuotient
  let x : freeProfiniteGroupTwo := ProfiniteGrp.ProfiniteCompletion.etaFn
    (GrpCat.of (FreeGroup (Fin 2))) (FreeGroup.of (0 : Fin 2))
  let y : freeProfiniteGroupTwo := ProfiniteGrp.ProfiniteCompletion.etaFn
    (GrpCat.of (FreeGroup (Fin 2))) (FreeGroup.of (1 : Fin 2))
  have hxy : x * y = y * x := hcomm x y
  have hq := congrArg (fun z => Q.hom z) hxy
  have hmulL : Q.hom (x * y) = Q.hom x * Q.hom y := Q.hom.map_mul x y
  have hmulR : Q.hom (y * x) = Q.hom y * Q.hom x := Q.hom.map_mul y x
  have hx : Q.hom x = Equiv.swap (0 : Fin 3) 1 := by
    simpa [Q, x] using freeProfiniteGroupTwo_symmetricThreeQuotient_eta_generator_zero
  have hy : Q.hom y = Equiv.swap (1 : Fin 3) 2 := by
    simpa [Q, y] using freeProfiniteGroupTwo_symmetricThreeQuotient_eta_generator_one
  rw [hmulL, hmulR, hx, hy] at hq
  exact symmetricThreeSwaps_noncommute hq

/-! ## 4. The certified anabelioid B(Pi_geo) -/

/-- The certified anabelioid B(Pi_geo) of the free profinite group on two
generators: its cover category is, by construction, the category of finite
continuous Pi_geo-sets, and its stored profinite group is Pi_geo. -/
noncomputable def freeProfinitePiGeometricAnabelioid : Iut.EtaleFundamentalGroup :=
  Iut.continuousActionEtaleFundamentalGroup freeProfiniteGroupTwo

theorem freeProfinitePiGeometricAnabelioid_group :
    freeProfinitePiGeometricAnabelioid.group = freeProfiniteGroupTwo :=
  rfl

/-- The certified fundamental-group property of B(Pi_geo). -/
theorem freeProfinitePiGeometricAnabelioid_certified :
    letI := freeProfinitePiGeometricAnabelioid.coverCategory
    letI := freeProfinitePiGeometricAnabelioid.galoisCategory
    letI := freeProfinitePiGeometricAnabelioid.fiberFunctor
    letI (X : freeProfinitePiGeometricAnabelioid.Cover) :=
      freeProfinitePiGeometricAnabelioid.action X
    PreGaloisCategory.IsFundamentalGroup freeProfinitePiGeometricAnabelioid.fiber
      freeProfinitePiGeometricAnabelioid.group :=
  Iut.EtaleFundamentalGroup.certified freeProfinitePiGeometricAnabelioid

/-! ## 5. The frozen card for the once-punctured curve geometric pi1 -/

/-- Frozen card: the candidate geometric fundamental group of the actual
once-punctured curve scheme curveScheme K, identified with the free
profinite group on two generators.  Every field is bound to actual geometric
data: the actual base scheme is the once-punctured curve scheme (through the
scheme isomorphism baseSchemeIso), the geometric base change is an actual scheme
mapping to the base scheme, the cover category is the actual category of finite
etale covers of the geometric base change with a fiber functor and its
fundamental-group property, the geometric fiber is the fiber of the terminal
cover with its automorphism group, the candidate pi1 is related to the actual
fundamental group and to the free profinite group by profinite topological group
isomorphisms (categorical isomorphisms in ProfiniteGrp), and geometric
connectedness is the actual topological predicate IsConnected of the geometric
base change.  This is a frozen obligation: no inhabitant is constructed in this
file, there is no Realized proposition, and no theorem consumes the card.  In
particular the free profinite group plus a bare MulEquiv does not satisfy it. -/
structure PuncturedCurveGeometricPiCard (K : Type) [Field K] where
  /-- The actual base scheme of the once-punctured curve. -/
  baseScheme : Scheme
  /-- The base scheme is the actual once-punctured curve scheme. -/
  baseSchemeIso : baseScheme ≅ curveScheme K
  /-- The actual geometric base change of the base scheme. -/
  geometricBaseChange : Scheme
  /-- The geometric base change is the actual once-punctured curve scheme. -/
  geometricBaseChangeIso : geometricBaseChange ≅ curveScheme K
  /-- The actual Galois category, fiber functor, fundamental group and
  geometric pi1 data of the finite etale cover category of the actual
  once-punctured curve scheme. -/
  galoisData : SchemeGaloisConnectednessCard (curveScheme K)
  /-- The actual geometric fiber at the terminal cover. -/
  geometricFiber : FintypeCat
  /-- The geometric fiber is the fiber of the actual terminal cover under the
  actual fiber functor. -/
  geometricFiberIso : geometricFiber ≅
    galoisData.fiber.obj (terminalCover (curveScheme K))
  /-- The automorphism group of the actual geometric fiber. -/
  geometricAut : Type
  /-- The group structure on the automorphism group. -/
  [groupGeometricAut : Group geometricAut]
  /-- The automorphism group is the actual Aut group of the geometric fiber. -/
  geometricAutIso : geometricAut ≃* Aut geometricFiber
  /-- The candidate geometric fundamental group. -/
  geometricPiOne : ProfiniteGrp
  /-- The candidate pi1 is the actual geometric pi1 of the Galois data, up to
  a profinite topological group isomorphism. -/
  geometricPiOneIso_actual : geometricPiOne ≅ galoisData.geometricPiOne
  /-- The candidate pi1 is the free profinite group on two generators, up to a
  profinite topological group isomorphism. -/
  freeProfiniteIso : geometricPiOne ≅ freeProfiniteGroupTwo
  /-- Actual geometric connectedness of the once-punctured curve base scheme. -/
  geometricConnectedness : IsConnected (curveScheme K)

/-- The frozen identification card for the source once-punctured curve over Q:
the geometric pi1 of the curve y^2 = x^3 - x with the origin removed is the free
profinite group on two generators.  This is the standard punctured-curve
free-group theorem, which is NOT available in the tree; the card type has no
inhabitant constructed here and no Realized proposition.  The free profinite
group is only the candidate group. -/
abbrev FreeProfinitePiCurveIdentificationCard :=
  PuncturedCurveGeometricPiCard ℚ

end Example36
end LeanFormal.IUT.IUTII.Frobenioid
