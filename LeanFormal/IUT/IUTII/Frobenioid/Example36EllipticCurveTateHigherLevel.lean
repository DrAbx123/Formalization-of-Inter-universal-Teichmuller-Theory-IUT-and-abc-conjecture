import LeanFormal.IUT.IUTII.Frobenioid.Example36EllipticCurveAnabelioid
import Mathlib.Tactic

/-!
# Next Tate level: the 4-torsion E[4] of y^2 = x^3 - x and its anabelioid realization

Source anchor: IUT II, Sections 3-6, boundary item (1) (geometric fundamental
group of the base curve); this file is the next finite level after the mod-2
realization of Example36EllipticCurveAnabelioid.lean.  It strengthens the
concrete finite-level Tate-module realization from E[2] to E[4] = E[2^2] for the
concrete elliptic curve y^2 = x^3 - x over the separable closure of Q.

## What is constructed and proved

* tateLevelFourTorsion : the actual 4-torsion subgroup
  {P | 4 P = 0} of the curve over the separable closure, built with the existing
  division-point API (ABCBridge/Galois/EllipticPrimeTorsionGalois.lean,
  torsionSubgroup; EllipticDivisionPolynomialEvaluation.lean for the nsmul
  membership form).  Its elements are proved to be exactly the 4-torsion points,
  the 2-torsion subgroup is proved to be contained in it, and the genuine
  level-transition map multiplicationByTwoFourToTwo : E[4] -> E[2] is defined.
* The kernel of that transition is multiplicatively/additively equivalent to
  E[2] (multiplicationByTwoKerEquiv), and E[4] is proved finite from finite
  kernel and finite range (finite_of_finite_ker_of_finite_range, a general
  additive-group lemma proved here because the tree has no packaged theorem for
  this).  Finite E[4] is then packaged as the profinite group
  tateLevelFourProfiniteGroup = E[4] with the discrete topology.
* E[4] is nontrivial: the point (0,0) (which is 2-torsion, hence 4-torsion)
  gives a nonzero element of E[4] and an element different from the identity of
  the profinite group.
* The finite-level anabelioid realization:
  tateLevelFourAnabelioid = B(E[4]),
  tateLevelFourAnabelioidTotal = B(Gal(Qbar/Q) x E[4]),
  and the pointed anabelioid morphism B(Gal x E[4]) -> B(Gal) induced by the
  genuine continuous projection (using Iut.continuousActionEtaleFundamentalGroup
  and Iut.continuousActionPointedHom, and reusing
  rationalAbsoluteGaloisGroup / rationalAbsoluteGaloisAnabelioid from the mod-2
  module).  The induced map on certified fundamental groups is proved to be the
  projection and to be surjective.
* The single-place D-prime-strip ellipticCurveTateLevelFourDPrimeStrip has Pi and
  G equal to the certified fundamental groups of B(Gal x E[4]) and B(Gal); its
  geometric kernel is proved equal to the kernel of the genuine projection and
  multiplicatively equivalent to the concrete E[4].  The kernel is nontrivial
  (an explicit element corresponding to the concrete 2-torsion point (0,0) is
  produced and proved different from the identity), so the strip has a
  nontrivial geometric kernel and is not an identity-projection strip.

## Honest boundary: what is NOT proved here

* E[4] is only proved finite; its exact cardinality 16 and the surjectivity of
  multiplication by 2 on E(K) (equivalently the division-by-2 step, i.e.
  DivisionPolynomialDetectsTorsion for n = 4 / the psi_4 torsion criterion) are
  not available in the tree and are not proved.  Consequently no explicit
  non-2-torsion 4-torsion point and no strict inclusion E[2] < E[4] are
  constructed.
* The pro-2 inverse limit T_2(E) = lim_n E[2^n] with its multiplication-by-2
  transition maps is NOT constructed: the tree provides only single-level
  torsion subgroups, no transition system E[2^{n+1}] -> E[2^n] with the
  projective-limit property, and no equality T_2(E)/2 T_2(E) = E[2] or
  T_2(E)/4 T_2(E) = E[4]; the genuine finite-level transition
  multiplicationByTwoFourToTwo is only a map of finite groups, not a map in a
  projective system.
* Continuity of the Galois action on E[4] with respect to the Krull topology
  is not constructed.  The total group realized here is the direct product
  Gal x E[4], a finite-level split product model, NOT the curve anabelioid.
  In particular this file does not realize a sequence with T_2(E) as geometric
  kernel: that old target wording was wrong, because the geometric kernel of
  the proper elliptic curve is the full Tate module prod_l T_l(E), while IUT I
  needs the whole nonabelian pi1 of the ONCE-PUNCTURED curve.  The corrected
  frozen source target is recorded in
  LeanFormal/IUT/IUTII/Frobenioid/Example36EllipticCurveSourcePiCard.lean
  (SourceCurvePiData, SourceFullTateModuleData, SourceCurvePiCard); it is not
  proved here and has no consumer.  This file does NOT prove non-splitness of
  any extension.
* No theta / q-pilot / Tate identification and no arithmetic degree, log-volume
  or comparison statement is claimed.
-/

noncomputable section

namespace LeanFormal.IUT.IUTII.Frobenioid
namespace Example36

open WeierstrassCurve

/-- The underlying point type of the concrete curve over the separable closure. -/
abbrev tateLevelFourPointType :=
  WeierstrassCurve.Affine.Point (curveY2EqX3SubX⁄tateGeometricBase)

local instance : DecidableEq tateGeometricBase := Classical.decEq tateGeometricBase

/-! ## The 4-torsion subgroup and its level transition -/

/-- The actual 4-torsion subgroup E[4] = {P | 4 P = 0} of y^2 = x^3 - x over
the separable closure of Q. -/
noncomputable abbrev tateLevelFourTorsion : AddSubgroup tateLevelFourPointType :=
  LeanFormal.IUT.ABCBridge.Galois.torsionSubgroup
    (curveY2EqX3SubX⁄tateGeometricBase) 4

theorem tateLevelFour_mem_iff {P : tateLevelFourPointType} :
    P ∈ tateLevelFourTorsion ↔ (4 : ℕ) • P = 0 :=
  LeanFormal.IUT.ABCBridge.Galois.mem_torsionSubgroup

/-- The 2-torsion subgroup is contained in the 4-torsion subgroup. -/
theorem twoTorsion_le_fourTorsion : tateLevelTwoTorsion ≤ tateLevelFourTorsion := by
  intro P hP
  rw [tateLevelFour_mem_iff]
  rw [tateLevelTwo_mem_iff] at hP
  rw [show (4:ℕ) = 2 * 2 from rfl, mul_nsmul, hP, nsmul_zero]

/-- The genuine level-transition map E[4] -> E[2], multiplication by two. -/
noncomputable def multiplicationByTwoFourToTwo :
    tateLevelFourTorsion →+ tateLevelTwoTorsion where
  toFun P := ⟨(2:ℕ) • P.1, by
    rw [tateLevelTwo_mem_iff]
    have h4 : (4:ℕ) • P.1 = 0 := tateLevelFour_mem_iff.mp P.2
    rwa [show (4:ℕ) = 2 * 2 from rfl, mul_nsmul] at h4⟩
  map_zero' := Subtype.ext (by simp)
  map_add' P Q := Subtype.ext (by
    simp only [AddSubgroup.coe_add, two_nsmul]
    abel)

/-- The kernel of the level transition E[4] -> E[2] is the 2-torsion subgroup. -/
noncomputable def multiplicationByTwoKerEquiv :
    multiplicationByTwoFourToTwo.ker ≃+ tateLevelTwoTorsion where
  toFun x := ⟨x.1.1, by
    have hx : multiplicationByTwoFourToTwo x.1 = 0 := x.2
    have h2 : (2:ℕ) • x.1.1 = 0 := congrArg Subtype.val hx
    exact tateLevelTwo_mem_iff.mpr h2⟩
  invFun Q := ⟨⟨Q.1, twoTorsion_le_fourTorsion Q.2⟩, by
    apply Subtype.ext
    exact tateLevelTwo_mem_iff.mp Q.2⟩
  left_inv x := by
    apply Subtype.ext
    apply Subtype.ext
    rfl
  right_inv Q := by
    apply Subtype.ext
    rfl
  map_add' x y := rfl

theorem multiplicationByTwoKer_finite : Finite multiplicationByTwoFourToTwo.ker :=
  Finite.of_injective multiplicationByTwoKerEquiv.toFun multiplicationByTwoKerEquiv.injective

theorem multiplicationByTwoRange_finite : Finite multiplicationByTwoFourToTwo.range :=
  Finite.of_injective (fun x : multiplicationByTwoFourToTwo.range => x.1)
    Subtype.val_injective

/-- An additive group with finite kernel and finite range along an additive
homomorphism is finite.  (The tree has no packaged theorem for this exact
statement; it is proved here from a choice of section of the range.) -/
theorem finite_of_finite_ker_of_finite_range {G H : Type*} [AddGroup G] [AddGroup H]
    (f : G →+ H) (hker : Finite f.ker) (hrange : Finite f.range) : Finite G := by
  classical
  haveI : Finite f.ker := hker
  haveI : Finite f.range := hrange
  let s : f.range → G := fun Q => Classical.choose (AddMonoidHom.mem_range.mp Q.2)
  have hs : ∀ Q : f.range, f (s Q) = Q.1 := fun Q =>
    Classical.choose_spec (AddMonoidHom.mem_range.mp Q.2)
  refine Finite.of_injective
    (fun g : G => ((⟨g - s ⟨f g, AddMonoidHom.mem_range.mpr ⟨g, rfl⟩⟩,
      (by rw [AddMonoidHom.mem_ker, map_sub, hs, sub_self] :
        g - s ⟨f g, AddMonoidHom.mem_range.mpr ⟨g, rfl⟩⟩ ∈ f.ker)⟩ : f.ker),
      (⟨f g, AddMonoidHom.mem_range.mpr ⟨g, rfl⟩⟩ : f.range))) ?_
  intro g h heq
  have hkerEq : (⟨g - s ⟨f g, AddMonoidHom.mem_range.mpr ⟨g, rfl⟩⟩,
      (by rw [AddMonoidHom.mem_ker, map_sub, hs, sub_self] :
        g - s ⟨f g, AddMonoidHom.mem_range.mpr ⟨g, rfl⟩⟩ ∈ f.ker)⟩ : f.ker) =
      ⟨h - s ⟨f h, AddMonoidHom.mem_range.mpr ⟨h, rfl⟩⟩,
      (by rw [AddMonoidHom.mem_ker, map_sub, hs, sub_self] :
        h - s ⟨f h, AddMonoidHom.mem_range.mpr ⟨h, rfl⟩⟩ ∈ f.ker)⟩ :=
    congrArg Prod.fst heq
  have hrangeEq : (⟨f g, AddMonoidHom.mem_range.mpr ⟨g, rfl⟩⟩ : f.range) =
      ⟨f h, AddMonoidHom.mem_range.mpr ⟨h, rfl⟩⟩ := congrArg Prod.snd heq
  have hsEq : s ⟨f g, AddMonoidHom.mem_range.mpr ⟨g, rfl⟩⟩ =
      s ⟨f h, AddMonoidHom.mem_range.mpr ⟨h, rfl⟩⟩ := congrArg s hrangeEq
  have hsub : g - s ⟨f g, AddMonoidHom.mem_range.mpr ⟨g, rfl⟩⟩ =
      h - s ⟨f h, AddMonoidHom.mem_range.mpr ⟨h, rfl⟩⟩ := congrArg Subtype.val hkerEq
  calc g = (g - s ⟨f g, AddMonoidHom.mem_range.mpr ⟨g, rfl⟩⟩) +
        s ⟨f g, AddMonoidHom.mem_range.mpr ⟨g, rfl⟩⟩ := (sub_add_cancel _ _).symm
    _ = (h - s ⟨f h, AddMonoidHom.mem_range.mpr ⟨h, rfl⟩⟩) +
        s ⟨f h, AddMonoidHom.mem_range.mpr ⟨h, rfl⟩⟩ := by rw [hsub, hsEq]
    _ = h := sub_add_cancel _ _

/-- The 4-torsion subgroup is finite. -/
theorem tateLevelFourTorsion_finite : Finite tateLevelFourTorsion :=
  finite_of_finite_ker_of_finite_range multiplicationByTwoFourToTwo
    multiplicationByTwoKer_finite multiplicationByTwoRange_finite

noncomputable instance tateLevelFourTorsionFinite : Finite tateLevelFourTorsion :=
  tateLevelFourTorsion_finite

/-! ## E[4] as a profinite group and its nontrivial element -/

/-- The 4-torsion subgroup as a discrete profinite group. -/
noncomputable abbrev tateLevelFourProfiniteGroup : ProfiniteGrp :=
  ProfiniteGrp.ofFiniteGrp (FiniteGrp.of (Multiplicative tateLevelFourTorsion))

theorem tateLevelFourProfiniteGroup_coe :
    (tateLevelFourProfiniteGroup : Type) = Multiplicative tateLevelFourTorsion :=
  rfl

/-- The concrete 2-torsion point (0,0), viewed as a 4-torsion point. -/
noncomputable def tateLevelFourPointZeroZero : tateLevelFourTorsion :=
  ⟨tateLevelTwoPointZeroZero.1, twoTorsion_le_fourTorsion tateLevelTwoPointZeroZero.2⟩

theorem tateLevelFourPointZeroZero_ne_zero : tateLevelFourPointZeroZero ≠ 0 := by
  intro h
  have h' : (tateLevelFourPointZeroZero : tateLevelFourPointType) = 0 :=
    congrArg Subtype.val h
  exact tateLevelTwoPointZeroZero_ne_zero (Subtype.ext h')

/-- The profinite group E[4] has a nontrivial element. -/
theorem tateLevelFourProfiniteGroup_exists_ne_one :
    ∃ x : (tateLevelFourProfiniteGroup : Type), x ≠ 1 :=
  ⟨Multiplicative.ofAdd tateLevelFourPointZeroZero, fun h =>
    tateLevelFourPointZeroZero_ne_zero (congrArg Multiplicative.toAdd h)⟩

theorem tateLevelFourProfiniteGroup_nontrivial :
    Nontrivial (tateLevelFourProfiniteGroup : Type) :=
  let ⟨x, hx⟩ := tateLevelFourProfiniteGroup_exists_ne_one
  ⟨x, 1, hx⟩

/-! ## The finite-level anabelioid and D-prime-strip at Tate level four -/

/-- The finite-level total group B(Gal(Qbar/Q) x E[4]). -/
noncomputable abbrev tateLevelFourAnabelioidTotalGroup : ProfiniteGrp :=
  profiniteProduct rationalAbsoluteGaloisGroup tateLevelFourProfiniteGroup

/-- The genuine continuous projection of the total group onto the absolute
Galois group of Q. -/
noncomputable abbrev tateLevelFourAnabelioidProjection :
    tateLevelFourAnabelioidTotalGroup ⟶ rationalAbsoluteGaloisGroup :=
  profiniteProductFst _ _

theorem tateLevelFourAnabelioidProjection_surjective :
    Function.Surjective (tateLevelFourAnabelioidProjection).hom.toMonoidHom :=
  profiniteProductFst_surjective _ _

/-- The kernel of the genuine projection is the concrete E[4]. -/
noncomputable def tateLevelFourAnabelioidProjection_kerMulEquiv :
    (tateLevelFourAnabelioidProjection).hom.toMonoidHom.ker ≃*
      (tateLevelFourProfiniteGroup : Type) :=
  prodFstKerMulEquiv rationalAbsoluteGaloisGroup (tateLevelFourProfiniteGroup : Type)

/-- The anabelioid B(E[4]). -/
noncomputable abbrev tateLevelFourAnabelioid : Iut.EtaleFundamentalGroup :=
  Iut.continuousActionEtaleFundamentalGroup tateLevelFourProfiniteGroup

/-- The anabelioid B(Gal(Qbar/Q) x E[4]). -/
noncomputable abbrev tateLevelFourAnabelioidTotal : Iut.EtaleFundamentalGroup :=
  Iut.continuousActionEtaleFundamentalGroup tateLevelFourAnabelioidTotalGroup

theorem tateLevelFourAnabelioid_group :
    tateLevelFourAnabelioid.group = tateLevelFourProfiniteGroup :=
  rfl

theorem tateLevelFourAnabelioidTotal_group :
    tateLevelFourAnabelioidTotal.group = tateLevelFourAnabelioidTotalGroup :=
  rfl

/-- The pointed anabelioid morphism B(Gal x E[4]) -> B(Gal) induced by the
genuine projection. -/
noncomputable abbrev tateLevelFourAnabelioidMorphism :
    Iut.SourcePointedAnabelioidHom tateLevelFourAnabelioidTotal
      rationalAbsoluteGaloisAnabelioid :=
  Iut.continuousActionPointedHom tateLevelFourAnabelioidProjection

/-- The map on certified fundamental groups is the genuine projection. -/
theorem tateLevelFourAnabelioidMorphism_fundamentalGroup_apply
    (x : (tateLevelFourAnabelioidTotal.group : Type)) :
    (Iut.SourcePointedAnabelioidHom.fundamentalGroupHom
        tateLevelFourAnabelioidMorphism).hom.toMonoidHom x =
      (tateLevelFourAnabelioidProjection).hom.toMonoidHom x :=
  Iut.continuousActionPointedHom_fundamentalGroupHom tateLevelFourAnabelioidProjection x

theorem tateLevelFourAnabelioidMorphism_fundamentalGroup_surjective :
    Function.Surjective (Iut.SourcePointedAnabelioidHom.fundamentalGroupHom
      tateLevelFourAnabelioidMorphism).hom.toMonoidHom := by
  intro y
  obtain ⟨x, hx⟩ := tateLevelFourAnabelioidProjection_surjective y
  exact ⟨x, by rw [tateLevelFourAnabelioidMorphism_fundamentalGroup_apply]; exact hx⟩

/-- The concrete elliptic-curve anabelioid D-prime-strip at Tate level four: its
fundamental group is the certified fundamental group of B(Gal x E[4]) and its
Galois group is the certified fundamental group of B(Gal), with the genuine
projection. -/
noncomputable def ellipticCurveTateLevelFourDPrimeStrip : DPrimeStrip Unit where
  Pi _ := tateLevelFourAnabelioidTotal.group
  groupPi _ := inferInstance
  G _ := rationalAbsoluteGaloisAnabelioid.group
  groupG _ := inferInstance
  proj _ := (tateLevelFourAnabelioidProjection).hom.toMonoidHom
  proj_surjective _ := tateLevelFourAnabelioidProjection_surjective

/-- The projection of the level-four D-prime-strip is the map on certified
fundamental groups induced by the pointed anabelioid morphism. -/
theorem ellipticCurveTateLevelFourDPrimeStrip_proj_eq_anabelioidMorphism
    (x : ellipticCurveTateLevelFourDPrimeStrip.Pi ()) :
    ellipticCurveTateLevelFourDPrimeStrip.proj () x =
      (Iut.SourcePointedAnabelioidHom.fundamentalGroupHom
        tateLevelFourAnabelioidMorphism).hom.toMonoidHom x :=
  (tateLevelFourAnabelioidMorphism_fundamentalGroup_apply x).symm

/-- The geometric kernel of the level-four D-prime-strip is the kernel of the
genuine projection. -/
theorem ellipticCurveTateLevelFourDPrimeStrip_geometric_eq_projectionKernel :
    ellipticCurveTateLevelFourDPrimeStrip.geometric () =
      (tateLevelFourAnabelioidProjection).hom.toMonoidHom.ker :=
  rfl

/-- The geometric kernel of the level-four D-prime-strip is multiplicatively
equivalent to the concrete E[4]. -/
noncomputable def ellipticCurveTateLevelFourDPrimeStrip_geometricMulEquiv :
    (ellipticCurveTateLevelFourDPrimeStrip.geometric ()) ≃*
      (tateLevelFourProfiniteGroup : Type) :=
  tateLevelFourAnabelioidProjection_kerMulEquiv

/-- The geometric kernel contains an explicit nontrivial element corresponding to
the concrete 2-torsion point (0,0). -/
noncomputable def ellipticCurveTateLevelFourDPrimeStrip_geometricPointZeroZero :
    ellipticCurveTateLevelFourDPrimeStrip.geometric () :=
  (ellipticCurveTateLevelFourDPrimeStrip_geometricMulEquiv).symm
    (Multiplicative.ofAdd tateLevelFourPointZeroZero)

theorem ellipticCurveTateLevelFourDPrimeStrip_geometricPointZeroZero_corresponds :
    ellipticCurveTateLevelFourDPrimeStrip_geometricMulEquiv
        ellipticCurveTateLevelFourDPrimeStrip_geometricPointZeroZero =
      Multiplicative.ofAdd tateLevelFourPointZeroZero :=
  (ellipticCurveTateLevelFourDPrimeStrip_geometricMulEquiv).apply_symm_apply _

theorem ellipticCurveTateLevelFourDPrimeStrip_geometricPointZeroZero_ne_one :
    (ellipticCurveTateLevelFourDPrimeStrip_geometricPointZeroZero :
        ellipticCurveTateLevelFourDPrimeStrip.Pi ()) ≠ 1 := by
  intro h
  have h1 := ellipticCurveTateLevelFourDPrimeStrip_geometricPointZeroZero_corresponds
  have hy : ellipticCurveTateLevelFourDPrimeStrip_geometricPointZeroZero = 1 :=
    Subtype.ext h
  rw [hy, map_one] at h1
  have h2 : tateLevelFourPointZeroZero = 0 := congrArg Multiplicative.toAdd h1.symm
  exact tateLevelFourPointZeroZero_ne_zero h2

theorem ellipticCurveTateLevelFourDPrimeStrip_geometric_nontrivialElement :
    ∃ x : ellipticCurveTateLevelFourDPrimeStrip.Pi (),
      x ∈ ellipticCurveTateLevelFourDPrimeStrip.geometric () ∧ x ≠ 1 :=
  ⟨ellipticCurveTateLevelFourDPrimeStrip_geometricPointZeroZero,
    ellipticCurveTateLevelFourDPrimeStrip_geometricPointZeroZero.2,
    ellipticCurveTateLevelFourDPrimeStrip_geometricPointZeroZero_ne_one⟩

theorem ellipticCurveTateLevelFourDPrimeStrip_geometric_ne_bot :
    ellipticCurveTateLevelFourDPrimeStrip.geometric () ≠ ⊥ := by
  obtain ⟨x, hxmem, hxne⟩ :=
    ellipticCurveTateLevelFourDPrimeStrip_geometric_nontrivialElement
  intro hbot
  exact hxne (Subgroup.mem_bot.mp (hbot ▸ hxmem))

theorem ellipticCurveTateLevelFourDPrimeStrip_hasNontrivialGeometricKernel :
    HasNontrivialGeometricKernel ellipticCurveTateLevelFourDPrimeStrip :=
  ⟨(), ellipticCurveTateLevelFourDPrimeStrip_geometric_ne_bot⟩

/-- The 2-torsion point (0,0) is a nonzero element of E[4]. -/
theorem tateLevelFourTorsion_exists_ne_zero :
    ∃ x : tateLevelFourTorsion, x ≠ 0 :=
  ⟨tateLevelFourPointZeroZero, tateLevelFourPointZeroZero_ne_zero⟩

/-- The level-transition kernel statement: the kernel of E[4] -> E[2] is the
2-torsion subgroup. -/
theorem multiplicationByTwoKerEquiv_coe (x : multiplicationByTwoFourToTwo.ker) :
    (multiplicationByTwoKerEquiv x : tateLevelFourPointType) = x.1.1 :=
  rfl

end Example36
end LeanFormal.IUT.IUTII.Frobenioid
