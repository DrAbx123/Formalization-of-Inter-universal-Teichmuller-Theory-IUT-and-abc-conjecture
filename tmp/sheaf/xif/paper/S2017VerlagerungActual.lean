import tmp.sheaf.xif.paper.S2011Cor110bActual
import Mathlib.GroupTheory.Transfer
import Mathlib.FieldTheory.Galois.Profinite

/-!
# S2017: the Verlagerung/transfer package and mu_{Q/Z}(G_v)

Layer: **O** (original Theta-link / q-pilot).  Consumer: the S2011 package
(tmp/sheaf/xif/paper/S2011Cor110bActual.lean), whose missing item (M1) is
superseded here, and through it the [AbsTopIII] Corollary 1.10 interface of
S2000/S2011.

## The source object

[AbsTopIII], Corollary 1.10, (a): for a profinite group G_k,

  mu_{Q/Z}(G_k) := colim_H (H^ab)_tors,
  mu_hat^Z(G_k) := Hom(Q/Z, mu_{Q/Z}(G_k)),

where H runs over the open subgroups of G_k and the transition maps are the
Verlagerung (transfer) maps.

## The correction to S2011's (M1)

S2011 records (M1) as: Mathlib contains no Verlagerung for a finite-index
subgroup, so the colimit cannot be formed.  That statement is false for the
Mathlib revision pinned by this project (v4.32.2): `MonoidHom.transfer` in
`Mathlib.GroupTheory.Transfer` (Thomas Browning) is exactly the transfer
homomorphism.  For `H : Subgroup G` with `[H.FiniteIndex]` and a commutative
target A it gives `G ->* A`; with A = Abelianization H and the canonical map
`H ->* Abelianization H` it gives the Verlagerung

  transferAb H : Abelianization G ->* Abelianization H.

Mathlib builds it from a left transversal (`Subgroup.leftTransversals.diff`);
`transferAb_of_eq_diff` below exposes that transversal formula, and
`map_subtype_comp_transferAb` records the standard bookkeeping identity
`res o V = [G:H]` on G^ab, where res is induced by the inclusion H -> G.

**Direction.**  The Verlagerung goes from the bigger group to the smaller:
for H <= K one has V : K^ab -> H^ab, not H^ab -> G^ab.  Consequently the
source's colimit over open subgroups is the colimit over the order dual of
the subgroup lattice: as the subgroup decreases (equivalently, as the fixed
field increases) the transfer maps are the transition maps.  The colimit
below is built in exactly this direction.

## What is constructed (unconditional, no sorry, no axiom)

* `Verlagerung.transferAb`, its transversal formula, and
  `res o V = index` on abelianizations;
* `torsionMap`, the restriction of a group homomorphism to torsion subgroups;
* for open subgroups H <= K of G_v = Gal(Qbar_p/Q_p), the transfer
  `verlagerungOpen h : Abelianization K ->* Abelianization H` and its torsion
  version `toStage h : (K^ab)_tors -> (H^ab)_tors`;
* the direct limit `muQZ p` of the groups `(H^ab)_tors` over all open
  subgroups, as the quotient of their direct sum by the transfer relations,
  together with the cocone maps `muQZof` and the universal property
  `muQZ_lift` / `muQZ_lift_of` / `muQZ_lift_unique`;
* `muHatZ p := KummerCyclotome (Multiplicative (muQZ p))`, i.e.
  `Hom(Q/Z, mu_{Q/Z}(G_v))` in the notation of the source;
* the comparison propositions `muQZComparison p` and `muHatComparison p`.

The colimit is the universal object: any family of homomorphisms out of the
torsion abelianizations which is compatible with all transfer maps factors
uniquely through `muQZ p` (`muQZ_lift`, with computation rule
`muQZ_lift_of`).  No directedness hypothesis is needed for this quotient
construction; composition relations among transfers are automatic in the
quotient and are not assumed.

## Exact first missing after this package (not assumed here)

(M2) **Local reciprocity on torsion, with transfer compatibility.**  The
     levelwise identification `(H^ab)_tors = mu(FixedField H)` is stated in
     S2011 as `localReciprocityOnTorsion p`; still missing is its
     compatibility with the transfer maps, i.e. that under these
     identifications the transfer is the inclusion of the roots of unity of
     the smaller fixed field into those of the larger one.  This is local
     class field theory on torsion, not formal group theory.  As in S2011,
     `Abelianization U` is the abstract abelianization, while the source's
     `(U^ab)` is the profinite (closed-commutator) abelianization; that
     caveat remains part of (M2).

(M3) **Continuous H^2 and H^2(G_v, mu_hat^Z) = Z-hat.**  As recorded in
     S2011: no continuous H^2 and no Z-hat exist in the tree; the source
     computation is lim_n Br(k_v)[n].  Not statable here, so no declaration
     is fabricated for it.

(M4) **The normalized surjection** H^1(G_v, mu_hat^Z) ->> Z-hat.  S2011's
     `weakFrobeniusNormalization p` remains the strongest statable form.

(M5) **Joint continuity of the G_v-action**: no topology is put on the
     limit in this tree.

(M6) **Model caveat**: the tree Kummer image is that of O^tri_{Qbar_p}; the
     source statement (d) is about k_v^times inside the limit.

`muHatComparison p` below is the precise remaining comparison of the
group-theoretic cyclotome with the actual cyclotome `PsiCnsTorsionCyclotome`
of S2000; it is a proposition, neither proved nor assumed.

## Not run

Full Project build, target comparator, independent review, and the
[AbsTopIII] H^2 construction were not run.
-/

set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 800000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.checkUnivs false

noncomputable section
open scoped DirectSum
open LeanFormal.IUT
open LeanFormal.IUT.LocalMLFModelTMPair
open LeanFormal.IUT.XiFPaper.S2000CohomologicalPsiCnsActual
open LeanFormal.IUT.XiFPaper.S2011Cor110bActual

namespace LeanFormal.IUT.XiFPaper.S2017VerlagerungActual

variable (p : Nat) [Fact (Nat.Prime p)]

/-! ## 1. The Verlagerung on abelianizations -/

namespace Verlagerung

variable {G : Type*} [Group G] (H : Subgroup G) [H.FiniteIndex]

/-- The Verlagerung (transfer) from `G^ab` to `H^ab` for a finite-index
subgroup `H`, obtained from Mathlib's `MonoidHom.transfer` with target the
abelianization of `H`. -/
noncomputable def transferAb : Abelianization G →* Abelianization H :=
  Abelianization.lift (MonoidHom.transfer (Abelianization.of (G := H)))

theorem transferAb_of (g : G) :
    transferAb H (Abelianization.of g) =
      MonoidHom.transfer (Abelianization.of (G := H)) g := rfl

/-- The transfer is the difference of the left transversals `T` and `g • T`,
which is Mathlib's explicit transversal formula. -/
theorem transferAb_of_eq_diff (T : H.LeftTransversal) (g : G) :
    transferAb H (Abelianization.of g) =
      Subgroup.leftTransversals.diff (Abelianization.of (G := H)) T (g • T) := by
  rw [transferAb_of, MonoidHom.transfer_def]

/-- The transfer bookkeeping identity `res o V = [G:H]` on `G^ab`: composing
the Verlagerung with the map induced by the inclusion `H -> G` is the
`H.index`-th power map.  The proof uses the orbit product formula for the
transfer and `Subgroup.index_eq_sum_minimalPeriod`. -/
theorem map_subtype_transferAb_of (g : G) :
    Abelianization.map H.subtype (transferAb H (Abelianization.of g)) =
      Abelianization.of (g ^ H.index) := by
  classical
  letI : Fintype (Quotient (MulAction.orbitRel (Subgroup.zpowers g) (G ⧸ H))) :=
    Fintype.ofFinite _
  rw [transferAb_of, MonoidHom.transfer_eq_prod_quotient_orbitRel_zpowers_quot]
  simp only [map_prod, Abelianization.map_of, Subgroup.coe_subtype]
  have hfactor : ∀ q : Quotient (MulAction.orbitRel (Subgroup.zpowers g) (G ⧸ H)),
      Abelianization.of ((Quotient.out q.out)⁻¹ * g ^
          Function.minimalPeriod (fun x => g • x) q.out * Quotient.out q.out) =
        Abelianization.of (g ^ Function.minimalPeriod (fun x => g • x) q.out) := by
    intro q
    simp only [map_mul, map_inv, map_pow]
    rw [mul_comm (Abelianization.of (Quotient.out q.out))⁻¹, mul_assoc,
      inv_mul_cancel, mul_one]
  simp_rw [hfactor]
  calc
    ∏ x : Quotient (MulAction.orbitRel (Subgroup.zpowers g) (G ⧸ H)),
        Abelianization.of (g ^ Function.minimalPeriod (fun y => g • y) x.out)
        = ∏ x : Quotient (MulAction.orbitRel (Subgroup.zpowers g) (G ⧸ H)),
            (Abelianization.of g) ^ Function.minimalPeriod (fun y => g • y) x.out := by
          apply Finset.prod_congr rfl
          intro x _
          rw [map_pow]
    _ = (Abelianization.of g) ^ H.index := by
          rw [Finset.prod_pow_eq_pow_sum, ← H.index_eq_sum_minimalPeriod]
    _ = Abelianization.of (g ^ H.index) := by rw [map_pow]

/-- The map `g |-> g ^ [G:H]` from `G` to `G^ab`. -/
noncomputable def powIndexHom : G →* Abelianization G where
  toFun g := Abelianization.of (g ^ H.index)
  map_one' := by simp
  map_mul' g h := by
    rw [map_pow, map_mul, mul_pow, map_pow, map_pow]

theorem map_subtype_comp_transferAb_apply (x : Abelianization G) :
    Abelianization.map H.subtype (transferAb H x) =
      Abelianization.lift (powIndexHom H) x :=
  Abelianization.lift_unique (powIndexHom H)
    ((Abelianization.map H.subtype).comp (transferAb H))
    (fun g => map_subtype_transferAb_of H g)

/-- Hom-level form of `map_subtype_transferAb_of`. -/
theorem map_subtype_comp_transferAb :
    (Abelianization.map H.subtype).comp (transferAb H) =
      Abelianization.lift (powIndexHom H) :=
  MonoidHom.ext (fun x => map_subtype_comp_transferAb_apply H x)

end Verlagerung

/-! ## 2. Open subgroups and the transfer on torsion -/

/-- Every open subgroup of the local absolute Galois group has finite index.
This is where compactness of `G_v` enters: a compact group modulo an open
subgroup is finite. -/
theorem openSubgroup_finiteIndex (H : OpenSubgroup (LocalAbsoluteGalois p)) :
    (H : Subgroup (LocalAbsoluteGalois p)).FiniteIndex := by
  haveI : Finite (LocalAbsoluteGalois p ⧸ (H : Subgroup (LocalAbsoluteGalois p))) :=
    Subgroup.quotient_finite_of_isOpen (H : Subgroup (LocalAbsoluteGalois p)) H.isOpen
  exact Subgroup.finiteIndex_of_finite_quotient

/-- Restriction of a homomorphism of commutative groups to their torsion
subgroups. -/
noncomputable def torsionMap {A B : Type*} [CommGroup A] [CommGroup B] (f : A →* B) :
    CommGroup.torsion A →* CommGroup.torsion B where
  toFun x := ⟨f (x : A), f.isOfFinOrder x.2⟩
  map_one' := Subtype.ext (map_one f)
  map_mul' x y := Subtype.ext (map_mul f (x : A) (y : A))

abbrev Index := OpenSubgroup (LocalAbsoluteGalois p)

abbrev Stage (H : Index p) := Additive (CommGroup.torsion (Abelianization H))

/-- The Verlagerung between two open subgroups `H <= K`, on abelianizations. -/
noncomputable def verlagerungOpen {H K : Index p} (h : H ≤ K) :
    Abelianization K →* Abelianization H := by
  haveI hH : (H : Subgroup (LocalAbsoluteGalois p)).FiniteIndex :=
    openSubgroup_finiteIndex p H
  haveI hHK : (((H : Subgroup (LocalAbsoluteGalois p)).subgroupOf
      (K : Subgroup (LocalAbsoluteGalois p)))).FiniteIndex := inferInstance
  exact Abelianization.lift (MonoidHom.transfer
    ((Abelianization.of (G := H)).comp (Subgroup.subgroupOfEquivOfLe h).toMonoidHom))

/-- The transfer between the torsion parts of two open subgroups, in the
actual direction `K^ab -> H^ab` for `H <= K`. -/
noncomputable def toStage {H K : Index p} (h : H ≤ K) (v : Stage p K) : Stage p H :=
  Additive.ofMul (torsionMap (verlagerungOpen p h) (Additive.toMul v))

/-! ## 3. The direct limit mu_{Q/Z}(G_v) -/

/-- The transfer relations in the direct sum of the torsion abelianizations.
`H K` range over open subgroups with `H <= K`; the relation identifies the
class of `v` in `(K^ab)_tors` with the class of its transfer in `(H^ab)_tors`. -/
noncomputable def relSet : Set (⨁ H : Index p, Stage p H) := by
  classical
  exact {x | ∃ (H K : Index p) (h : H ≤ K) (v : Stage p K),
    x = DirectSum.of (Stage p) K v - DirectSum.of (Stage p) H (toStage p h v)}

noncomputable def muQZRel : AddSubgroup (⨁ H : Index p, Stage p H) :=
  AddSubgroup.closure (relSet p)

/-- `mu_{Q/Z}(G_v) = colim_H (H^ab)_tors`, in the transfer direction (order
dual of the open-subgroup lattice), as a quotient of the direct sum by the
transfer relations. -/
noncomputable abbrev muQZ := (⨁ H : Index p, Stage p H) ⧸ muQZRel p

/-- The canonical map from a stage `(H^ab)_tors` to `mu_{Q/Z}(G_v)`. -/
noncomputable def muQZof (H : Index p) : Stage p H →+ muQZ p := by
  classical
  exact (QuotientAddGroup.mk' (muQZRel p)).comp (DirectSum.of (Stage p) H)

/-- The defining compatibility of the colimit: the transfer `K^ab -> H^ab`
becomes the identity after passing to `mu_{Q/Z}(G_v)`. -/
theorem muQZof_transfer {H K : Index p} (h : H ≤ K) (v : Stage p K) :
    muQZof p H (toStage p h v) = muQZof p K v := by
  classical
  change (QuotientAddGroup.mk ((DirectSum.of (Stage p) H) (toStage p h v)) : muQZ p) =
    QuotientAddGroup.mk ((DirectSum.of (Stage p) K) v)
  rw [QuotientAddGroup.eq_iff_sub_mem]
  have hmem : DirectSum.of (Stage p) K v - DirectSum.of (Stage p) H (toStage p h v) ∈
      muQZRel p := AddSubgroup.subset_closure ⟨H, K, h, v, rfl⟩
  simpa using neg_mem hmem

/-- **Universal property of `mu_{Q/Z}(G_v)`.**  A family of homomorphisms out
of the torsion abelianizations which is compatible with all transfer maps
factors through the colimit. -/
noncomputable def muQZ_lift (A : Type) [AddCommGroup A]
    (f : ∀ H : Index p, Stage p H →+ A)
    (hf : ∀ {H K : Index p} (h : H ≤ K) (v : Stage p K),
      f H (toStage p h v) = f K v) :
    muQZ p →+ A := by
  classical
  refine QuotientAddGroup.lift (muQZRel p) (DirectSum.toAddMonoid (fun H => f H)) ?_
  change AddSubgroup.closure (relSet p) ≤ _
  rw [AddSubgroup.closure_le]
  rintro _ ⟨H, K, h, v, rfl⟩
  apply AddMonoidHom.mem_ker.mpr
  simp only [AddMonoidHom.map_sub, DirectSum.toAddMonoid_of, hf h v, sub_self]

/-- The computation rule of the universal property. -/
theorem muQZ_lift_of (A : Type) [AddCommGroup A]
    (f : ∀ H : Index p, Stage p H →+ A)
    (hf : ∀ {H K : Index p} (h : H ≤ K) (v : Stage p K),
      f H (toStage p h v) = f K v)
    (H : Index p) (v : Stage p H) :
    muQZ_lift p A f hf (muQZof p H v) = f H v := by
  classical
  rw [muQZ_lift]
  rw [muQZof, AddMonoidHom.comp_apply, QuotientAddGroup.mk'_apply]
  rw [QuotientAddGroup.lift_mk']
  exact DirectSum.toAddMonoid_of (fun H => f H) H v

/-- Uniqueness part of the universal property: an additive homomorphism out of
the colimit is determined by its composites with the cocone maps `muQZof`. -/
theorem muQZ_lift_unique (A : Type) [AddCommGroup A]
    (f : ∀ H : Index p, Stage p H →+ A)
    (hf : ∀ {H K : Index p} (h : H ≤ K) (v : Stage p K),
      f H (toStage p h v) = f K v)
    (g : muQZ p →+ A)
    (hg : ∀ (H : Index p) (v : Stage p H), g (muQZof p H v) = f H v) :
    g = muQZ_lift p A f hf := by
  classical
  apply AddMonoidHom.ext
  intro x
  induction x using QuotientAddGroup.induction_on with
  | _ z =>
    change (g.comp (QuotientAddGroup.mk' (muQZRel p))) z =
      muQZ_lift p A f hf ((QuotientAddGroup.mk' (muQZRel p)) z)
    have hfam : (fun H : Index p =>
        (g.comp (QuotientAddGroup.mk' (muQZRel p))).comp (DirectSum.of (Stage p) H)) = f := by
      funext H
      ext v
      exact hg H v
    rw [DirectSum.toAddMonoid.unique (ψ := g.comp (QuotientAddGroup.mk' (muQZRel p))), hfam]
    rw [muQZ_lift, QuotientAddGroup.mk'_apply, QuotientAddGroup.lift_mk']

/-! ## 4. mu_hat^Z(G_v) and the remaining comparison -/

/-- `mu_hat^Z(G_v) = Hom(Q/Z, mu_{Q/Z}(G_v))`, in multiplicative notation:
the `KummerCyclotome` of the multiplicative version of the colimit. -/
abbrev muHatZ : Type := KummerCyclotome (Multiplicative (muQZ p))

/-- The comparison of the group-theoretic cyclotome with the actual one of
S2000, `Hom(Q/Z, mu)` of the torsion units of the local integral monoid.
This is the remaining local-reciprocity input; it is stated as a
proposition, neither proved nor assumed. -/
def muHatComparison : Prop :=
  Nonempty (muHatZ p ≃* PsiCnsTorsionCyclotome p)

/-- The underlying torsion-group comparison: local reciprocity identifies
`mu_{Q/Z}(G_v)` with the torsion subgroup of the units of the algebraic
closure.  This is exactly the missing identification behind
`muHatComparison`. -/
def muQZComparison : Prop :=
  Nonempty (muQZ p ≃+ Additive (CommGroup.torsion (Otri p)ˣ))

/-- S2011's levelwise local reciprocity statement, recalled here as the next
missing input.  The transfer compatibility of these levelwise
identifications (the transfer corresponds to the inclusion of roots of
unity of the smaller fixed field into those of the larger one) is the
refinement still missing. -/
abbrev localReciprocityMissing : Prop := localReciprocityOnTorsion p

/-! The paper's H^2 normalization (M3) is not statable in this tree: there
is no continuous H^2 and no Z-hat.  No declaration is fabricated for it. -/

/-! ## 5. Axiom probes -/

#print axioms Verlagerung.transferAb
#print axioms Verlagerung.transferAb_of_eq_diff
#print axioms Verlagerung.map_subtype_transferAb_of
#print axioms Verlagerung.map_subtype_comp_transferAb
#print axioms openSubgroup_finiteIndex
#print axioms torsionMap
#print axioms verlagerungOpen
#print axioms muQZof
#print axioms muQZof_transfer
#print axioms muQZ_lift
#print axioms muQZ_lift_of
#print axioms muQZ_lift_unique
#print axioms muHatZ
#print axioms muHatComparison

end LeanFormal.IUT.XiFPaper.S2017VerlagerungActual

