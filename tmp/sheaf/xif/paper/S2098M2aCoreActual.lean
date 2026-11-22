/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/

import tmp.sheaf.xif.paper.S2089FiniteAbelianSubextensionActual
import tmp.sheaf.xif.paper.S2093ArtinM2aBridge
import Reciprocity.ProfiniteCompletion
import Reciprocity.GaloisStructure

/-!
# S2098: M2a-core of local reciprocity for one finite L / Q_p, actually inhabited

Layer: **O** (original Theta-link / q-pilot).  Consumers: S2027
(`localReciprocityIsomorphism`, `localArtinTorsion`, `LocalArtinSourceData`),
S2024 (`LocalReciprocityData` and through it S2011/S2017), and the [AbsTopIII]
Corollary 1.10 interface.

S2050/S2056 located the exact missing M2a bridge: LANA's local-CFT carrier
`PadicField.artin : K^x ->* Gal(PadicField.maxAbelian K Omega / K)` and S2027's
infinite-Galois carrier `Gal(maximalAbelianExtension U / localField U)` were two
different objects.  S2089 proved

  `maxAbelian_eq_maximalAbelianExtension : PadicField.maxAbelian E Omega =
    maximalAbelianExtension p U`

with the induced field equivalence and the Galois-group equivalence
`galoisGroupEquiv : Gal(maxAbelian / E) ~= Gal(maximalAbelianExtension / E)`.

This file is **S2089 + M2a-core**.  Nothing below is assumed or fabricated: every
declaration is either proved here or is an explicitly named proposition recording
a gap; no `sorry`, `admit` or new `axiom` is introduced.

## 1. The Artin map on S2027's carrier (unconditional)

`artinMaximalAbelian U : (localField p U)^x ->* Gal(maximalAbelianExtension U / localField U)`
is `PadicField.artin` conjugated by `galoisGroupEquiv`.  Its kernel is the
intersection of the norm groups of the finite abelian subextensions
(`artinMaximalAbelian_eq_one_iff`), and on a finite abelian level `M` it acts by
`PadicField.abRec` (`artinMaximalAbelian_apply`).

## 2. `localReciprocityIsomorphism` is inhabited (unconditional)

LANA already proves that the Artin map extends to an isomorphism of topological
groups from the profinite completion of `K^x` onto `Gal(K^ab/K)`
(`PadicField.artinCompletionEquiv`, in `Reciprocity/ProfiniteCompletion.lean`;
its proof consumes the local existence theorem `PadicField.existence` and
`PadicField.denseRange_artin`).  Transporting it along S2089's
`galoisGroupEquiv` gives

  `unitProfiniteCompletionEquivGal U : unitProfiniteCompletion p U ~=*
     Gal(maximalAbelianExtension p U / localField p U)`,

which is exactly S2027's (M2a-core) `localReciprocityIsomorphism p U`:

  `localReciprocityIsomorphism_holds : localReciprocityIsomorphism p U`.

The square `unitProfiniteCompletionEquivGal_eta` records that this is the
*reciprocity* isomorphism and not an arbitrary one: composed with
`L^x -> L^x-hat` it is the Artin map `artinMaximalAbelian`.

## 3. `localArtinTorsion` is inhabited (unconditional)

S2027 recorded (M2a-torsion) as missing: `torsion (L^x-hat) ~= mu(L)`.  The
structure theory of `L^x` itself is indeed absent from the tree, but LANA's
`galAbEquiv : Gal(K^ab/K) ~= O^x x Zhat` (after choosing a uniformiser) reduces
the torsion computation to three elementary facts, all proved here:

* `Brauer.ZHat` is torsion free additively (`zhat_nsmul_eq_zero`), hence
  `Multiplicative Zhat` has no nontrivial torsion (`zhat_isOfFinOrder_eq_one`);
* every root of unity has absolute value one (`nrm_coe_eq_one_of_isOfFinOrder`),
  so `torsion O^x` is `torsion K^x = mu(L)` (`torsionUnitGroupEquivMu`);
* torsion splits off a torsion-free factor (`torsionProdOfRightTorsionFree`).

Composing those with `torsionMulEquiv` of `galAbEquiv` and of `galoisGroupEquiv`
yields the Artin-induced

  `localArtinTorsionEquiv U : mu p U ~=* torsion (Gal(maxAbelianExt / L))`

and consequently `localArtinTorsion_holds : localArtinTorsion p U`.

## 4. `LocalArtinSourceData` and S2024's `LocalReciprocityData`

The `artin` field of `LocalArtinSourceData` is constructed unconditionally
(`localArtinSourceArtin`), via `galoisGroupMaximalAbelian`.  The `carrier` field
is exactly S2027's recorded (M2c): the comparison of the torsion of the
*abstract* abelianization `Abelianization U` with the torsion of the *profinite*
abelianization `TopologicalAbelianization (Gal(Qbar_p/L))`.
`abelianizationToTopological` is only known to be surjective, and injectivity on
torsion is not derivable from the tree.  Hence `LocalArtinSourceData` is
constructed from (M2c) (`localArtinSourceDataOfComparison`), (M2c) is recorded as
the first missing piece (`localArtinSourceCarrierMissing`), and together with
(M2b) -- the transfer compatibility, literally S2024's `transfer_compat` -- this
yields S2024's `LocalReciprocityData p` (`localReciprocityData_of_source`) and the
S2017 consequences `muQZComparison` and `muHatComparison`.

## Dependencies consumed

`Reciprocity.Artin`, `Reciprocity.ProfiniteCompletion`,
`Reciprocity.GaloisStructure`, `Reciprocity.ArtinInertia`,
`Reciprocity.ExistenceTheorem` (local existence), S2027, S2089.

## Not run

Full Project build, target comparator, independent review, and the [AbsTopIII]
H^2 construction.  (M2c) and (M2b) are stated, not proved.
-/

set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 800000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

noncomputable section

open IntermediateField
open LeanFormal.IUT.XiFPaper.S2017VerlagerungActual
open LeanFormal.IUT.XiFPaper.S2024LocalReciprocityActual
open LeanFormal.IUT.XiFPaper.S2027LocalArtinActual
open LeanFormal.IUT.XiFPaper.S2089FiniteAbelianSubextensionActual
open LeanFormal.IUT.XiFPaper.S2011Cor110bActual
open LeanFormal.IUT.XiFPaper.S2056MaxAbelianBridge

namespace LeanFormal.IUT.XiFPaper.S2098M2aCoreActual

variable {p : Nat} [Fact (Nat.Prime p)]
variable (U : Index p)

/-! ## 1. The Artin map on S2027's carrier -/

/-- **M2a step (1).**  LANA's Artin map `K^x ->* Gal(K^ab / K)`, retyped along
S2089's field equivalence to S2027's carrier
`Gal(maximalAbelianExtension / L)`. -/
noncomputable def artinMaximalAbelian (U : Index p) :
    (localField p U)ˣ →* Gal(↥(maximalAbelianExtension p U) / localField p U) :=
  (galoisGroupEquiv U).toMonoidHom.comp
    (PadicField.artin p (localField p U) (AlgebraicClosure ℚ_[p]))

/-- Unfolding lemma for `artinMaximalAbelian`. -/
theorem artinMaximalAbelian_def (x : (localField p U)ˣ) :
    artinMaximalAbelian U x =
      galoisGroupEquiv U
        (PadicField.artin p (localField p U) (AlgebraicClosure ℚ_[p]) x) :=
  rfl

/-- **The Artin map acts by finite-level reciprocity.**  On a finite abelian
subextension `M / L` of `Qbar_p`, `artinMaximalAbelian U x` acts as
`PadicField.abRec M.1 x`. -/
theorem artinMaximalAbelian_apply (x : (localField p U)ˣ)
    (M : PadicField.AbFin (localField p U) (AlgebraicClosure ℚ_[p]))
    (y : AlgebraicClosure ℚ_[p]) (hy : y ∈ M.1) :
    ((artinMaximalAbelian U x)
        ⟨y, maxAbelian_le_maximalAbelianExtension U (PadicField.le_maxAbelian M hy)⟩ :
        AlgebraicClosure ℚ_[p]) =
      ((PadicField.abRec p M.1 x ⟨y, hy⟩ : M.1) : AlgebraicClosure ℚ_[p]) := by
  have hsymm : ((maxAbelianEquivMaximalAbelianExtension (p := p) U).symm
      ⟨y, maxAbelian_le_maximalAbelianExtension U (PadicField.le_maxAbelian M hy)⟩ :
        PadicField.maxAbelian (localField p U) (AlgebraicClosure ℚ_[p])) =
      ⟨y, PadicField.le_maxAbelian M hy⟩ :=
    Subtype.ext rfl
  rw [artinMaximalAbelian_def, galoisGroupEquiv_apply, hsymm,
    maxAbelianEquivMaximalAbelianExtension_apply]
  exact PadicField.artin_apply x M.1 y hy

/-- **The kernel of the Artin map is the intersection of the norm groups.** -/
theorem artinMaximalAbelian_eq_one_iff (x : (localField p U)ˣ) :
    artinMaximalAbelian U x = 1 ↔
      ∀ M : PadicField.AbFin (localField p U) (AlgebraicClosure ℚ_[p]),
        x ∈ PadicField.normGroup (localField p U) M.1 := by
  rw [artinMaximalAbelian_def, MulEquiv.map_eq_one_iff, ← MonoidHom.mem_ker,
    PadicField.mem_ker_artin_iff]

/-! ## 2. M2a-core: the reciprocity isomorphism -/

/-- **M2a-core, the isomorphism.**  LANA's isomorphism of topological groups
`K^x-hat ~= Gal(K^ab/K)` (`PadicField.artinCompletionEquiv`), transported to
S2027's carriers by S2089's `galoisGroupEquiv`. -/
noncomputable def unitProfiniteCompletionEquivGal (U : Index p) :
    unitProfiniteCompletion p U ≃*
      Gal(↥(maximalAbelianExtension p U) / localField p U) :=
  ((PadicField.artinCompletionEquiv p (localField p U) (AlgebraicClosure ℚ_[p])).toMulEquiv).trans
    (galoisGroupEquiv U)

/-- `unitToCompletion` is the canonical map `etaFn` of the profinite completion. -/
theorem unitToCompletion_eq_etaFn (x : (localField p U)ˣ) :
    unitToCompletion p U x =
      ProfiniteGrp.ProfiniteCompletion.etaFn (GrpCat.of (localField p U)ˣ) x :=
  rfl

/-- **The reciprocity isomorphism extends the Artin map.**  This is what makes
`unitProfiniteCompletionEquivGal` the *reciprocity* isomorphism: composed with
`L^x -> L^x-hat` it is `artinMaximalAbelian`. -/
@[simp]
theorem unitProfiniteCompletionEquivGal_eta (x : (localField p U)ˣ) :
    unitProfiniteCompletionEquivGal U (unitToCompletion p U x) = artinMaximalAbelian U x := by
  rw [unitProfiniteCompletionEquivGal, MulEquiv.trans_apply, artinMaximalAbelian_def]
  exact congrArg (fun y => galoisGroupEquiv U y)
    (PadicField.artinCompletionEquiv_eta x)

/-- **M2a-core holds.**  S2027's `localReciprocityIsomorphism p U` is inhabited. -/
theorem localReciprocityIsomorphism_holds (U : Index p) :
    localReciprocityIsomorphism p U :=
  ⟨unitProfiniteCompletionEquivGal U⟩

/-! ## 3. Torsion: `Zhat` is torsion free, and `torsion O^x = mu(L)` -/

/-- **`Zhat` is torsion free additively.**  If `n • a = 0` for `a : Zhat` and
`n != 0` then `a = 0`.  Proved from the defining projective system
`Zhat -> ZMod (m * n) -> ZMod m`: `n • a = 0` at level `m * n` forces the class
of `a` at level `m` to vanish. -/
theorem zhat_nsmul_eq_zero {a : Brauer.ZHat} {n : ℕ} (hn : n ≠ 0) (h : n • a = 0) :
    a = 0 := by
  apply Brauer.ZHat.ext
  intro m
  set M : ℕ+ := ⟨m.val * n, Nat.mul_pos m.pos (Nat.pos_of_ne_zero hn)⟩ with hM
  have hMn : (M : ℕ) = m.val * n := rfl
  have hx0 : (n : ℕ) • ((a : ∀ k : ℕ+, ZMod k) M) = 0 := by
    have h1 := congrArg (fun z : Brauer.ZHat => (z : ∀ k : ℕ+, ZMod k) M) h
    simpa using h1
  haveI : NeZero (M : ℕ) := ⟨Nat.pos_iff_ne_zero.mp M.pos⟩
  have hcast : ((n * ((a : ∀ k : ℕ+, ZMod k) M).val : ℕ) : ZMod (M : ℕ)) = 0 := by
    have h2 : (n : ZMod (M : ℕ)) * ((a : ∀ k : ℕ+, ZMod k) M) = 0 := by
      rw [← nsmul_eq_mul]
      exact hx0
    calc ((n * ((a : ∀ k : ℕ+, ZMod k) M).val : ℕ) : ZMod (M : ℕ))
        = (n : ZMod (M : ℕ)) * (((a : ∀ k : ℕ+, ZMod k) M).val : ZMod (M : ℕ)) := by
          rw [Nat.cast_mul]
      _ = (n : ZMod (M : ℕ)) * ((a : ∀ k : ℕ+, ZMod k) M) := by rw [ZMod.natCast_zmod_val]
      _ = 0 := h2
  have hdvd : (M : ℕ) ∣ n * ((a : ∀ k : ℕ+, ZMod k) M).val :=
    (ZMod.natCast_eq_zero_iff _ _).mp hcast
  have hdvdm : m.val ∣ ((a : ∀ k : ℕ+, ZMod k) M).val := by
    have hdvd' : m.val * n ∣ n * ((a : ∀ k : ℕ+, ZMod k) M).val := hdvd
    rw [Nat.mul_comm (n := m.val) (m := n)] at hdvd'
    exact Nat.dvd_of_mul_dvd_mul_left (Nat.pos_of_ne_zero hn) hdvd'
  have hmem : (m : ℕ) ∣ (M : ℕ) := ⟨n, hMn⟩
  rw [← Brauer.ZHat.castHom_apply a hmem]
  rw [ZMod.castHom_apply, ZMod.cast_eq_val]
  exact (ZMod.natCast_eq_zero_iff _ _).mpr hdvdm

/-- **`Multiplicative Zhat` has no nontrivial torsion.** -/
theorem zhat_isOfFinOrder_eq_one (a : Multiplicative Brauer.ZHat) (ha : IsOfFinOrder a) :
    a = 1 := by
  obtain ⟨n, hn, han⟩ := isOfFinOrder_iff_pow_eq_one.mp ha
  have h : n • a.toAdd = 0 := by
    have h1 := congrArg Multiplicative.toAdd han
    simpa using h1
  exact Multiplicative.toAdd.injective
    (by simpa using zhat_nsmul_eq_zero hn.ne' h)

/-- **Torsion splits off a torsion-free factor.** -/
noncomputable def torsionProdOfRightTorsionFree {A B : Type*} [CommGroup A] [CommGroup B]
    (hB : ∀ b : B, IsOfFinOrder b → b = 1) :
    CommGroup.torsion (A × B) ≃* CommGroup.torsion A where
  toFun x := ⟨(x : A × B).1, (MonoidHom.fst A B).isOfFinOrder x.2⟩
  invFun y := ⟨((y : A), 1), IsOfFinOrder.prod_iff.mpr ⟨y.2, IsOfFinOrder.one⟩⟩
  left_inv x := by
    apply Subtype.ext
    exact Prod.ext rfl ((hB (x : A × B).2 ((MonoidHom.snd A B).isOfFinOrder x.2)).symm)
  right_inv y := by
    apply Subtype.ext
    rfl
  map_mul' x y := by
    apply Subtype.ext
    rfl

/-- **Every root of unity has absolute value one.** -/
theorem nrm_coe_eq_one_of_isOfFinOrder {u : (localField p U)ˣ} (hu : IsOfFinOrder u) :
    PadicField.nrm p (localField p U) (u : localField p U) = 1 := by
  obtain ⟨n, hn, hun⟩ := isOfFinOrder_iff_pow_eq_one.mp hu
  have hval : ((u : localField p U) ^ n) = 1 := by
    rw [← Units.val_pow_eq_pow_val, hun]
    rfl
  have hne : (u : localField p U) ≠ 0 := u.ne_zero
  have hv : PadicField.v p ((u : localField p U) ^ n) = 0 := by
    rw [hval, PadicField.v_one]
  rw [PadicField.v_pow hne] at hv
  rcases mul_eq_zero.mp hv with h | h
  · exact absurd (by exact_mod_cast h) hn.ne'
  · rw [PadicField.nrm_eq_one_iff_v_eq_zero hne, h]

/-- **`torsion O^x = mu(L)`**: the roots of unity of a local field are exactly
the torsion units. -/
noncomputable def torsionUnitGroupEquivMu (U : Index p) :
    CommGroup.torsion (PadicField.unitGroup p (localField p U)) ≃* mu p U where
  toFun u :=
    ⟨((u : PadicField.unitGroup p (localField p U)) : (localField p U)ˣ),
      (Subgroup.subtype (PadicField.unitGroup p (localField p U))).isOfFinOrder u.2⟩
  invFun z :=
    ⟨⟨(z : (localField p U)ˣ),
        PadicField.mem_unitGroup.mpr (nrm_coe_eq_one_of_isOfFinOrder U z.2)⟩,
      (Subgroup.subtype_injective (PadicField.unitGroup p (localField p U))).isOfFinOrder_iff.mp z.2⟩
  left_inv u := by
    apply Subtype.ext
    apply Subtype.ext
    rfl
  right_inv z := by
    apply Subtype.ext
    rfl
  map_mul' u v := by
    apply Subtype.ext
    rfl

/-! ## 4. M2a-torsion: `mu(L) ~= torsion Gal(L^ab/L)` -/

/-- The chosen uniformiser of `L`, as a unit. -/
noncomputable def uniformizerUnit (U : Index p) : (localField p U)ˣ :=
  Units.mk0 (PadicField.uniformizer p (localField p U))
    (PadicField.uniformizer_spec (p := p) (K := localField p U)).ne_zero

/-- The chosen uniformiser has valuation one. -/
theorem uniformizerUnit_val (U : Index p) :
    PadicField.v p ((uniformizerUnit U : (localField p U)ˣ) : localField p U) = 1 :=
  PadicField.uniformizer_spec (p := p) (K := localField p U)

/-- **LANA's decomposition `Gal(K^ab/K) ~= O^x x Zhat`, transported to
S2027's carrier.** -/
noncomputable def galoisGroupMaximalAbelianEquivProd (U : Index p) :
    Gal(↥(maximalAbelianExtension p U) / localField p U) ≃*
      (PadicField.unitGroup p (localField p U) × Multiplicative Brauer.ZHat) :=
  (galoisGroupEquiv U).symm.trans
    (PadicField.galAbEquiv (p := p) (K := localField p U) (Ω := AlgebraicClosure ℚ_[p])
      (π := uniformizerUnit U) (uniformizerUnit_val U)).toMulEquiv

/-- **M2a-torsion.**  The Artin map identifies the roots of unity of `L` with
the torsion of `Gal(L^ab / L)`. -/
noncomputable def localArtinTorsionEquiv (U : Index p) :
    mu p U ≃*
      CommGroup.torsion (Gal(↥(maximalAbelianExtension p U) / localField p U)) :=
  ((torsionUnitGroupEquivMu U).symm.trans
      (torsionProdOfRightTorsionFree
        (A := PadicField.unitGroup p (localField p U))
        (B := Multiplicative Brauer.ZHat)
        (fun b hb => zhat_isOfFinOrder_eq_one b hb)).symm).trans
    (torsionMulEquiv (galoisGroupMaximalAbelianEquivProd U)).symm

/-- **M2a-torsion holds.** -/
theorem localArtinTorsion_holds (U : Index p) : localArtinTorsion p U :=
  ⟨localArtinTorsionEquiv U⟩

/-! ## 5. `LocalArtinSourceData`: the `artin` field unconditionally, (M2c) as gap -/

/-- The `artin` field of `LocalArtinSourceData`, unconditionally: this is
(M2a) in S2027's topological-abelianization shape, via
`galoisGroupMaximalAbelian`. -/
noncomputable def localArtinSourceArtin (U : Index p) :
    mu p U ≃*
      CommGroup.torsion (TopologicalAbelianization (localGaloisGroup p U)) :=
  (localArtinTorsionEquiv U).trans
    (torsionMulEquiv (galoisGroupMaximalAbelian p U)).symm

/-- **The first missing piece: (M2c).**  The comparison of the torsion of the
abstract abelianization with the torsion of the profinite abelianization, for
every open subgroup `U`.  This is exactly the `carrier` field of
`LocalArtinSourceData` and is not derivable in the tree. -/
def localArtinSourceCarrierMissing : Prop :=
  ∀ U : Index p, profiniteTorsionComparison p U

/-- **`LocalArtinSourceData` from (M2c).**  The `artin` field is constructed;
the `carrier` field is exactly the hypothesis. -/
noncomputable def localArtinSourceDataOfComparison
    (hc : localArtinSourceCarrierMissing (p := p)) : LocalArtinSourceData p where
  artin := fun U => localArtinSourceArtin U
  carrier := fun U => (hc U).some

/-- The source datum produced from (M2c) has the constructed `artin` field. -/
theorem localArtinSourceDataOfComparison_artin (hc : localArtinSourceCarrierMissing (p := p))
    (U : Index p) :
    (localArtinSourceDataOfComparison hc).artin U = localArtinSourceArtin U :=
  rfl

/-! ## 6. S2024's `LocalReciprocityData` from (M2c) + (M2b) -/

/-- **(M2b): the transfer compatibility.**  This is literally S2024's
`transfer_compat` field for the datum built from (M2c); it is the norm
compatibility of the reciprocity map, absent from the tree. -/
def localReciprocityTransferCompatibility
    (hc : localArtinSourceCarrierMissing (p := p)) : Prop :=
  ∀ {H K : Index p} (h : H ≤ K) (v : CommGroup.torsion (Abelianization K)),
    levelwiseEquiv p (localArtinSourceDataOfComparison hc) H
        (torsionMap (verlagerungOpen p h) v) =
      fixedFieldTorsionUnitsInclusion p h
        (levelwiseEquiv p (localArtinSourceDataOfComparison hc) K v)

/-- **(M2c) + (M2b) give S2024's `LocalReciprocityData`.** -/
noncomputable def localReciprocityData_of_source
    (hc : localArtinSourceCarrierMissing (p := p))
    (htransfer : localReciprocityTransferCompatibility hc) :
    LocalReciprocityData p :=
  S2027LocalArtinActual.localReciprocityData_of_source p
    (localArtinSourceDataOfComparison hc) htransfer

/-- **S2011's levelwise reciprocity on torsion**, from (M2c). -/
theorem localReciprocityOnTorsion_of_source (hc : localArtinSourceCarrierMissing (p := p)) :
    localReciprocityOnTorsion p :=
  S2027LocalArtinActual.localReciprocityOnTorsion_of_source p
    (localArtinSourceDataOfComparison hc)

/-- **(M2c) + (M2b) give S2017's `muQZComparison`.** -/
theorem muQZComparison_of_source
    (hc : localArtinSourceCarrierMissing (p := p))
    (htransfer : localReciprocityTransferCompatibility hc) :
    muQZComparison p :=
  muQZComparison_of_data p (localReciprocityData_of_source hc htransfer)

/-- **(M2c) + (M2b) give S2017's `muHatComparison`.** -/
theorem muHatComparison_of_source
    (hc : localArtinSourceCarrierMissing (p := p))
    (htransfer : localReciprocityTransferCompatibility hc) :
    muHatComparison p :=
  muHatComparison_of_data p (localReciprocityData_of_source hc htransfer)

/-! ## 7. Axiom probes -/

#print axioms zhat_nsmul_eq_zero
#print axioms zhat_isOfFinOrder_eq_one
#print axioms torsionProdOfRightTorsionFree
#print axioms nrm_coe_eq_one_of_isOfFinOrder
#print axioms torsionUnitGroupEquivMu
#print axioms artinMaximalAbelian
#print axioms artinMaximalAbelian_apply
#print axioms artinMaximalAbelian_eq_one_iff
#print axioms unitProfiniteCompletionEquivGal
#print axioms unitProfiniteCompletionEquivGal_eta
#print axioms localReciprocityIsomorphism_holds
#print axioms uniformizerUnit
#print axioms galoisGroupMaximalAbelianEquivProd
#print axioms localArtinTorsionEquiv
#print axioms localArtinTorsion_holds
#print axioms localArtinSourceArtin
#print axioms localArtinSourceDataOfComparison
#print axioms localReciprocityData_of_source
#print axioms localReciprocityOnTorsion_of_source

end LeanFormal.IUT.XiFPaper.S2098M2aCoreActual