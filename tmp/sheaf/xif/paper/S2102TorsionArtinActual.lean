/-
Copyright (c) 2026 LANA Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LANA Project
-/
import tmp.sheaf.xif.paper.S2046M2S2089Port
import Reciprocity.GaloisStructure

/-!
# S2102: an actual inhabitant of the M2a torsion equivalence

Layer: **O** (original Theta-link / q-pilot).  Consumer: S2046's
`S2046M2TorsionRequired` and S2027's `localArtinTorsion`, hence the
`artin` field of `LocalArtinSourceData` and the S2024/S2017 reductions.

For one finite `L / Q_p` with `L = localField p U`, this file constructs

  `mu p U  ~=*  torsion (TopologicalAbelianization (localGaloisGroup p U))`

unconditionally.  The construction is genuinely via the local Artin map:

* `PadicField.artinCompletionEquiv` (LANA's local CFT port, built from the
  finite-level reciprocity maps `PadicField.abRec`, the norm theorem
  `PadicField.ker_abRec` and the local existence theorem) gives
  `L^x-hat ~= Gal(L^ab/L)`;
* S2089's `galoisGroupEquiv` transports `Gal(PadicField.maxAbelian / L)` to
  S2027's `Gal(maximalAbelianExtension p U / L)`;
* `PadicField.galAbEquiv` decomposes `Gal(K^ab/K) ~= O_K^x x Zhat`, so the
  torsion computation reduces to three elementary facts proved here:
  `Zhat` is torsion free, every root of unity has absolute value one (so
  `torsion O^x = torsion K^x = mu(L)`), and a torsion-free factor can be
  split off a product;
* composing with S2027's `galoisGroupMaximalAbelian` lands on the profinite
  abelianization carrier.

No `sorry`, `admit` or new `axiom` is introduced.  The printed axioms are
`propext`, `Classical.choice` and `Quot.sound` only.
-/

set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 800000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

noncomputable section

open IntermediateField
open LeanFormal.IUT.XiFPaper.S2017VerlagerungActual
open LeanFormal.IUT.XiFPaper.S2027LocalArtinActual
open LeanFormal.IUT.XiFPaper.S2089FiniteAbelianSubextensionActual

namespace LeanFormal.IUT.XiFPaper.S2102TorsionArtinActual

variable {p : Nat} [Fact (Nat.Prime p)]
variable (U : Index p)

/-- `localField p U` is a finite extension of `Q_p`. -/
instance localFieldFiniteDimensional (U : Index p) :
    FiniteDimensional ℚ_[p] (localField p U) :=
  LeanFormal.IUT.LocalIntegralUnitKummerInjectivity.fixedField_finiteDimensional p U

/-! ## 1. `Zhat` is torsion free -/

/-- **`Zhat` is torsion free additively.**  If `n • a = 0` for `a : Zhat` and
`n ≠ 0` then `a = 0`.  Proved from the defining projective system
`Zhat -> ZMod (m * n) -> ZMod m`: `n • a = 0` at level `m * n` forces the class
of `a` at level `m` to vanish. -/
theorem zhat_nsmul_eq_zero {a : Brauer.ZHat} {n : Nat} (hn : n ≠ 0) (h : n • a = 0) :
    a = 0 := by
  apply Brauer.ZHat.ext
  intro m
  set M : PNat := ⟨m.val * n, Nat.mul_pos m.pos (Nat.pos_of_ne_zero hn)⟩ with hM
  have hMn : (M : Nat) = m.val * n := rfl
  have hx0 : (n : Nat) • ((a : forall k : PNat, ZMod k) M) = 0 := by
    have h1 := congrArg (fun z : Brauer.ZHat => (z : forall k : PNat, ZMod k) M) h
    simpa using h1
  haveI : NeZero (M : Nat) := ⟨Nat.pos_iff_ne_zero.mp M.pos⟩
  have hcast : ((n * ((a : forall k : PNat, ZMod k) M).val : Nat) : ZMod (M : Nat)) = 0 := by
    have h2 : (n : ZMod (M : Nat)) * ((a : forall k : PNat, ZMod k) M) = 0 := by
      rw [← nsmul_eq_mul]
      exact hx0
    calc ((n * ((a : forall k : PNat, ZMod k) M).val : Nat) : ZMod (M : Nat))
        = (n : ZMod (M : Nat)) * (((a : forall k : PNat, ZMod k) M).val : ZMod (M : Nat)) := by
          rw [Nat.cast_mul]
      _ = (n : ZMod (M : Nat)) * ((a : forall k : PNat, ZMod k) M) := by rw [ZMod.natCast_zmod_val]
      _ = 0 := h2
  have hdvd : (M : Nat) ∣ n * ((a : forall k : PNat, ZMod k) M).val :=
    (ZMod.natCast_eq_zero_iff _ _).mp hcast
  have hdvd' : m.val * n ∣ n * ((a : forall k : PNat, ZMod k) M).val := by
    rw [← hMn]
    exact hdvd
  have hdvd'' : n * m.val ∣ n * ((a : forall k : PNat, ZMod k) M).val := by
    rw [Nat.mul_comm n m.val]
    exact hdvd'
  have hdvdm : m.val ∣ ((a : forall k : PNat, ZMod k) M).val :=
    Nat.dvd_of_mul_dvd_mul_left (Nat.pos_of_ne_zero hn) hdvd''
  have hmem : (m : Nat) ∣ (M : Nat) := ⟨n, hMn⟩
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
  have h0 : a.toAdd = (1 : Multiplicative Brauer.ZHat).toAdd := by
    rw [zhat_nsmul_eq_zero (Nat.pos_iff_ne_zero.mp hn) h]
    rfl
  exact Multiplicative.toAdd.injective h0

/-- **Torsion splits off a torsion-free factor.** -/
noncomputable def torsionProdOfRightTorsionFree {A B : Type*} [CommGroup A] [CommGroup B]
    (hB : forall b : B, IsOfFinOrder b → b = 1) :
    CommGroup.torsion (A × B) ≃* CommGroup.torsion A where
  toFun x := ⟨(x : A × B).1, MonoidHom.isOfFinOrder (MonoidHom.fst A B) x.2⟩
  invFun y := ⟨((y : A), 1), IsOfFinOrder.prod_iff.mpr ⟨y.2, IsOfFinOrder.one⟩⟩
  left_inv x := by
    apply Subtype.ext
    exact Prod.ext rfl
      ((hB (x : A × B).2 (MonoidHom.isOfFinOrder (MonoidHom.snd A B) x.2)).symm)
  right_inv y := by
    apply Subtype.ext
    rfl
  map_mul' x y := by
    apply Subtype.ext
    rfl

/-! ## 2. `torsion O^x = mu(L)` -/

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
  · exact absurd (by exact_mod_cast h) (Nat.pos_iff_ne_zero.mp hn)
  · rw [PadicField.nrm_eq_one_iff_v_eq_zero hne, h]

/-- **`torsion O^x = mu(L)`**: the roots of unity of a local field are exactly
the torsion units. -/
noncomputable def torsionUnitGroupEquivMu (U : Index p) :
    CommGroup.torsion (PadicField.unitGroup p (localField p U)) ≃* mu p U where
  toFun u :=
    ⟨((u : PadicField.unitGroup p (localField p U)) : (localField p U)ˣ),
      MonoidHom.isOfFinOrder
        (Subgroup.subtype (PadicField.unitGroup p (localField p U))) u.2⟩
  invFun z :=
    ⟨⟨(z : (localField p U)ˣ),
        PadicField.mem_unitGroup.mpr (nrm_coe_eq_one_of_isOfFinOrder U z.2)⟩,
      (Function.Injective.isOfFinOrder_iff
        (f := Subgroup.subtype (PadicField.unitGroup p (localField p U)))
        (Subgroup.subtype_injective _)).mp z.2⟩
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

/-! ## 3. The decomposition `Gal(L^ab/L) = O^x x Zhat` -/

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

/-! ## 4. The torsion equivalence -/

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

/-- **S2027's `localArtinTorsion` holds.** -/
theorem localArtinTorsion_holds (U : Index p) : localArtinTorsion p U :=
  ⟨localArtinTorsionEquiv U⟩

/-- **The actual inhabitant of `S2046M2TorsionRequired`**: the torsion of the
profinite abelianization of `localGaloisGroup p U` is `mu p U`. -/
noncomputable def S2046M2TorsionRequired_actual (U : Index p) :
    LeanFormal.IUT.XiFPaper.S2046M2S2089Port.S2046M2TorsionRequired (p := p) U :=
  (localArtinTorsionEquiv U).trans
    (torsionMulEquiv (galoisGroupMaximalAbelian p U)).symm

/-- **The inhabitant in `Nonempty` form.** -/
theorem S2046M2TorsionRequired_holds (U : Index p) :
    Nonempty (LeanFormal.IUT.XiFPaper.S2046M2S2089Port.S2046M2TorsionRequired (p := p) U) :=
  ⟨S2046M2TorsionRequired_actual U⟩

/-- **S2027's `localArtinTorsionTopological` holds.** -/
theorem localArtinTorsionTopological_holds (U : Index p) :
    localArtinTorsionTopological p U :=
  ⟨S2046M2TorsionRequired_actual U⟩

/-! ## 5. The target statement, at its exact type -/

/-- The constructed inhabitant has exactly the target type, definitionally. -/
example (U : Index p) :
    mu p U ≃* CommGroup.torsion (TopologicalAbelianization (localGaloisGroup p U)) :=
  S2046M2TorsionRequired_actual U

/-! ## 6. Axiom probes -/

#print axioms zhat_nsmul_eq_zero
#print axioms zhat_isOfFinOrder_eq_one
#print axioms torsionProdOfRightTorsionFree
#print axioms nrm_coe_eq_one_of_isOfFinOrder
#print axioms torsionUnitGroupEquivMu
#print axioms uniformizerUnit
#print axioms galoisGroupMaximalAbelianEquivProd
#print axioms localArtinTorsionEquiv
#print axioms localArtinTorsion_holds
#print axioms S2046M2TorsionRequired_actual
#print axioms S2046M2TorsionRequired_holds
#print axioms localArtinTorsionTopological_holds

end LeanFormal.IUT.XiFPaper.S2102TorsionArtinActual
