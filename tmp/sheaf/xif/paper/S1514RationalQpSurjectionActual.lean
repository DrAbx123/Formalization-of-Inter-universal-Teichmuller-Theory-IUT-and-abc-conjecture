import tmp.sheaf.xif.paper.S1474ReportBTensorRealizationActual
import Mathlib.LinearAlgebra.TensorProduct.Basic

/-!
# S1514: the actual canonical Qp-linear map from the rational source tensor to the source block

S1505 proves that there is no `Qp`-linear equivalence between the rational
tensor `RatT = SourceLogShellActualIQTensor (sourceDatum ...)` base-changed
to `Qp` and the finite `Qp` tensor `SourceBlk`; the obstruction is the
infinite `Q`-dimension of `RatT` (equivalently, the infinite `Qp`-dimension
of `RatT ⊗[Q] Qp`) against the finite `Qp`-dimension of `SourceBlk`.

This file constructs the correct positive comparison, with no equivalence
claim:

* a general canonical `Qp`-linear map
  `(⨂[Q] i, M i) ⊗[Q] Qp →ₗ[Qp] ⨂[Qp] i, M i`, induced by the universal
  property of the tensor product;
* its pure-tensor formula `t ⊗ q ↦ q • t`;
* surjectivity, using that pure tensors span the `Qp` tensor;
* the induced quotient equivalence by the kernel, i.e. the exact sequence
  `0 → ker → (⨂[Q] i, M i) ⊗[Q] Qp → ⨂[Qp] i, M i → 0`;
* an exact description of the kernel as the preimage, under the canonical
  `Q`-linear map `(⨂[Q] i, M i) ⊗[Q] Qp → (⨂[Qp] i, M i) ⊗[Q] Qp`, of
  the kernel of the `Q`-action map `(⨂[Qp] i, M i) ⊗[Q] Qp → ⨂[Qp] i, M i`.

The actual source instance is

* `RatT = SourceLogShellActualIQTensor (sourceDatum I j t)`;
* `SourceBlk I j t = ⨂[Qp] i, CommonPrimeCompletion (t i)`;
* the canonical map `sourceCanonicalQpMap` is the composite of the rational
  identification `sourceIQTensorEquiv` with the general canonical map.

No `Qp`-linear equivalence is constructed or asserted.  The explicit kernel
is left as the exact kernel above; a finite presentation of the action
kernel, or an integral lattice-level comparison, is the remaining
paper-level comparison.  This is the first missing item, not a hidden
equivalence.
-/

noncomputable section
open scoped TensorProduct
set_option maxSynthPendingDepth 10
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT.XiFPaper.S1514RationalQpSurjectionActual

/-! ## 1. The base-change module structure and the canonical map -/

variable {p : Nat} [Fact p.Prime]

/-- The right `Qp`-scalar action on a base change `V ⊗[Q] Qp`, acting on
the second factor.  This is separated from the module instance so that the
instance fields can be proved without invoking the instance under
construction. -/
noncomputable def baseChangeRightSmulFun (V : Type*) [AddCommGroup V] [Module ℚ V]
    (a : ℚ_[p]) (x : V ⊗[ℚ] ℚ_[p]) : V ⊗[ℚ] ℚ_[p] :=
  TensorProduct.map LinearMap.id (LinearMap.mulLeft ℚ a) x

/-- `V ⊗[Q] Qp` is a `Qp`-module by acting on the second factor.  Mathlib
has the left action on the first factor; this right action is the one
needed for the paper's `RatT ⊗[Q] Qp`. -/
noncomputable instance baseChangeRightModule (V : Type*) [AddCommGroup V] [Module ℚ V] :
    Module ℚ_[p] (V ⊗[ℚ] ℚ_[p]) where
  smul := baseChangeRightSmulFun (p := p) V
  one_smul x := by
    change baseChangeRightSmulFun (p := p) V (1 : ℚ_[p]) x = x
    simp [baseChangeRightSmulFun]
  mul_smul a b x := by
    change TensorProduct.map LinearMap.id (LinearMap.mulLeft ℚ (a * b)) x =
      (TensorProduct.map LinearMap.id (LinearMap.mulLeft ℚ a)).comp
        (TensorProduct.map LinearMap.id (LinearMap.mulLeft ℚ b)) x
    rw [← TensorProduct.map_comp]
    congr 1
    ext y
    simp [LinearMap.mulLeft, mul_assoc]
  smul_zero a := by
    change baseChangeRightSmulFun (p := p) V a 0 = 0
    simp [baseChangeRightSmulFun]
  smul_add a x y := by
    change baseChangeRightSmulFun (p := p) V a (x + y) =
      baseChangeRightSmulFun (p := p) V a x + baseChangeRightSmulFun (p := p) V a y
    simp [baseChangeRightSmulFun, map_add]
  add_smul a b x := by
    change TensorProduct.map LinearMap.id (LinearMap.mulLeft ℚ (a + b)) x =
      (TensorProduct.map LinearMap.id (LinearMap.mulLeft ℚ a) +
        TensorProduct.map LinearMap.id (LinearMap.mulLeft ℚ b) :
          V ⊗[ℚ] ℚ_[p] →ₗ[ℚ] V ⊗[ℚ] ℚ_[p]) x
    rw [← TensorProduct.map_add_right]
    congr 1
    ext y
    simp [LinearMap.mulLeft, add_mul]
  zero_smul x := by
    change baseChangeRightSmulFun (p := p) V 0 x = 0
    simp [baseChangeRightSmulFun]

/-! ## 2. Base change of a `Q`-linear map -/

section BaseChangeMap
variable {V W : Type*} [AddCommGroup V] [Module ℚ V] [AddCommGroup W] [Module ℚ W]

/-- The tensor map `e ⊗ id` commutes with the right `Qp`-action. -/
theorem tensorProductMap_id_mulLeft_apply (e : V →ₗ[ℚ] W) (a : ℚ_[p])
    (x : V ⊗[ℚ] ℚ_[p]) :
    TensorProduct.map e LinearMap.id
        (TensorProduct.map LinearMap.id (LinearMap.mulLeft ℚ a) x) =
      TensorProduct.map LinearMap.id (LinearMap.mulLeft ℚ a)
        (TensorProduct.map e LinearMap.id x) := by
  change ((TensorProduct.map e LinearMap.id).comp
    (TensorProduct.map LinearMap.id (LinearMap.mulLeft ℚ a))) x =
    ((TensorProduct.map LinearMap.id (LinearMap.mulLeft ℚ a)).comp
      (TensorProduct.map e LinearMap.id)) x
  rw [← TensorProduct.map_comp, ← TensorProduct.map_comp]
  simp

/-- `TensorProduct.map e id` is `Qp`-linear for the right base-change
module structure. -/
theorem tensorProductMap_id_smul (e : V →ₗ[ℚ] W) (a : ℚ_[p])
    (x : V ⊗[ℚ] ℚ_[p]) :
    TensorProduct.map e LinearMap.id (baseChangeRightSmulFun (p := p) V a x) =
      baseChangeRightSmulFun (p := p) W a
        (TensorProduct.map e LinearMap.id x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp [baseChangeRightSmulFun]
  | tmul v q =>
      simp [baseChangeRightSmulFun, TensorProduct.map_tmul]
  | add x y hx hy =>
      simp [baseChangeRightSmulFun, map_add, hx, hy]
      exact congrArg₂ (· + ·) (tensorProductMap_id_mulLeft_apply e a x)
        (tensorProductMap_id_mulLeft_apply e a y)

/-- Scalar extension of a `Q`-linear map `V → W` to the base changes. -/
noncomputable def baseChangeMap (e : V →ₗ[ℚ] W) :
    (V ⊗[ℚ] ℚ_[p]) →ₗ[ℚ_[p]] (W ⊗[ℚ] ℚ_[p]) where
  toFun := TensorProduct.map e LinearMap.id
  map_add' x y := by simp
  map_smul' a x := tensorProductMap_id_smul (p := p) e a x

@[simp] theorem baseChangeMap_tmul (e : V →ₗ[ℚ] W) (v : V) (q : ℚ_[p]) :
    baseChangeMap (p := p) e (v ⊗ₜ[ℚ] q) = e v ⊗ₜ[ℚ] q := by
  simp [baseChangeMap]

/-- Base change of a `Q`-linear equivalence is surjective. -/
theorem baseChangeMap_surjective (e : V ≃ₗ[ℚ] W) :
    Function.Surjective (baseChangeMap (p := p) e.toLinearMap) := by
  intro z
  refine ⟨baseChangeMap (p := p) e.symm.toLinearMap z, ?_⟩
  change (TensorProduct.map e.toLinearMap LinearMap.id).comp
    (TensorProduct.map e.symm.toLinearMap LinearMap.id) z = z
  rw [← TensorProduct.map_comp]
  simp

end BaseChangeMap

/-! ## 3. The canonical map on the rational tensor -/

variable {ι : Type*} [Finite ι]
variable (M : ι → Type*) [∀ i, AddCommGroup (M i)] [∀ i, Module ℚ_[p] (M i)]
variable [∀ i, Module ℚ (M i)] [∀ i, IsScalarTower ℚ ℚ_[p] (M i)]

/-- The `Q`-linear pure-tensor evaluation from the rational tensor to the
`Qp` tensor.  This is the canonical `Q`-linear map underlying the comparison. -/
noncomputable def qTensorToQpTensor :
    (⨂[ℚ] i, M i) →ₗ[ℚ] (⨂[ℚ_[p]] i, M i) :=
  PiTensorProduct.lift ((PiTensorProduct.tprod ℚ_[p]).restrictScalars ℚ)

@[simp] theorem qTensorToQpTensor_tprod (x : (i : ι) → M i) :
    qTensorToQpTensor (p := p) M (⨂ₜ[ℚ] i, x i) = ⨂ₜ[ℚ_[p]] i, x i := by
  rw [qTensorToQpTensor, PiTensorProduct.lift.tprod]
  rfl

/-- The `Q`-bilinear map `(t, q) ↦ q • eval(t)`. -/
noncomputable def baseChangeBilin :
    (⨂[ℚ] i, M i) →ₗ[ℚ] ℚ_[p] →ₗ[ℚ] (⨂[ℚ_[p]] i, M i) where
  toFun t := (LinearMap.id : ℚ_[p] →ₗ[ℚ] ℚ_[p]).smulRight
    (qTensorToQpTensor (p := p) M t)
  map_add' t₁ t₂ := by
    ext q
    simp [map_add]
  map_smul' c t := by
    ext q
    change q • qTensorToQpTensor (p := p) M (c • t) =
      c • (q • qTensorToQpTensor (p := p) M t)
    rw [LinearMap.map_smul]
    exact smul_comm q c (qTensorToQpTensor (p := p) M t)

/-- The canonical `Qp`-linear map from the base change of the rational tensor
to the `Qp` tensor.  This file proves only its surjectivity and describes its
kernel; no equivalence is asserted. -/
noncomputable def canonicalMap :
    ((⨂[ℚ] i, M i) ⊗[ℚ] ℚ_[p]) →ₗ[ℚ_[p]] (⨂[ℚ_[p]] i, M i) where
  toFun x := TensorProduct.lift (baseChangeBilin (p := p) M) x
  map_add' x y := (TensorProduct.lift (baseChangeBilin (p := p) M)).map_add x y
  map_smul' a x := by
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul t q =>
        change TensorProduct.lift (baseChangeBilin (p := p) M)
          (baseChangeRightSmulFun (p := p) (⨂[ℚ] i, M i) a (t ⊗ₜ[ℚ] q)) =
          a • (TensorProduct.lift (baseChangeBilin (p := p) M) (t ⊗ₜ[ℚ] q))
        simp only [baseChangeRightSmulFun, TensorProduct.map_tmul, LinearMap.id_coe, id_eq,
          LinearMap.mulLeft_apply]
        rw [TensorProduct.lift.tmul, TensorProduct.lift.tmul]
        simp only [baseChangeBilin, LinearMap.coe_mk, AddHom.coe_mk,
          LinearMap.coe_smulRight, LinearMap.smul_apply, LinearMap.id_coe, id_eq]
        rw [smul_smul]
    | add x y hx hy =>
        simp only [map_add, hx, hy, smul_add]

@[simp] theorem canonicalMap_tmul (t : ⨂[ℚ] i, M i) (q : ℚ_[p]) :
    canonicalMap (p := p) M (t ⊗ₜ[ℚ] q) = q • qTensorToQpTensor (p := p) M t := by
  change TensorProduct.lift (baseChangeBilin (p := p) M) (t ⊗ₜ[ℚ] q) = _
  rw [TensorProduct.lift.tmul]
  rfl

@[simp] theorem canonicalMap_tprod (x : (i : ι) → M i) (q : ℚ_[p]) :
    canonicalMap (p := p) M ((⨂ₜ[ℚ] i, x i) ⊗ₜ[ℚ] q) =
      q • (⨂ₜ[ℚ_[p]] i, x i) := by
  rw [canonicalMap_tmul, qTensorToQpTensor_tprod]

/-- The canonical map is surjective: every pure tensor of the `Qp` tensor is
the image of the corresponding rational pure tensor with scalar `1`. -/
theorem canonicalMap_surjective : Function.Surjective (canonicalMap (p := p) M) := by
  have h : Submodule.span ℚ_[p] (Set.range (PiTensorProduct.tprod ℚ_[p])) ≤
      LinearMap.range (canonicalMap (p := p) M) := by
    rw [Submodule.span_le]
    rintro y ⟨x, rfl⟩
    exact ⟨(⨂ₜ[ℚ] i, x i) ⊗ₜ[ℚ] (1 : ℚ_[p]), by
      rw [canonicalMap_tprod]; simp⟩
  have htop : LinearMap.range (canonicalMap (p := p) M) = ⊤ := by
    rw [eq_top_iff, ← PiTensorProduct.span_tprod_eq_top (R := ℚ_[p]) (s := M)]
    exact h
  intro y
  exact LinearMap.mem_range.mp (by rw [htop]; exact Submodule.mem_top)

/-- The quotient by the kernel of the canonical map is exactly the `Qp`
tensor.  This is the exact sequence
`0 → ker → (⨂[Q] i, M i) ⊗[Q] Qp → ⨂[Qp] i, M i → 0`. -/
noncomputable def canonicalMapQuotientEquiv :
    (((⨂[ℚ] i, M i) ⊗[ℚ] ℚ_[p]) ⧸
      LinearMap.ker (canonicalMap (p := p) M)) ≃ₗ[ℚ_[p]]
      (⨂[ℚ_[p]] i, M i) :=
  (LinearMap.quotKerEquivRange (canonicalMap (p := p) M)).trans
    ((LinearEquiv.ofEq _ _ (LinearMap.range_eq_top.mpr (canonicalMap_surjective (p := p) M))).trans
      Submodule.topEquiv)

/-! ## 4. Description of the kernel: the `Q`-action kernel -/

/-- The `Q`-bilinear `Q`-action map `(y, q) ↦ q • y`. -/
noncomputable def qpActionBilin :
    (⨂[ℚ_[p]] i, M i) →ₗ[ℚ] ℚ_[p] →ₗ[ℚ] (⨂[ℚ_[p]] i, M i) where
  toFun y := (LinearMap.id : ℚ_[p] →ₗ[ℚ] ℚ_[p]).smulRight y
  map_add' y₁ y₂ := by
    ext q
    simp
  map_smul' c y := by
    ext q
    change q • (c • y) = c • (q • y)
    exact smul_comm q c y

/-- The `Q`-linear action map from the `Q`-tensor of the target to the
target.  Its kernel is the module of `Q`-relations among the `Qp` pure
tensors. -/
noncomputable def qpAction :
    ((⨂[ℚ_[p]] i, M i) ⊗[ℚ] ℚ_[p]) →ₗ[ℚ] (⨂[ℚ_[p]] i, M i) :=
  TensorProduct.lift (qpActionBilin (p := p) M)

@[simp] theorem qpAction_tmul (y : ⨂[ℚ_[p]] i, M i) (q : ℚ_[p]) :
    qpAction (p := p) M (y ⊗ₜ[ℚ] q) = q • y := by
  change TensorProduct.lift (qpActionBilin (p := p) M) (y ⊗ₜ[ℚ] q) = _
  rw [TensorProduct.lift.tmul]
  rfl

/-- Pointwise factorization of the canonical map through the action map. -/
theorem canonicalMap_apply_eq (x : (⨂[ℚ] i, M i) ⊗[ℚ] ℚ_[p]) :
    canonicalMap (p := p) M x =
      qpAction (p := p) M
        (TensorProduct.map (qTensorToQpTensor (p := p) M) LinearMap.id x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul t q =>
      simp [qpAction_tmul, canonicalMap_tmul]
  | add x y hx hy =>
      simp [map_add, hx, hy]

/-- Exact kernel description: `x` is killed by the canonical map iff its
image in the `Qp` tensor of `Q`-tensors lies in the kernel of the `Q`-action
map.  This is the exact `Q`-relation kernel; no finite presentation of the
action kernel is asserted here. -/
theorem canonicalMap_ker_iff (x : (⨂[ℚ] i, M i) ⊗[ℚ] ℚ_[p]) :
    canonicalMap (p := p) M x = 0 ↔
      TensorProduct.map (qTensorToQpTensor (p := p) M) LinearMap.id x ∈
        LinearMap.ker (qpAction (p := p) M) := by
  rw [canonicalMap_apply_eq]
  rfl

/-- Rational relations in the tensor are killed after base change. -/
theorem qTensorToQpTensor_ker_tmul_mem_ker (t : ⨂[ℚ] i, M i)
    (ht : qTensorToQpTensor (p := p) M t = 0) (q : ℚ_[p]) :
    canonicalMap (p := p) M (t ⊗ₜ[ℚ] q) = 0 := by
  rw [canonicalMap_tmul, ht, smul_zero]


/-! ## 5. The actual source tensor and the source block -/

open LeanFormal.IUT
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.SourceProcessionCapsule
open LeanFormal.IUT.XiFPaper.S1474ReportBTensorRealizationActual
open LeanFormal.IUT.XiFPaper.S1264SourceCapsuleInd1Actual

universe uv upi umon ui
variable {l : PrimeGeFive} {V : Type uv}
variable (I : OriginalInput l V)
variable (n : Int) (vQ : RationalPlaceAt l)

local instance factPrimeOfPrimeGeFiveS1514 (l : PrimeGeFive) : Fact (Nat.Prime l.value) :=
  l.factPrime

/-- The actual rational base change `RatT ⊗[Q] Qp` at a fixed capsule level
and fixed tuple of actual finite places. -/
abbrev SourceRationalBaseChange (j : Nat) (t : SourceTup (I := I) j) : Type _ :=
  SourceLogShellActualIQTensor (sourceDatum (I := I) (j := j) (t := t)) ⊗[ℚ] ℚ_[l.value]

/-- The actual canonical `Qp`-linear map from `RatT ⊗[Q] Qp` to
`SourceBlk`.  It is the composite of the proved rational identification
`sourceIQTensorEquiv` with the general canonical base-change map.  It is
surjective below; this file does not assert that it is an equivalence. -/
noncomputable def sourceCanonicalQpMap (j : Nat) (t : SourceTup (I := I) j) :
    SourceRationalBaseChange (I := I) (l := l) j t →ₗ[ℚ_[l.value]]
      SourceBlk (I := I) (l := l) (j := j) (t := t) :=
  (canonicalMap (p := l.value) (fun i => CommonPrimeCompletion (t i))).comp
    (baseChangeMap (p := l.value)
      (sourceIQTensorEquiv (I := I) (j := j) (t := t)).toLinearMap)

/-- The actual map on a pure rational tensor: scalar extension of the pure
tensor.  This is the actual form of `t ⊗ q ↦ q • t`. -/
theorem sourceCanonicalQpMap_tprod (j : Nat) (t : SourceTup (I := I) j)
    (x : (i : Capsule j) → CommonPrimeCompletion (t i)) (q : ℚ_[l.value]) :
    sourceCanonicalQpMap (I := I) (l := l) (j := j) (t := t)
      (((sourceIQTensorEquiv (I := I) (j := j) (t := t)).symm
        (⨂ₜ[ℚ] i, x i)) ⊗ₜ[ℚ] q) =
      q • (⨂ₜ[ℚ_[l.value]] i, x i) := by
  change canonicalMap (p := l.value) (fun i => CommonPrimeCompletion (t i))
    (baseChangeMap (p := l.value)
      (sourceIQTensorEquiv (I := I) (j := j) (t := t)).toLinearMap
      (((sourceIQTensorEquiv (I := I) (j := j) (t := t)).symm
        (⨂ₜ[ℚ] i, x i)) ⊗ₜ[ℚ] q)) =
    q • (⨂ₜ[ℚ_[l.value]] i, x i)
  rw [baseChangeMap_tmul]
  have harg : (sourceIQTensorEquiv (I := I) (j := j) (t := t)).toLinearMap
      ((sourceIQTensorEquiv (I := I) (j := j) (t := t)).symm
        (⨂ₜ[ℚ] i, x i)) = ⨂ₜ[ℚ] i, x i := by
    simp
  rw [harg]
  rw [canonicalMap_tprod]

/-- The actual canonical map is surjective onto the source block. -/
theorem sourceCanonicalQpMap_surjective (j : Nat) (t : SourceTup (I := I) j) :
    Function.Surjective (sourceCanonicalQpMap (I := I) (l := l) (j := j) (t := t)) :=
  (canonicalMap_surjective (p := l.value)
    (M := fun i => CommonPrimeCompletion (t i))).comp
    (baseChangeMap_surjective (p := l.value)
      (sourceIQTensorEquiv (I := I) (j := j) (t := t)))

theorem sourceCanonicalQpMap_range_eq_top (j : Nat) (t : SourceTup (I := I) j) :
    LinearMap.range (sourceCanonicalQpMap (I := I) (l := l) (j := j) (t := t)) = ⊤ :=
  LinearMap.range_eq_top.mpr
    (sourceCanonicalQpMap_surjective (I := I) (l := l) (j := j) (t := t))

/-- The exact quotient of `RatT ⊗[Q] Qp` by the kernel is the source block. -/
noncomputable def sourceCanonicalQuotientEquiv (j : Nat) (t : SourceTup (I := I) j) :
    (SourceRationalBaseChange (I := I) (l := l) j t ⧸
      LinearMap.ker (sourceCanonicalQpMap (I := I) (l := l) (j := j) (t := t))) ≃ₗ[ℚ_[l.value]]
      SourceBlk (I := I) (l := l) (j := j) (t := t) :=
  (LinearMap.quotKerEquivRange
    (sourceCanonicalQpMap (I := I) (l := l) (j := j) (t := t))).trans
    ((LinearEquiv.ofEq _ _
      (sourceCanonicalQpMap_range_eq_top (I := I) (l := l) (j := j) (t := t))).trans
      Submodule.topEquiv)

/-- The kernel of the actual canonical map, as a `Qp`-submodule. -/
noncomputable abbrev sourceCanonicalKernel (j : Nat) (t : SourceTup (I := I) j) :
    Submodule ℚ_[l.value] (SourceRationalBaseChange (I := I) (l := l) j t) :=
  LinearMap.ker (sourceCanonicalQpMap (I := I) (l := l) (j := j) (t := t))

/-- Exact kernel description at the actual source: membership in the kernel
is exactly membership of the base-changed rational tensor in the kernel of
the general canonical map. -/
theorem sourceCanonicalKernel_iff (j : Nat) (t : SourceTup (I := I) j)
    (x : SourceRationalBaseChange (I := I) (l := l) j t) :
    x ∈ sourceCanonicalKernel (I := I) (l := l) (j := j) (t := t) ↔
      baseChangeMap (p := l.value)
        (sourceIQTensorEquiv (I := I) (j := j) (t := t)).toLinearMap x ∈
        LinearMap.ker (canonicalMap (p := l.value)
          (fun i => CommonPrimeCompletion (t i))) := by
  rfl

/-- Rational relations in the rational tensor are killed by the actual
canonical map after scalar extension.  This is one explicit part of the
kernel; it is not asserted to exhaust the kernel. -/
theorem sourceCanonicalKernel_contains_rationalRelations (j : Nat)
    (t : SourceTup (I := I) j)
    (r : SourceLogShellActualIQTensor (sourceDatum (I := I) (j := j) (t := t)))
    (q : ℚ_[l.value])
    (hr : qTensorToQpTensor (p := l.value)
      (fun i => CommonPrimeCompletion (t i))
      (sourceIQTensorEquiv (I := I) (j := j) (t := t) r) = 0) :
    (r ⊗ₜ[ℚ] q) ∈ sourceCanonicalKernel (I := I) (l := l) (j := j) (t := t) := by
  change canonicalMap (p := l.value) (fun i => CommonPrimeCompletion (t i))
    (baseChangeMap (p := l.value)
      (sourceIQTensorEquiv (I := I) (j := j) (t := t)).toLinearMap
      (r ⊗ₜ[ℚ] q)) = 0
  rw [baseChangeMap_tmul]
  exact qTensorToQpTensor_ker_tmul_mem_ker (p := l.value)
    (M := fun i => CommonPrimeCompletion (t i)) _ hr q

/-! ## 6. Axiom probes -/

#print axioms canonicalMap_surjective
#print axioms canonicalMapQuotientEquiv
#print axioms canonicalMap_ker_iff
#print axioms sourceCanonicalQpMap_tprod
#print axioms sourceCanonicalQpMap_surjective
#print axioms sourceCanonicalQuotientEquiv
#print axioms sourceCanonicalKernel_iff
#print axioms sourceCanonicalKernel_contains_rationalRelations

end LeanFormal.IUT.XiFPaper.S1514RationalQpSurjectionActual
