import tmp.sheaf.xif.paper.Ind2TensorActionActual

/-!
# S1265: actual source `Fmod`-unit copies acting on the capsule tensor packet

The data layer `SourceProcessionCapsuleData` defines, for a ring `R`,
`TensorPacket L vQ = ⨂[R] i : Capsule j, (v : Place vQ) → L.Shell i vQ v`.
The file `Ind2TensorActionActual` builds the per-factor scalar action of
`Rˣ`-copies.  This file replaces the arbitrary scalar group `Rˣ` by the
actual source group

```text
SourceFmodUnitCopies j = Capsule j → (I.initial.arithmetic.Fmod)ˣ,
```

the independent copies of the units of the base field of the actual
`OriginalInput` `I`.  A unit of `Fmod` is sent to a unit of `R` through an
`R`-algebra structure on `Fmod`; the resulting per-factor scalar action is
the existing actual `Ind2` action, fed with the source units rather than with
arbitrary `R`-units.

The source field `Fmod` itself is the canonical `R`: the construction
`sourceInd2FmodTensorEquiv` is unconditional and lands on the actual tensor
packet over the actual source field.

Exact first field for the Real actual tensor packet used by
`GlobalKummerIndActionsActual`: a ring hom `I.initial.arithmetic.Fmod →+* Real`
(equivalently an `Algebra Fmod Real`).  This is not a field of
`OriginalInput`; without it the Real packet is not an `Fmod`-module and the
source units have no Real scalar action.  The conditional Real bridge below is
therefore stated from that exact field, not from a free scalar action.

Both the generic and the unconditional `Fmod` constructions are parametric in
the actual tensor packet `C` (the `SourceProcessionCapsuleContract` already
consumed by `Ind1AutomorphismTensorActionActual` and
`GlobalKummerIndActionsActual`).  Constructing that contract, i.e. the actual
log-shell family, from `I` is the separate data-layer gap; it is not replaced
here by a degenerate one-point contract.

No placeholder type, no vacuous proposition, no custom assumption, and no
arbitrary choice is used.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 2000000

namespace LeanFormal.IUT.XiFPaper.S1265SourceInd2Actual

open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.Theorem311Source.SourceProcessionCapsule
open LeanFormal.IUT.XiFPaper.MultiradialProcessionActual
open LeanFormal.IUT.XiFPaper.Ind2TensorActionActual
open scoped TensorProduct

universe ua uv upi umon ui uR uVQ uPlace uShell

variable {l : PrimeGeFive} {V : Type uv}
variable {I : OriginalInput.{ua, uv, upi, umon, ui} l V}

/-! ## 1. The actual source unit-copy family -/

/-- The independent copies of the units of the actual source base field at
capsule level `j`: one copy on each capsule tensor factor. -/
abbrev SourceFmodUnitCopies (I : OriginalInput.{ua, uv, upi, umon, ui} l V)
    (j : Fin (capsuleLevels l)) : Type ua :=
  Capsule j.val → (I.initial.arithmetic.Fmod)ˣ

/-- The actual source family is exactly the `FmodUnitCopies` already named in
`MultiradialProcessionActual`. -/
theorem sourceFmodUnitCopies_eq_fmodUnitCopies
    (j : Fin (capsuleLevels l)) :
    SourceFmodUnitCopies (I := I) j = FmodUnitCopies (I := I) j := rfl

/-- The source unit-copy family is not a one-point/vacuous group: its copy
group is a product of the nontrivial unit group of the number field `Fmod`. -/
theorem sourceFmodUnitCopies_nontrivial (j : Fin (capsuleLevels l)) :
    Nontrivial (SourceFmodUnitCopies (I := I) j) := by
  have h2 : (2 : I.initial.arithmetic.Fmod) ≠ 0 := two_ne_zero
  have hneg : (-1 : I.initial.arithmetic.Fmod) ≠ 1 := by
    intro h
    apply h2
    linear_combination -h
  refine ⟨fun _ => -1, fun _ => 1, ?_⟩
  intro h
  have hi := congrFun h ⟨0, Nat.succ_pos j.val⟩
  exact hneg (congrArg (fun u : (I.initial.arithmetic.Fmod)ˣ =>
    (u : I.initial.arithmetic.Fmod)) hi)

/-! ## 2. From source units to units of the coefficient field -/

section Generic

variable {R : Type uR} [Field R] [Algebra (I.initial.arithmetic.Fmod) R]
variable (C : SourceProcessionCapsuleContract R l V I)
variable (j : Fin (capsuleLevels l)) (vQ : C.VQ)

/-- A unit of the actual source base field, regarded as a unit of `R` through
the `R`-algebra structure.  The inverse is the image of the source inverse. -/
noncomputable def sourceFmodUnitToRUnit
    (u : (I.initial.arithmetic.Fmod)ˣ) : Rˣ where
  val := algebraMap (I.initial.arithmetic.Fmod) R (u : I.initial.arithmetic.Fmod)
  inv := algebraMap (I.initial.arithmetic.Fmod) R
    ((u⁻¹ : (I.initial.arithmetic.Fmod)ˣ) : I.initial.arithmetic.Fmod)
  val_inv := by
    rw [← map_mul, Units.mul_inv, map_one]
  inv_val := by
    rw [← map_mul, Units.inv_mul, map_one]

theorem sourceFmodUnitToRUnit_one :
    sourceFmodUnitToRUnit (I := I) (R := R) 1 = 1 := by
  ext
  simp [sourceFmodUnitToRUnit]

theorem sourceFmodUnitToRUnit_mul
    (u v : (I.initial.arithmetic.Fmod)ˣ) :
    sourceFmodUnitToRUnit (I := I) (R := R) (u * v) =
      sourceFmodUnitToRUnit (I := I) (R := R) u *
        sourceFmodUnitToRUnit (I := I) (R := R) v := by
  ext
  simp [sourceFmodUnitToRUnit, map_mul]

/-- The per-tensor-factor action of one actual `Fmod`-unit copy. -/
noncomputable def sourceInd2FactorEquiv
    (u : (I.initial.arithmetic.Fmod)ˣ) (i : Capsule j.val) :
    DirectSumFactor (C.logShell j) vQ i ≃ₗ[R]
      DirectSumFactor (C.logShell j) vQ i :=
  scalarPiEquiv (C := C) (j := j) (vQ := vQ)
    (sourceFmodUnitToRUnit (I := I) (R := R) u) i

/-- The actual tensor action of the independent `Fmod`-unit copies on the
actual tensor packet.  Each copy acts only on its own tensor factor. -/
noncomputable def sourceInd2TensorEquiv
    (f : SourceFmodUnitCopies (I := I) j) :
    ActualTensorPacket C j vQ ≃ₗ[R] ActualTensorPacket C j vQ :=
  PiTensorProduct.congr
    (fun i => sourceInd2FactorEquiv (I := I) (R := R) C j vQ (f i) i)

/-- Compatibility with pure tensors: the tensor action is the tensor of the
per-factor scalar actions. -/
theorem sourceInd2TensorEquiv_tprod
    (f : SourceFmodUnitCopies (I := I) j)
    (x : (i : Capsule j.val) → DirectSumFactor (C.logShell j) vQ i) :
    sourceInd2TensorEquiv (I := I) (R := R) C j vQ f
        (PiTensorProduct.tprod R x) =
      PiTensorProduct.tprod R
        (fun i => sourceInd2FactorEquiv (I := I) (R := R) C j vQ (f i) i (x i)) :=
  PiTensorProduct.congr_tprod _ x

/-! ## 3. Action laws -/

theorem sourceInd2FactorEquiv_one_apply
    (i : Capsule j.val)
    (x : DirectSumFactor (C.logShell j) vQ i) :
    sourceInd2FactorEquiv (I := I) (R := R) C j vQ 1 i x = x := by
  change ind2FactorAction (C := C) (j := j) (vQ := vQ)
    (sourceFmodUnitToRUnit (I := I) (R := R) 1) i x = x
  rw [sourceFmodUnitToRUnit_one, ind2FactorAction_one]
  rfl

theorem sourceInd2TensorEquiv_one_apply
    (x : ActualTensorPacket C j vQ) :
    sourceInd2TensorEquiv (I := I) (R := R) C j vQ 1 x = x := by
  induction x using PiTensorProduct.induction_on with
  | smul_tprod r x =>
      rw [map_smul, sourceInd2TensorEquiv_tprod]
      simp [sourceInd2FactorEquiv_one_apply]
  | add x y hx hy =>
      rw [map_add, hx, hy]

/-- The unit copy family acts by the identity at the unit of the copy group. -/
theorem sourceInd2TensorEquiv_one :
    sourceInd2TensorEquiv (I := I) (R := R) C j vQ 1 =
      LinearEquiv.refl R (ActualTensorPacket C j vQ) := by
  ext x
  exact sourceInd2TensorEquiv_one_apply (I := I) (R := R) C j vQ x

theorem sourceInd2FactorEquiv_mul_apply
    (u v : (I.initial.arithmetic.Fmod)ˣ) (i : Capsule j.val)
    (x : DirectSumFactor (C.logShell j) vQ i) :
    sourceInd2FactorEquiv (I := I) (R := R) C j vQ (u * v) i x =
      sourceInd2FactorEquiv (I := I) (R := R) C j vQ u i
        (sourceInd2FactorEquiv (I := I) (R := R) C j vQ v i x) := by
  ext w
  simp [sourceInd2FactorEquiv, sourceFmodUnitToRUnit, scalarPiEquiv,
    smul_smul, mul_comm]

theorem sourceInd2TensorEquiv_mul_apply
    (f g : SourceFmodUnitCopies (I := I) j)
    (x : ActualTensorPacket C j vQ) :
    sourceInd2TensorEquiv (I := I) (R := R) C j vQ (f * g) x =
      sourceInd2TensorEquiv (I := I) (R := R) C j vQ f
        (sourceInd2TensorEquiv (I := I) (R := R) C j vQ g x) := by
  induction x using PiTensorProduct.induction_on with
  | smul_tprod r x =>
      rw [map_smul, map_smul, sourceInd2TensorEquiv_tprod]
      rw [map_smul, sourceInd2TensorEquiv_tprod, sourceInd2TensorEquiv_tprod]
      simp [sourceInd2FactorEquiv_mul_apply]
  | add x y hx hy =>
      rw [map_add, map_add, hx, hy, map_add]

/-- The copy family acts multiplicatively. -/
theorem sourceInd2TensorEquiv_mul
    (f g : SourceFmodUnitCopies (I := I) j) :
    sourceInd2TensorEquiv (I := I) (R := R) C j vQ (f * g) =
      (sourceInd2TensorEquiv (I := I) (R := R) C j vQ g).trans
        (sourceInd2TensorEquiv (I := I) (R := R) C j vQ f) := by
  ext x
  rw [LinearEquiv.trans_apply]
  exact sourceInd2TensorEquiv_mul_apply (I := I) (R := R) C j vQ f g x

/-- Copies at different capsule labels are independent: their tensor actions
commute.  The proof uses commutativity of the source base field. -/
theorem sourceInd2TensorEquiv_comm
    (f g : SourceFmodUnitCopies (I := I) j) :
    (sourceInd2TensorEquiv (I := I) (R := R) C j vQ f).trans
        (sourceInd2TensorEquiv (I := I) (R := R) C j vQ g) =
      (sourceInd2TensorEquiv (I := I) (R := R) C j vQ g).trans
        (sourceInd2TensorEquiv (I := I) (R := R) C j vQ f) := by
  rw [← sourceInd2TensorEquiv_mul (f := g) (g := f),
    ← sourceInd2TensorEquiv_mul (f := f) (g := g), mul_comm]

end Generic

/-! ## 4. The unconditional actual packet over the source field itself -/

/-- The action on the actual tensor packet over the actual source base field.
This is the source-faithful carrier: no algebra hypothesis and no Real
embedding is needed. -/
noncomputable def sourceInd2FmodTensorEquiv
    (C : SourceProcessionCapsuleContract (I.initial.arithmetic.Fmod) l V I)
    (j : Fin (capsuleLevels l)) (vQ : C.VQ)
    (f : SourceFmodUnitCopies (I := I) j) :
    ActualTensorPacket C j vQ ≃ₗ[I.initial.arithmetic.Fmod]
      ActualTensorPacket C j vQ :=
  sourceInd2TensorEquiv (I := I) (R := I.initial.arithmetic.Fmod) C j vQ f

theorem sourceInd2FmodTensorEquiv_tprod
    (C : SourceProcessionCapsuleContract (I.initial.arithmetic.Fmod) l V I)
    (j : Fin (capsuleLevels l)) (vQ : C.VQ)
    (f : SourceFmodUnitCopies (I := I) j)
    (x : (i : Capsule j.val) → DirectSumFactor (C.logShell j) vQ i) :
    sourceInd2FmodTensorEquiv (I := I) C j vQ f (PiTensorProduct.tprod _ x) =
      PiTensorProduct.tprod _
        (fun i => sourceInd2FactorEquiv (I := I) (R := I.initial.arithmetic.Fmod)
          C j vQ (f i) i (x i)) :=
  sourceInd2TensorEquiv_tprod (I := I) (R := I.initial.arithmetic.Fmod) C j vQ f x

theorem sourceInd2FmodFactorEquiv_apply
    (C : SourceProcessionCapsuleContract (I.initial.arithmetic.Fmod) l V I)
    (j : Fin (capsuleLevels l)) (vQ : C.VQ)
    (u : (I.initial.arithmetic.Fmod)ˣ) (i : Capsule j.val)
    (x : DirectSumFactor (C.logShell j) vQ i) (v : C.place vQ) :
    sourceInd2FactorEquiv (I := I) (R := I.initial.arithmetic.Fmod)
        C j vQ u i x v =
      (u : I.initial.arithmetic.Fmod) • x v := rfl

theorem sourceInd2FmodTensorEquiv_tprod_apply
    (C : SourceProcessionCapsuleContract (I.initial.arithmetic.Fmod) l V I)
    (j : Fin (capsuleLevels l)) (vQ : C.VQ)
    (f : SourceFmodUnitCopies (I := I) j)
    (x : (i : Capsule j.val) → DirectSumFactor (C.logShell j) vQ i) :
    sourceInd2FmodTensorEquiv (I := I) C j vQ f (PiTensorProduct.tprod _ x) =
      PiTensorProduct.tprod _
        (fun i => (f i : I.initial.arithmetic.Fmod) • x i) := by
  rw [sourceInd2FmodTensorEquiv_tprod]
  rfl

theorem sourceInd2FmodTensorEquiv_one
    (C : SourceProcessionCapsuleContract (I.initial.arithmetic.Fmod) l V I)
    (j : Fin (capsuleLevels l)) (vQ : C.VQ) :
    sourceInd2FmodTensorEquiv (I := I) C j vQ 1 =
      LinearEquiv.refl (I.initial.arithmetic.Fmod)
        (ActualTensorPacket C j vQ) :=
  sourceInd2TensorEquiv_one (I := I) (R := I.initial.arithmetic.Fmod) C j vQ

theorem sourceInd2FmodTensorEquiv_mul
    (C : SourceProcessionCapsuleContract (I.initial.arithmetic.Fmod) l V I)
    (j : Fin (capsuleLevels l)) (vQ : C.VQ)
    (f g : SourceFmodUnitCopies (I := I) j) :
    sourceInd2FmodTensorEquiv (I := I) C j vQ (f * g) =
      (sourceInd2FmodTensorEquiv (I := I) C j vQ g).trans
        (sourceInd2FmodTensorEquiv (I := I) C j vQ f) :=
  sourceInd2TensorEquiv_mul (I := I) (R := I.initial.arithmetic.Fmod) C j vQ f g

theorem sourceInd2FmodTensorEquiv_comm
    (C : SourceProcessionCapsuleContract (I.initial.arithmetic.Fmod) l V I)
    (j : Fin (capsuleLevels l)) (vQ : C.VQ)
    (f g : SourceFmodUnitCopies (I := I) j) :
    (sourceInd2FmodTensorEquiv (I := I) C j vQ f).trans
        (sourceInd2FmodTensorEquiv (I := I) C j vQ g) =
      (sourceInd2FmodTensorEquiv (I := I) C j vQ g).trans
        (sourceInd2FmodTensorEquiv (I := I) C j vQ f) :=
  sourceInd2TensorEquiv_comm (I := I) (R := I.initial.arithmetic.Fmod) C j vQ f g

/-! ## 5. Exact first field for the Real actual tensor packet -/

/-- The exact missing field: a real embedding of the actual source base field.
`OriginalInput` carries `Fmod` but no embedding of it into `Real`. -/
abbrev SourceFmodRealEmbedding (I : OriginalInput.{ua, uv, upi, umon, ui} l V) :
    Type ua :=
  I.initial.arithmetic.Fmod →+* Real

/-- The first field is equivalently an `Algebra Fmod Real` structure. -/
theorem sourceFmodRealScalar_iff :
    Nonempty (Algebra (I.initial.arithmetic.Fmod) Real) ↔
      Nonempty (SourceFmodRealEmbedding (I := I)) := by
  constructor
  · rintro ⟨h⟩
    exact ⟨algebraMap (I.initial.arithmetic.Fmod) Real⟩
  · rintro ⟨φ⟩
    exact ⟨φ.toAlgebra⟩

/-- Conditional Real-packet bridge: a ring hom `Fmod →+* Real` turns the
actual source unit copies into actual `Real`-units, and the existing actual
Ind2 tensor action applies. -/
noncomputable def sourceInd2RealTensorEquiv
    (C : SourceProcessionCapsuleContract Real l V I)
    (j : Fin (capsuleLevels l)) (vQ : C.VQ)
    (φ : SourceFmodRealEmbedding (I := I))
    (f : SourceFmodUnitCopies (I := I) j) :
    ActualTensorPacket C j vQ ≃ₗ[Real] ActualTensorPacket C j vQ :=
  ind2TensorEquiv (C := C) (j := j) (vQ := vQ)
    (fun i => Units.map φ.toMonoidHom (f i))

theorem sourceInd2RealTensorEquiv_tprod
    (C : SourceProcessionCapsuleContract Real l V I)
    (j : Fin (capsuleLevels l)) (vQ : C.VQ)
    (φ : SourceFmodRealEmbedding (I := I))
    (f : SourceFmodUnitCopies (I := I) j)
    (x : (i : Capsule j.val) → DirectSumFactor (C.logShell j) vQ i) :
    sourceInd2RealTensorEquiv C j vQ φ f (PiTensorProduct.tprod Real x) =
      PiTensorProduct.tprod Real
        (fun i => ind2FactorAction (C := C) (j := j) (vQ := vQ)
          (Units.map φ.toMonoidHom (f i)) i (x i)) :=
  ind2TensorEquiv_tprod (C := C) (j := j) (vQ := vQ)
    (fun i => Units.map φ.toMonoidHom (f i)) x

/-- The Real bridge is exactly the existing actual Ind2 action with the source
units embedded through `φ`; no separate Real action is invented. -/
theorem sourceInd2RealTensorEquiv_eq_ind2TensorEquiv
    (C : SourceProcessionCapsuleContract Real l V I)
    (j : Fin (capsuleLevels l)) (vQ : C.VQ)
    (φ : SourceFmodRealEmbedding (I := I))
    (f : SourceFmodUnitCopies (I := I) j) :
    sourceInd2RealTensorEquiv C j vQ φ f =
      ind2TensorEquiv (C := C) (j := j) (vQ := vQ)
        (fun i => Units.map φ.toMonoidHom (f i)) := rfl

end LeanFormal.IUT.XiFPaper.S1265SourceInd2Actual

end
