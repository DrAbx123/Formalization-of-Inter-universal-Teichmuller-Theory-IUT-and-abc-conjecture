import tmp.sheaf.xif.paper.S1267TensorUnitActual
import tmp.sheaf.xif.paper.ConcreteC3RootTensorActual
import tmp.sheaf.xif.paper.ConcreteC3DonorAssemblyActual

/-!
# S1326: the actual diagonal tensor unit inside the C3 tensor landing

S1267 constructs the actual tensor unit of the concrete tensor block

  ConcreteBlock I place = tensor over Q_p of (i : FinitePrimePlace 2 7), K,
  K = CommonPrimeCompletion place,

as the diagonal insertion D z = tprod (fun _ => z) of the actual q candidate:

  concreteActualTensorUnit = Units.mkOfMulEqOne (D q) (D q^{-1}) ...,

with the definitional value law (concreteActualTensorUnit : ConcreteBlock) =
concreteTensorLanding q.q and explicit inverse D q^{-1}.  No mk0, no identity
unit, no if-then-else and no arbitrary unit is used.

This file is the consumer integration step.  It fills, with that actual unit,

* Theorem311Source.ConcreteC3RootTensorActual.ConcreteTensorLandingData, the
  exact missing tensor-landing structure of the concrete C3 root/tensor source,
  and
* the tensor part (tensorLanding, tensorLanding_q) of
  Theorem311Source.ConcreteC3DonorAssemblyActual.ConcreteC3DonorMissingFields.

Both q-landing laws are the definitional equation tensorLanding q.q = tensorUnit
(rfl); they are not postulated.  The completion-root systems, the Kummer class
tower and the root-change tower are *not* constructed here: they remain the
explicit fields of ConcreteC3DonorMissingFields, and the full record is only
formed from them as hypotheses (concreteC3DonorMissingFieldsOf).

Finally the actual tensor unit is proved different from the identity unit 1
carried by the earlier donor assembly, so installing it is not a cosmetic
change: the old assembly cannot carry the actual diagonal landing at all
(oldAssembly_tensorLanding_incompatible).

No axiom, sorry, True/PUnit placeholder, arbitrary unit or scaled target is
used.  Only propext, Classical.choice and Quot.sound can occur, from the S1267
unit construction and the finite tensor theory.
-/

noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
open scoped BigOperators TensorProduct
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.XiFPaper.S1326C3TensorUnitIntegrationActual

open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.LocalFieldPadicTensor
open LeanFormal.IUT.XiFPaper.S1219ConcreteTensorLandingActual
open LeanFormal.IUT.XiFPaper.S1267TensorUnitActual
open LeanFormal.IUT.Theorem311Source.ConcreteC3DonorActual
open LeanFormal.IUT.Theorem311Source.ConcreteC3RootTensorActual
open LeanFormal.IUT.Theorem311Source.ConcreteC3DonorAssemblyActual

universe upi umon ui

variable {l : PrimeGeFive}
variable (I : OriginalInput.{0, 0, upi, umon, ui} l (FinitePrimePlace 2 7))
variable {p : Nat} [Fact p.Prime]
variable (place : FinitePlaceAtPrime (I.initial.arithmetic.Fmod) p)

/-! ## 1. Filling ConcreteTensorLandingData with the actual diagonal unit -/

/-- The exact tensor landing structure of the concrete C3 root/tensor source,
filled by actual data:

* tensor index FinitePrimePlace 2 7;
* one place per index, the supplied actual place;
* tensor landing z |-> tprod (fun _ => z);
* tensor unit the actual diagonal insertion of the q candidate.

The q law is definitional.  Compared with the obstruction recorded in
ConcreteC3RootTensorActual, only the data is supplied; nothing about it is
postulated. -/
noncomputable def concreteTensorLandingDataActual :
    ConcreteTensorLandingData (I := I) place where
  tensorIndex := ConcreteIndex
  tensorFintype := inferInstance
  tensorPlaceIndex := ConcretePlaceIndex
  tensorPlaces := concretePlaces (I := I) (p := p) place
  tensorTuple := concreteTuple
  tensorUnit := concreteActualTensorUnit (I := I) (p := p) place
  tensorLanding := concreteTensorLanding (I := I) (p := p) place
  tensorLanding_q := rfl

/-- The exact tensor-landing obstruction of ConcreteC3RootTensorActual is now
resolved by actual data (the unit is the diagonal insertion of S1267). -/
theorem concreteTensorLandingObstruction_resolved :
    ConcreteTensorLandingObstruction (I := I) place :=
  ⟨concreteTensorLandingDataActual (I := I) (p := p) place⟩

/-- The tensor unit of the filled landing data is the actual diagonal insertion
of the chosen q candidate. -/
@[simp] theorem concreteTensorLandingDataActual_tensorUnit_val :
    ((concreteTensorLandingDataActual (I := I) (p := p) place).tensorUnit :
      ArithmeticTensorTupleBlock
        (concreteTensorLandingDataActual (I := I) (p := p) place).tensorPlaces
        (concreteTensorLandingDataActual (I := I) (p := p) place).tensorTuple) =
    concreteTensorLanding (I := I) (p := p) place
      ((concreteQCandidate (I := I) place).q) :=
  concreteActualTensorUnit_val_eq_landing (I := I) (p := p) place

/-- The q landing law of the filled landing data in the exact consumer form. -/
theorem concreteTensorLandingDataActual_tensorLanding_q :
    (concreteTensorLandingDataActual (I := I) (p := p) place).tensorLanding
        (((concreteC3ActualFields (I := I) place).q).q) =
      ((concreteTensorLandingDataActual (I := I) (p := p) place).tensorUnit :
        ArithmeticTensorTupleBlock
          (concreteTensorLandingDataActual (I := I) (p := p) place).tensorPlaces
          (concreteTensorLandingDataActual (I := I) (p := p) place).tensorTuple) :=
  rfl

/-- The q landing itself is nonzero (S1219 diagonal nonzero theorem). -/
theorem concreteTensorLandingDataActual_landing_q_ne_zero :
    concreteTensorLanding (I := I) (p := p) place
      ((concreteQCandidate (I := I) place).q) ≠ 0 :=
  concreteTensorLanding_ne_zero (I := I) (p := p) place
    (concreteQCandidate (I := I) place) (concreteQCandidate (I := I) place).q_ne_zero

/-- The filled tensor unit is nonzero: its underlying element is the nonzero
diagonal insertion (the unit is an actual unit of the tensor ring). -/
theorem concreteTensorLandingDataActual_tensorUnit_ne_zero :
    ((concreteTensorLandingDataActual (I := I) (p := p) place).tensorUnit :
      ArithmeticTensorTupleBlock
        (concreteTensorLandingDataActual (I := I) (p := p) place).tensorPlaces
        (concreteTensorLandingDataActual (I := I) (p := p) place).tensorTuple) ≠ 0 := by
  rw [concreteTensorLandingDataActual_tensorUnit_val]
  exact concreteTensorLandingDataActual_landing_q_ne_zero (I := I) (p := p) place

/-! ## 2. The donor assembly carrying the actual tensor unit

ConcreteC3DonorAssemblyActual is the actual constructible part of the C3 donor
fields.  Its tensor unit used to be the identity unit 1; the q landing law of
ConcreteC3DonorMissingFields therefore could not be met.  The assembly below
only changes that field to the actual diagonal unit; all other fields are the
actual ones. -/

/-- The actual C3 donor assembly with its tensor unit replaced by the actual
diagonal tensor unit (all other fields are those of the actual assembly). -/
noncomputable def actualConcreteC3DonorAssemblyActualUnit :
    ConcreteC3DonorAssemblyActual (I := I) :=
  { actualConcreteC3DonorAssembly (I := I) place with
    tensorUnit := concreteActualTensorUnit (I := I) (p := p) place }

/-- The tensor unit of the corrected assembly is the actual diagonal insertion. -/
@[simp] theorem actualConcreteC3DonorAssemblyActualUnit_tensorUnit :
    (actualConcreteC3DonorAssemblyActualUnit (I := I) (p := p) place).tensorUnit =
      concreteActualTensorUnit (I := I) (p := p) place :=
  rfl

/-- The q unit of the corrected assembly is the actual completion q unit. -/
@[simp] theorem actualConcreteC3DonorAssemblyActualUnit_qUnit :
    (actualConcreteC3DonorAssemblyActualUnit (I := I) (p := p) place).qUnit =
      concreteQUnit (I := I) place :=
  rfl

/-- The assembly-level q landing law: the actual diagonal landing of the actual
q candidate is the actual tensor unit of the corrected assembly.  This is the
exact statement consumed by ConcreteC3DonorMissingFields.tensorLanding_q. -/
theorem actualConcreteC3DonorAssemblyActualUnit_tensorLanding_q :
    concreteTensorLanding (I := I) (p := p) place
        (((actualConcreteC3DonorAssemblyActualUnit (I := I) (p := p) place).q).q) =
      ((actualConcreteC3DonorAssemblyActualUnit (I := I) (p := p) place).tensorUnit :
        ArithmeticTensorTupleBlock
          (actualConcreteC3DonorAssemblyActualUnit (I := I) (p := p) place).tensorPlaces
          (actualConcreteC3DonorAssemblyActualUnit (I := I) (p := p) place).tensorTuple) :=
  rfl

/-- The tensor unit of the old assembly was the identity unit 1; this is the
fake unit that the integration replaces. -/
theorem actualConcreteC3DonorAssembly_tensorUnit_val :
    ((actualConcreteC3DonorAssembly (I := I) place).tensorUnit :
      ArithmeticTensorTupleBlock
        (actualConcreteC3DonorAssembly (I := I) place).tensorPlaces
        (actualConcreteC3DonorAssembly (I := I) place).tensorTuple) = 1 :=
  rfl

/-! ## 3. The tensor fields of ConcreteC3DonorMissingFields

ConcreteC3DonorMissingFields has the fields roots, roots', kummerClass,
rootChange, rootChange_eq, tensorLanding, tensorLanding_q.  The first five are
the genuinely missing completion-root/Kummer data; the last two are exactly the
two fields constructed here. -/

/-- The exact last two fields of ConcreteC3DonorMissingFields, for a fixed
actual assembly: the tensor landing map and its q law. -/
structure ConcreteC3DonorTensorLandingFields
    (A : ConcreteC3DonorAssemblyActual (I := I)) where
  tensorLanding : CommonPrimeCompletion (K := I.initial.arithmetic.Fmod) A.place →
    ArithmeticTensorTupleBlock A.tensorPlaces A.tensorTuple
  tensorLanding_q : tensorLanding
    (A.q.q : CommonPrimeCompletion (K := I.initial.arithmetic.Fmod) A.place) =
    (A.tensorUnit : ArithmeticTensorTupleBlock A.tensorPlaces A.tensorTuple)

/-- The exact tensor-landing fields at the actual-unit assembly, filled by the
actual diagonal landing and with the q law definitional. -/
noncomputable def concreteC3DonorTensorLandingFields :
    ConcreteC3DonorTensorLandingFields (I := I)
      (actualConcreteC3DonorAssemblyActualUnit (I := I) (p := p) place) where
  tensorLanding := concreteTensorLanding (I := I) (p := p) place
  tensorLanding_q := rfl

/-- The q law of the exact tensor-landing fields. -/
theorem concreteC3DonorTensorLandingFields_tensorLanding_q :
    (concreteC3DonorTensorLandingFields (I := I) (p := p) place).tensorLanding
        (((actualConcreteC3DonorAssemblyActualUnit (I := I) (p := p) place).q).q) =
      ((actualConcreteC3DonorAssemblyActualUnit (I := I) (p := p) place).tensorUnit :
        ArithmeticTensorTupleBlock
          (actualConcreteC3DonorAssemblyActualUnit (I := I) (p := p) place).tensorPlaces
          (actualConcreteC3DonorAssemblyActualUnit (I := I) (p := p) place).tensorTuple) :=
  rfl

/-- The full ConcreteC3DonorMissingFields record at the actual-unit assembly,
conditional exactly on the completion-root/Kummer data that the concrete source
does not supply.  The tensor fields are the actual ones above and the q law is
definitional: no root, Kummer class or landing is fabricated. -/
noncomputable def concreteC3DonorMissingFieldsOf
    (roots : NatRootSystem (concreteQUnit (I := I) place))
    (roots' : NatRootSystem (concreteQUnit (I := I) place))
    (kummerClass : CyclotomicTower
      (CommonPrimeCompletion (K := I.initial.arithmetic.Fmod) place))
    (rootChange : CyclotomicTower
      (CommonPrimeCompletion (K := I.initial.arithmetic.Fmod) place))
    (rootChange_eq : rootChange = KummerClass.rootSystemDiff roots roots') :
    ConcreteC3DonorMissingFields (I := I)
      (actualConcreteC3DonorAssemblyActualUnit (I := I) (p := p) place) where
  roots := roots
  roots' := roots'
  kummerClass := kummerClass
  rootChange := rootChange
  rootChange_eq := rootChange_eq
  tensorLanding := concreteTensorLanding (I := I) (p := p) place
  tensorLanding_q := rfl

/-- The tensor landing of the conditional full missing-field record is the
actual diagonal landing. -/
@[simp] theorem concreteC3DonorMissingFieldsOf_tensorLanding
    (roots : NatRootSystem (concreteQUnit (I := I) place))
    (roots' : NatRootSystem (concreteQUnit (I := I) place))
    (kummerClass : CyclotomicTower
      (CommonPrimeCompletion (K := I.initial.arithmetic.Fmod) place))
    (rootChange : CyclotomicTower
      (CommonPrimeCompletion (K := I.initial.arithmetic.Fmod) place))
    (rootChange_eq : rootChange = KummerClass.rootSystemDiff roots roots') :
    (concreteC3DonorMissingFieldsOf (I := I) (p := p) place
      roots roots' kummerClass rootChange rootChange_eq).tensorLanding =
      concreteTensorLanding (I := I) (p := p) place :=
  rfl

/-- End-to-end: with the missing roots/Kummer data as hypotheses, the
actual-unit assembly and the actual tensor landing compose into a full
SourcePilotRegionDonors. -/
noncomputable def concreteC3DonorSourcePilotRegionDonorsOf
    (roots : NatRootSystem (concreteQUnit (I := I) place))
    (roots' : NatRootSystem (concreteQUnit (I := I) place))
    (kummerClass : CyclotomicTower
      (CommonPrimeCompletion (K := I.initial.arithmetic.Fmod) place))
    (rootChange : CyclotomicTower
      (CommonPrimeCompletion (K := I.initial.arithmetic.Fmod) place))
    (rootChange_eq : rootChange = KummerClass.rootSystemDiff roots roots') :
    LeanFormal.IUT.N8Closure.C3Actual.SourcePilotRegionDonors
      (l := l) (V := FinitePrimePlace 2 7) (I := I) where
  p := p
  hp := inferInstance
  place := place
  q := concreteQCandidate (I := I) place
  thetaPacket := concreteThetaPacket (I := I)
  roots := roots
  roots' := roots'
  kummerClass := kummerClass
  rootChange := rootChange
  rootChange_eq := rootChange_eq
  tensorIndex := ConcreteIndex
  tensorFintype := inferInstance
  tensorPlaceIndex := ConcretePlaceIndex
  tensorPlaces := concretePlaces (I := I) (p := p) place
  tensorTuple := concreteTuple
  tensorUnit := concreteActualTensorUnit (I := I) (p := p) place
  tensorLanding := concreteTensorLanding (I := I) (p := p) place
  tensorLanding_q := rfl

/-! ## 4. Non-fakeness: the integrated unit is not the identity unit

The fold linear map multiplies the factors of a pure tensor.  On the diagonal
landing it is z to the number of tensor factors.  If the diagonal landing of the
q candidate were 1, then q ^ n = 1, contradicting the q-candidate valuation
Valued.v q < 1.  Hence the actual tensor unit is not 1, and the old
identity-unit assembly cannot carry the actual landing. -/

/-- The factor-multiplication linear map from the concrete tensor block to the
completion (the fold map). -/
noncomputable def concreteTensorFoldMap :
    ConcreteBlock I place →ₗ[ℚ_[p]]
      CommonPrimeCompletion (K := I.initial.arithmetic.Fmod) place :=
  PiTensorProduct.lift
    (MultilinearMap.mkPiAlgebra ℚ_[p] ConcreteIndex
      (CommonPrimeCompletion (K := I.initial.arithmetic.Fmod) place))

/-- The fold map on a pure tensor multiplies the factors. -/
theorem concreteTensorFoldMap_tprod
    (x : ConcreteIndex → CommonPrimeCompletion (K := I.initial.arithmetic.Fmod) place) :
    concreteTensorFoldMap (I := I) (p := p) place
        (finitePadicTensorTprod (p := p)
          (M := fun _ : ConcreteIndex =>
            CommonPrimeCompletion (K := I.initial.arithmetic.Fmod) place) x) =
      ∏ i, x i := by
  change PiTensorProduct.lift
      (MultilinearMap.mkPiAlgebra ℚ_[p] ConcreteIndex
        (CommonPrimeCompletion (K := I.initial.arithmetic.Fmod) place))
      (PiTensorProduct.tprod ℚ_[p] x) = ∏ i, x i
  rw [PiTensorProduct.lift.tprod, MultilinearMap.mkPiAlgebra_apply]

/-- The fold map of the diagonal landing of z is z to the number of tensor
factors. -/
theorem concreteTensorFoldMap_landing
    (z : CommonPrimeCompletion (K := I.initial.arithmetic.Fmod) place) :
    concreteTensorFoldMap (I := I) (p := p) place
        (concreteTensorLanding (I := I) (p := p) place z) =
      z ^ Fintype.card ConcreteIndex := by
  rw [concreteTensorLanding_apply, concreteTensorFoldMap_tprod, Finset.prod_const,
    Finset.card_univ]

/-- The fold map sends the identity of the tensor block to 1. -/
theorem concreteTensorFoldMap_one :
    concreteTensorFoldMap (I := I) (p := p) place 1 = 1 := by
  rw [← concreteTensorLanding_one (I := I) (p := p) place, concreteTensorFoldMap_landing]
  simp

/-- The concrete tensor index is nonempty (it contains the prime 2). -/
theorem concreteIndex_nonempty : Nonempty ConcreteIndex :=
  ⟨⟨2, by rw [mem_primeStrip_iff]; norm_num⟩⟩

/-- The diagonal landing of a q candidate is not the identity element: the
q candidate has Valued.v q < 1, while a 1 landing would force q ^ n = 1. -/
theorem concreteTensorLanding_qCandidate_ne_one
    (q : FinitePlaceQCandidate place.val) :
    concreteTensorLanding (I := I) (p := p) place
      (q.q : CommonPrimeCompletion (K := I.initial.arithmetic.Fmod) place) ≠ 1 := by
  intro h
  have hfold := congrArg (concreteTensorFoldMap (I := I) (p := p) place) h
  rw [concreteTensorFoldMap_landing, concreteTensorFoldMap_one] at hfold
  have hfoldC : (q.q : Completion place.val) ^ Fintype.card ConcreteIndex = 1 := hfold
  have hcard : 0 < Fintype.card ConcreteIndex := by
    rw [Fintype.card_pos_iff]
    exact concreteIndex_nonempty
  have hmul : (Valued.v q.q : WithZero (Multiplicative Int)) ^
      Fintype.card ConcreteIndex = 1 := by
    have h1 : Valued.v (q.q ^ Fintype.card ConcreteIndex) = 1 := by
      rw [hfoldC]
      simp
    rwa [map_pow] at h1
  have hlt : (Valued.v q.q : WithZero (Multiplicative Int)) ^
      Fintype.card ConcreteIndex < 1 :=
    pow_lt_one₀ bot_le q.valuation_lt_one (Nat.ne_of_gt hcard)
  rw [hmul] at hlt
  exact lt_irrefl 1 hlt

/-- The actual tensor unit of S1267 is not the identity unit. -/
theorem concreteActualTensorUnit_ne_one :
    concreteActualTensorUnit (I := I) (p := p) place ≠ 1 := by
  intro h
  have hval : (concreteActualTensorUnit (I := I) (p := p) place : ConcreteBlock I place) = 1 := by
    simpa using congrArg Units.val h
  have hland : concreteTensorLanding (I := I) (p := p) place
      ((Classical.choice (finitePlaceQCandidate_nonempty place.val)).q :
        CommonPrimeCompletion (K := I.initial.arithmetic.Fmod) place) = 1 := by
    rwa [concreteActualTensorUnit_val_eq_landing (I := I) (p := p) place] at hval
  exact concreteTensorLanding_qCandidate_ne_one (I := I) (p := p) place
    (Classical.choice (finitePlaceQCandidate_nonempty place.val)) hland

/-- The tensor unit of the filled landing data is not 1. -/
theorem concreteTensorLandingDataActual_tensorUnit_ne_one :
    (concreteTensorLandingDataActual (I := I) (p := p) place).tensorUnit ≠ 1 :=
  concreteActualTensorUnit_ne_one (I := I) (p := p) place

/-- The tensor unit of the corrected assembly is not 1. -/
theorem actualConcreteC3DonorAssemblyActualUnit_tensorUnit_ne_one :
    (actualConcreteC3DonorAssemblyActualUnit (I := I) (p := p) place).tensorUnit ≠ 1 :=
  concreteActualTensorUnit_ne_one (I := I) (p := p) place

/-- The old donor assembly (tensor unit 1) cannot carry the actual diagonal
tensor landing: the q law of ConcreteC3DonorMissingFields would force the
landing of q to be 1, which the actual diagonal landing is not. -/
theorem oldAssembly_tensorLanding_incompatible :
    ¬ ∃ M : ConcreteC3DonorMissingFields (I := I)
        (actualConcreteC3DonorAssembly (I := I) place),
      M.tensorLanding = concreteTensorLanding (I := I) (p := p) place := by
  rintro ⟨M, hM⟩
  have hq := M.tensorLanding_q
  rw [hM] at hq
  rw [actualConcreteC3DonorAssembly_tensorUnit_val (I := I) (p := p) place] at hq
  exact concreteTensorLanding_qCandidate_ne_one (I := I) (p := p) place
    (concreteQCandidate (I := I) place) hq

end LeanFormal.IUT.XiFPaper.S1326C3TensorUnitIntegrationActual

end
