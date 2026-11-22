import LeanFormal.IUT.Foundations.Theta.GaussianKernel
import LeanFormal.IUT.Foundations.Theta.SignedLabelEquiv
import LeanFormal.IUT.IUTIII.Theorem311.ConcreteFiniteModel
import LeanFormal.IUT.IUTII.Frobenioid.ConcreteSourceFrobenioidBridge
import Iut.Foundations.Frobenioid
import LeanFormal.IUT.Audit.Status
import Mathlib.Tactic

/-!
  Label-weighted diagonal objects with Gaussian weights `j ^ 2`.

  This file realizes the finite-model species of IUT II, Remark 4.5.4.
  On the divisor side the diagonal sends a divisor `phi` to the family
  `fun j => j.weight • phi` indexed by the bounded signed labels of `F_l`.
  On the multiplicative theta side it sends a unit `beta` to
  `fun j => beta ^ j.weight`.

  The construction is finite-model bookkeeping.  It does not construct the
  source-level `gau`-Frobenioid carrier or calibrate the source-side
  `G`-action on the exponents (audit gap B2); see the audit card below.
-/

namespace LeanFormal.IUT.SourceLabelWeightedDiagonal

open LeanFormal.IUT
open CategoryTheory

noncomputable section

/-! ## Weights and the distinguished labels `0` and `1` -/

/-- The Gaussian label weight `j ^ 2`, as a natural number. -/
def labelWeight {l : Nat} (j : SignedLabel l) : Nat :=
  (gaussExponent j.1).toNat

/-- The label `0`, available for every label length. -/
def zeroLabel {l : Nat} : SignedLabel l :=
  ⟨0, by
    change -(lStar l : Int) ≤ (0 : Int) ∧ (0 : Int) ≤ (lStar l : Int)
    exact ⟨neg_nonpos.mpr (Int.natCast_nonneg _), Int.natCast_nonneg _⟩⟩

/-- The label `1`, available once the label interval reaches `[-1, 1]`. -/
def oneLabel {l : Nat} (h : 1 ≤ lStar l) : SignedLabel l :=
  ⟨1, by
    change -(lStar l : Int) ≤ (1 : Int) ∧ (1 : Int) ≤ (lStar l : Int)
    have h' : (1 : Int) ≤ (lStar l : Int) := by exact_mod_cast h
    exact ⟨by omega, h'⟩⟩

@[simp] theorem labelWeight_zeroLabel {l : Nat} :
    labelWeight (zeroLabel (l := l)) = 0 := by
  simp [labelWeight, zeroLabel, gaussExponent]

@[simp] theorem labelWeight_oneLabel {l : Nat} (h : 1 ≤ lStar l) :
    labelWeight (oneLabel h) = 1 := by
  simp [labelWeight, oneLabel, gaussExponent]

@[simp] theorem labelWeight_neg {l : Nat} (j : SignedLabel l) :
    labelWeight (SignedLabel.neg j) = labelWeight j := by
  simp [labelWeight]

@[simp] theorem toFiniteLabel_zeroLabel (l : PrimeGeFive) :
    SignedLabel.toFiniteLabel l (zeroLabel (l := l.value)) = 0 := by
  simp [SignedLabel.toFiniteLabel, SignedLabel.toFl, zeroLabel]

/-! ## The additive diagonal on divisor monoids -/

section Additive

variable {M : Type*} [AddCommMonoid M]

/-- The family `fun j => j.weight • phi`, the divisor-side diagonal. -/
def weightedDiagonal (l : Nat) (phi : M) : SignedLabel l → M :=
  fun j => labelWeight j • phi

@[simp] theorem weightedDiagonal_apply (l : Nat) (phi : M) (j : SignedLabel l) :
    weightedDiagonal l phi j = labelWeight j • phi :=
  rfl

/-- The additive monoid hom `phi ↦ (j ↦ j.weight • phi)`. -/
def weightedDiagonalHom (l : Nat) : M →+ (SignedLabel l → M) where
  toFun := weightedDiagonal (M := M) l
  map_zero' := by
    funext j
    exact nsmul_zero _
  map_add' phi psi := by
    funext j
    exact nsmul_add phi psi _

@[simp] theorem weightedDiagonalHom_apply (l : Nat) (phi : M) (j : SignedLabel l) :
    weightedDiagonalHom (M := M) l phi j = labelWeight j • phi :=
  rfl

/-- The diagonal is injective once the label `1` is available. -/
theorem weightedDiagonal_injective {l : Nat} (h : 1 ≤ lStar l) :
    Function.Injective (weightedDiagonal (M := M) l) := by
  intro phi psi hphi
  have h1 := congrFun hphi (oneLabel h)
  simpa [weightedDiagonal, labelWeight_oneLabel h] using h1

@[simp] theorem weightedDiagonal_neg (l : Nat) (phi : M) (j : SignedLabel l) :
    weightedDiagonal l phi (SignedLabel.neg j) = weightedDiagonal l phi j := by
  simp [weightedDiagonal]

@[simp] theorem weightedDiagonal_zeroLabel (l : Nat) (phi : M) :
    weightedDiagonal l phi (zeroLabel (l := l)) = 0 := by
  simp [weightedDiagonal]

/-- The additive submonoid of label-weighted diagonal families. -/
def weightedDiagonalAddSubmonoid (l : Nat) : AddSubmonoid (SignedLabel l → M) :=
  AddMonoidHom.mrange (weightedDiagonalHom (M := M) l)

/-- Exact range characterization: a family is a diagonal exactly when every
    coordinate is the `j ^ 2`-multiple of the coordinate at label `1`. -/
theorem mem_weightedDiagonalAddSubmonoid_iff {l : Nat} (h : 1 ≤ lStar l)
    (D : SignedLabel l → M) :
    D ∈ weightedDiagonalAddSubmonoid (M := M) l ↔
      ∀ j, D j = labelWeight j • D (oneLabel h) := by
  constructor
  · intro hD
    rw [weightedDiagonalAddSubmonoid, AddMonoidHom.mem_mrange] at hD
    obtain ⟨phi, rfl⟩ := hD
    intro j
    simp [weightedDiagonalHom_apply, labelWeight_oneLabel h]
  · intro hD
    rw [weightedDiagonalAddSubmonoid, AddMonoidHom.mem_mrange]
    refine ⟨D (oneLabel h), ?_⟩
    funext j
    change labelWeight j • D (oneLabel h) = D j
    exact (hD j).symm

end Additive

/-! ## The multiplicative diagonal on theta values -/

section Multiplicative

variable {M : Type*} [CommMonoid M]

/-- The family `fun j => beta ^ j.weight`, the multiplicative diagonal. -/
def weightedDiagonalMul (l : Nat) (beta : M) : SignedLabel l → M :=
  fun j => beta ^ labelWeight j

@[simp] theorem weightedDiagonalMul_apply (l : Nat) (beta : M) (j : SignedLabel l) :
    weightedDiagonalMul l beta j = beta ^ labelWeight j :=
  rfl

/-- The multiplicative monoid hom `beta ↦ (j ↦ beta ^ j.weight)`. -/
def weightedDiagonalMulHom (l : Nat) : M →* (SignedLabel l → M) where
  toFun := weightedDiagonalMul (M := M) l
  map_one' := by
    funext j
    exact one_pow _
  map_mul' beta gamma := by
    funext j
    exact mul_pow beta gamma _

@[simp] theorem weightedDiagonalMulHom_apply (l : Nat) (beta : M) (j : SignedLabel l) :
    weightedDiagonalMulHom (M := M) l beta j = beta ^ labelWeight j :=
  rfl

/-- The multiplicative diagonal is injective once label `1` is available. -/
theorem weightedDiagonalMul_injective {l : Nat} (h : 1 ≤ lStar l) :
    Function.Injective (weightedDiagonalMul (M := M) l) := by
  intro beta gamma hbeta
  have h1 := congrFun hbeta (oneLabel h)
  simpa [weightedDiagonalMul, labelWeight_oneLabel h] using h1

@[simp] theorem weightedDiagonalMul_neg (l : Nat) (beta : M) (j : SignedLabel l) :
    weightedDiagonalMul l beta (SignedLabel.neg j) = weightedDiagonalMul l beta j := by
  simp [weightedDiagonalMul]

@[simp] theorem weightedDiagonalMul_zeroLabel (l : Nat) (beta : M) :
    weightedDiagonalMul l beta (zeroLabel (l := l)) = 1 := by
  simp [weightedDiagonalMul]

/-- The multiplicative submonoid of label-weighted diagonal families. -/
def weightedDiagonalSubmonoid (l : Nat) : Submonoid (SignedLabel l → M) :=
  MonoidHom.mrange (weightedDiagonalMulHom (M := M) l)

/-- Exact range characterization on the multiplicative side. -/
theorem mem_weightedDiagonalSubmonoid_iff {l : Nat} (h : 1 ≤ lStar l)
    (D : SignedLabel l → M) :
    D ∈ weightedDiagonalSubmonoid (M := M) l ↔
      ∀ j, D j = D (oneLabel h) ^ labelWeight j := by
  constructor
  · intro hD
    rw [weightedDiagonalSubmonoid, MonoidHom.mem_mrange] at hD
    obtain ⟨beta, rfl⟩ := hD
    intro j
    simp [labelWeight_oneLabel h]
  · intro hD
    rw [weightedDiagonalSubmonoid, MonoidHom.mem_mrange]
    refine ⟨D (oneLabel h), ?_⟩
    funext j
    change D (oneLabel h) ^ labelWeight j = D j
    exact (hD j).symm

end Multiplicative

/-! ## Weights on `F_l` through the bounded representative -/

/-- The Gaussian weight of a finite label, via its bounded representative. -/
def labelWeightOnFl (l : PrimeGeFive) (x : Fl l.value) : Nat :=
  labelWeight (SignedLabel.representative l x)

theorem representative_toFiniteLabel (l : PrimeGeFive)
    (j : SignedLabel l.value) :
    SignedLabel.representative l (SignedLabel.toFiniteLabel l j) = j := by
  simpa using (SignedLabel.equiv l).symm_apply_apply j

theorem labelWeightOnFl_toFiniteLabel (l : PrimeGeFive)
    (j : SignedLabel l.value) :
    labelWeightOnFl l (SignedLabel.toFiniteLabel l j) = labelWeight j := by
  simp [labelWeightOnFl, representative_toFiniteLabel]

theorem representative_zero (l : PrimeGeFive) :
    SignedLabel.representative l 0 = zeroLabel (l := l.value) := by
  apply SignedLabel.toFiniteLabel_injective l
  rw [SignedLabel.representative_toFl, toFiniteLabel_zeroLabel]

@[simp] theorem labelWeightOnFl_zero (l : PrimeGeFive) :
    labelWeightOnFl l 0 = 0 := by
  simp [labelWeightOnFl, representative_zero]

/-- The zero element of `F_l` is exactly the representative of the label `0`. -/
theorem representative_eq_zeroLabel_iff (l : PrimeGeFive) (x : Fl l.value) :
    SignedLabel.representative l x = zeroLabel (l := l.value) ↔ x = 0 := by
  constructor
  · intro h
    have h' := congrArg (SignedLabel.toFiniteLabel l) h
    simpa [SignedLabel.representative_toFl, toFiniteLabel_zeroLabel] using h'
  · intro h
    rw [h]
    exact representative_zero l

/-- Nonzero finite labels correspond to representatives away from label `0`. -/
theorem representative_ne_zeroLabel_iff (l : PrimeGeFive) (x : Fl l.value) :
    SignedLabel.representative l x ≠ zeroLabel (l := l.value) ↔ x ≠ 0 := by
  constructor
  · intro h hx
    exact h ((representative_eq_zeroLabel_iff l x).mpr hx)
  · intro hx h
    exact hx ((representative_eq_zeroLabel_iff l x).mp h)

/-! ## The diagonal on a divisorial monoid -/

universe u

section Frobenioid

variable {B : Type u} [Category.{u} B]
variable {IsFSM : ∀ {X Y : B}, (X ⟶ Y) → Prop}

/-- The label-weighted diagonal on the divisor monoid at a base object. -/
def frobenioidWeightedDiagonal (Phi : Iut.DivisorialMonoidOn B IsFSM)
    (stage : B) (l : Nat) :
    (Phi.obj stage).carrier →+
      (SignedLabel l → (Phi.obj stage).carrier) :=
  weightedDiagonalHom (M := (Phi.obj stage).carrier) l

/-- The carrier of the concrete CSFB stage divisorial monoid. -/
abbrev concreteStageDivisorCarrier
    (stage : ConcreteSourceFrobenioidBridge.concreteStageBase) : Type :=
  (ConcreteSourceFrobenioidBridge.concreteStageModelDivisorialMonoid.obj
    stage).carrier

/-- Concrete check: on the CSFB stage divisorial monoid, membership in the
    diagonal range is exactly the `j ^ 2 • phi` shape. -/
theorem concreteStageDivisor_weightedDiagonal_iff
    (l : Nat) (h : 1 ≤ lStar l)
    (stage : ConcreteSourceFrobenioidBridge.concreteStageBase)
    (D : SignedLabel l → concreteStageDivisorCarrier stage) :
    D ∈ AddMonoidHom.mrange (frobenioidWeightedDiagonal
        ConcreteSourceFrobenioidBridge.concreteStageModelDivisorialMonoid
        stage l) ↔
      ∀ j, D j = labelWeight j • D (oneLabel h) :=
  mem_weightedDiagonalAddSubmonoid_iff h D

end Frobenioid

/-! ## Theta-packet consumer: `q ^ (j ^ 2)` as a multiplicative diagonal -/

section ThetaConsumers

/-- `realThetaValue q j` is the `j ^ 2`-th power of the base unit `q`. -/
theorem realThetaValue_eq_unit_pow (q : Real) {l : Nat} (j : SignedLabel l) :
    realThetaValue q j.1 = q ^ labelWeight j :=
  rfl

theorem thetaScale_eq_gaussianFiveThetaQ_pow (l : PrimeGeFive)
    (j : SignedLabel l.value) :
    ConcreteSourceEtaleThetaBridge.thetaScale l j =
      gaussianFiveThetaQ ^ labelWeight j := by
  rw [ConcreteSourceEtaleThetaBridge.theta_scale_eq_real_value]
  exact realThetaValue_eq_unit_pow gaussianFiveThetaQ j

/-- The theta scale at any label is the scale at label `1` raised to the
    Gaussian weight. -/
theorem thetaScale_eq_oneLabel_pow (l : PrimeGeFive) (h : 1 ≤ lStar l.value)
    (j : SignedLabel l.value) :
    ConcreteSourceEtaleThetaBridge.thetaScale l j =
      ConcreteSourceEtaleThetaBridge.thetaScale l (oneLabel h) ^
        labelWeight j := by
  rw [thetaScale_eq_gaussianFiveThetaQ_pow,
    thetaScale_eq_gaussianFiveThetaQ_pow]
  simp [labelWeight_oneLabel h]

theorem thetaScale_finiteModel_eq_source (l : PrimeGeFive)
    (j : SignedLabel l.value) :
    ConcreteFiniteTheorem311.thetaScale l j =
      ConcreteSourceEtaleThetaBridge.thetaScale l j :=
  rfl

/-- The concrete theta packet is the multiplicative label-weighted diagonal
    with base unit the `j = 1` scale. -/
theorem thetaPacket_scale_eq_weightedDiagonalMul (l : PrimeGeFive)
    (h : 1 ≤ lStar l.value) :
    (ConcreteFiniteTheorem311.thetaPacket l).scale =
      weightedDiagonalMul (M := Real) l.value
        (ConcreteSourceEtaleThetaBridge.thetaScale l (oneLabel h)) := by
  funext j
  rw [ConcreteFiniteTheorem311.thetaPacket_scale]
  simp only [thetaScale_finiteModel_eq_source, weightedDiagonalMul_apply]
  exact thetaScale_eq_oneLabel_pow l h j

end ThetaConsumers

end

end LeanFormal.IUT.SourceLabelWeightedDiagonal

namespace LeanFormal.IUT.Audit

/-- Finite-model audit card for the label-weighted diagonal S2-W-2. -/
def sourceLabelWeightedDiagonal : Obligation :=
  { id := "IUT-III.source-label-weighted-diagonal"
    source :=
      "IUT II, Remark 4.5.4: divisor family of `j ^ 2`-multiples on a " ++
        "labeled Frobenioid"
    status := VerificationStatus.provedKernel
    note :=
      "Finite-model construction only. The divisor-side diagonal " ++
        "`j ↦ j ^ 2 • phi` has an exact range characterization, the " ++
        "multiplicative side is `j ↦ beta ^ (j ^ 2)`, and the concrete " ++
        "theta packet is proved to be the multiplicative diagonal with " ++
        "base unit the `j = 1` scale. This does not construct the " ++
        "source-level gau-Frobenioid carrier, does not calibrate the " ++
        "source-side G-action on labels (audit gap B2), and does not " ++
        "assert Remark 4.5.4 at source level."
    dependsOn :=
      [ "Foundations.Theta.GaussianKernel",
        "IUT-I-II.concrete-source-frobenioid-bridge",
        "IUT-I-II.concrete-source-algebraic-theta-bridge",
        "IUT-III.concrete-finite-theorem311-model" ] }

end LeanFormal.IUT.Audit
