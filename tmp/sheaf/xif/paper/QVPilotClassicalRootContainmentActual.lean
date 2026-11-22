import tmp.sheaf.xif.paper.QVFamTensorCoefficientActual
import tmp.sheaf.xif.paper.ThetaTensorScaledImageActual
import LeanFormal.IUT.ABCBridge.Geometry.FinitePlaceFractionalTensorLattice
import LeanFormal.IUT.ABCBridge.Geometry.FinitePlaceArithmeticTensorBlocks
import tmp.sheaf.xif.paper.QPilotZeroLocusDivisorActual
import tmp.sheaf.xif.paper.SignedLabelOneActual
import LeanFormal.IUT.IUTIII.Corollary312.StepXI.HolomorphicHull.CardHullRealGeneratorNonpositivity

/-! # Classical q-pilot region inside the root theta hull

The classical q-pilot coefficient is c_norm = order(qVFamily b).  The root
coefficient is c_root = order(qVFamily b)/(2l).  Since 2l >= 1 and order >= 0,

  c_norm >= c_root,

and the antitone fractional lattice gives

  F(c_norm) <= F(c_root).

Multiplying by the fixed holomorphic lattice gives

  F(c_norm) * O_hol subset F(c_root) * O_hol.

The root scaled region at label j uses coefficient j^2*c_root; at j=1 this is
c_root.  The root hull is the closure of the union over signed labels.  Hence
the classical q-pilot region is contained in the actual root theta hull.

No equality of log-volumes is asserted.  No fake inequality/axiom/sorry. -/

noncomputable section
open scoped BigOperators
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT.XiFPaper.QVPilotClassicalRootContainmentActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.ThetaTensorScaledImageActual
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.QPilotZeroLocusDivisorActual
open LeanFormal.IUT.XiFPaper.SignedLabelOneActual
open LeanFormal.IUT.NumberFieldFinitePlace

universe u

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable (b : Bad (nativePlaceSelection T))

noncomputable def oneSignedLabel : SignedLabel l.value :=
  ⟨1, by
    have h5 : 5 ≤ l.value := l.ge_five
    have hge : 1 ≤ lStar l.value := by
      unfold lStar
      omega
    rw [Set.mem_Icc]
    constructor
    · omega
    · exact_mod_cast hge⟩

theorem oneSignedLabel_val_local : (oneSignedLabel (l := l)).1 = 1 := rfl

/-- Classical q-pilot coefficient vector c_norm = order. -/
noncomputable def qPilotClassicalCoefficient : qVFamTensorV → Real :=
  fun _ => qVFamTensorCoefficient T b

/-- Root coefficient vector c_root = order/(2l). -/
noncomputable def qPilotRootCoefficient : qVFamTensorV → Real :=
  fun _ => ((qVFamily T b).order : Real) / (2 * l.value : Real)

/-- The root coefficient at a signed label j: j^2 * c_root. -/
noncomputable def qPilotRootLabelCoefficient
    (j : SignedLabel l.value) : qVFamTensorV → Real :=
  fun _ => ((gaussExponent j.1).toNat : Real) * qPilotRootCoefficient T b ()

/-- Coefficient inequality: c_root <= c_norm coordinatewise. -/
theorem qPilotRootCoefficient_le_classical :
    ∀ i : qVFamTensorV,
      qPilotRootCoefficient T b i ≤ qPilotClassicalCoefficient T b i := by
  intro i
  unfold qPilotRootCoefficient qPilotClassicalCoefficient qVFamTensorCoefficient
  have horder : (0 : Real) ≤ ((qVFamily T b).order : Real) := by positivity
  have hden : (1 : Real) ≤ (2 * l.value : Real) := by
    have : 0 < l.value := l.prime.pos
    exact_mod_cast (Nat.succ_le_of_lt (Nat.mul_pos (by norm_num) this))
  calc
    ((qVFamily T b).order : Real) / (2 * l.value : Real)
        ≤ ((qVFamily T b).order : Real) / 1 := by
          exact div_le_div_of_nonneg_left horder zero_lt_one hden
    _ = ((qVFamily T b).order : Real) := div_one _

/-- The classical q-pilot scaled region F(c_norm) * O_hol. -/
noncomputable def qPilotClassicalRegion : Set (qVFamTensorBlock T b) :=
  thetaTensorScaledRegion
    (places := qVFamTensorPlaces T b) (tuple := qVFamTensorTuple)
    (qPilotClassicalCoefficient T b)

/-- The root scaled region at coefficient j^2*c_root. -/
noncomputable def qPilotRootLabelRegion
    (j : SignedLabel l.value) : Set (qVFamTensorBlock T b) :=
  thetaTensorScaledRegion
    (places := qVFamTensorPlaces T b) (tuple := qVFamTensorTuple)
    (qPilotRootLabelCoefficient T b j)

/-- The root image union over signed labels. -/
noncomputable def qPilotRootImageSet : Set (qVFamTensorBlock T b) :=
  ⋃ j : SignedLabel l.value, qPilotRootLabelRegion T b j

/-- The actual root theta hull: closure of the root image union. -/
noncomputable def qPilotRootHull : Set (qVFamTensorBlock T b) :=
  closure (qPilotRootImageSet T b)

/-- The classical region is contained in the root region at j=1. -/
theorem qPilotClassicalRegion_subset_rootLabelRegion_one :
    qPilotClassicalRegion T b ⊆
      qPilotRootLabelRegion T b (oneSignedLabel (l := l)) := by
  unfold qPilotClassicalRegion qPilotRootLabelRegion thetaTensorScaledRegion
  have hcoeff : ∀ i : qVFamTensorV,
      qPilotRootLabelCoefficient T b (oneSignedLabel (l := l)) i ≤
        qPilotClassicalCoefficient T b i := by
    intro i
    simpa [qPilotRootLabelCoefficient, oneSignedLabel_val_local, gaussExponent_one_toNat,
      qPilotClassicalCoefficient, qVFamTensorCoefficient] using
      qPilotRootCoefficient_le_classical T b i
  have hF : arithmeticTupleFractionalLattice
      (qVFamTensorPlaces T b) qVFamTensorTuple
        (qPilotClassicalCoefficient T b) ≤
      arithmeticTupleFractionalLattice
        (qVFamTensorPlaces T b) qVFamTensorTuple
        (qPilotRootLabelCoefficient T b (oneSignedLabel (l := l))) :=
    arithmeticTupleFractionalLattice_mono
      (places := qVFamTensorPlaces T b) (tuple := qVFamTensorTuple)
      (a := qPilotRootLabelCoefficient T b (oneSignedLabel (l := l)))
      (b := qPilotClassicalCoefficient T b) hcoeff
  have hmul : arithmeticTupleFractionalLattice
        (qVFamTensorPlaces T b) qVFamTensorTuple
          (qPilotClassicalCoefficient T b) *
        arithmeticTupleHolomorphicLattice (qVFamTensorPlaces T b)
          qVFamTensorTuple ≤
      arithmeticTupleFractionalLattice
        (qVFamTensorPlaces T b) qVFamTensorTuple
          (qPilotRootLabelCoefficient T b (oneSignedLabel (l := l))) *
        arithmeticTupleHolomorphicLattice (qVFamTensorPlaces T b)
          qVFamTensorTuple := by
    apply Submodule.mul_le.mpr
    intro x hx y hy
    exact Submodule.mul_mem_mul (hF hx) hy
  intro z hz
  exact hmul hz

/-- The classical region is contained in the root image union. -/
theorem qPilotClassicalRegion_subset_rootImageSet :
    qPilotClassicalRegion T b ⊆ qPilotRootImageSet T b := by
  intro x hx
  unfold qPilotRootImageSet
  exact Set.mem_iUnion.mpr
    ⟨oneSignedLabel (l := l),
      qPilotClassicalRegion_subset_rootLabelRegion_one T b hx⟩

/-- The classical q-pilot region is contained in the actual root theta hull. -/
theorem qPilotClassicalRegion_subset_rootHull :
    qPilotClassicalRegion T b ⊆ qPilotRootHull T b :=
  (qPilotClassicalRegion_subset_rootImageSet T b).trans
    subset_closure

/-- Actual classical/root region and hull data. -/
structure QVPilotClassicalRootData where
  classicalCoefficient : qVFamTensorV → Real
  classicalCoefficient_eq : classicalCoefficient = qPilotClassicalCoefficient T b
  rootCoefficient : qVFamTensorV → Real
  rootCoefficient_eq : rootCoefficient = qPilotRootCoefficient T b
  classicalRegion : Set (qVFamTensorBlock T b)
  classicalRegion_eq : classicalRegion = qPilotClassicalRegion T b
  rootImageSet : Set (qVFamTensorBlock T b)
  rootImageSet_eq : rootImageSet = qPilotRootImageSet T b
  rootHull : Set (qVFamTensorBlock T b)
  rootHull_eq : rootHull = qPilotRootHull T b
  classicalRegion_subset_rootHull : classicalRegion ⊆ rootHull

/-- The actual data constructor. -/
noncomputable def qvPilotClassicalRootData : QVPilotClassicalRootData T b where
  classicalCoefficient := qPilotClassicalCoefficient T b
  classicalCoefficient_eq := rfl
  rootCoefficient := qPilotRootCoefficient T b
  rootCoefficient_eq := rfl
  classicalRegion := qPilotClassicalRegion T b
  classicalRegion_eq := rfl
  rootImageSet := qPilotRootImageSet T b
  rootImageSet_eq := rfl
  rootHull := qPilotRootHull T b
  rootHull_eq := rfl
  classicalRegion_subset_rootHull := qPilotClassicalRegion_subset_rootHull T b

end LeanFormal.IUT.XiFPaper.QVPilotClassicalRootContainmentActual

end
