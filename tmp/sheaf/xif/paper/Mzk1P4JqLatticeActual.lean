/- P4 route §15.2: actual J_q lattice inside the product of local completions
and its index/log compared with the GREEN S3133 scalar. -/
import tmp.sheaf.xif.paper.S3133RealifiedQPilotLogVolumeActual
import tmp.sheaf.xif.paper.Mzk1QVMultiplicityBridgeActual
import LeanFormal.IUT.Foundations.NumberField.FinitePlaces

noncomputable section
open scoped BigOperators
open LeanFormal.IUT
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.N8Closure.NativeInput
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.ArithmeticQPilotBaseChange
open LeanFormal.IUT.XiFPaper.S3133RealifiedQPilotLogVolumeActual
open LeanFormal.IUT.XiFPaper.QPilotGlobalLogVolumeFromQActual
open LeanFormal.IUT.XiFPaper.QPilotZeroLocusDivisorActual
open LeanFormal.IUT.XiFPaper.Mzk1QVMultiplicityBridgeActual

namespace LeanFormal.IUT.XiFPaper.Mzk1P4JqLatticeActual

variable {l : PrimeGeFive} (X : N8NativeInput l)
variable [Fintype (Bad (nativePlaceSelection X.S))]

/-- Product of the local completions F_b over bad places. -/
abbrev LocalCompletion (b : Bad (nativePlaceSelection X.S)) : Type :=
  IsDedekindDomain.HeightOneSpectrum.adicCompletion X.S.arithmetic.F
    (NumberFieldFinitePlace.underlyingPrime ((nativeBadLift X.S).lift b))

abbrev ProductCompletion : Type :=
  (b : Bad (nativePlaceSelection X.S)) → LocalCompletion (X := X) b

/-- Actual local integer lattice O_b. -/
def localCq (b : Bad (nativePlaceSelection X.S)) : Set (LocalCompletion (X := X) b) :=
  { x : LocalCompletion (X := X) b |
      x ∈ NumberFieldFinitePlace.CompletionIntegers ((nativeBadLift X.S).lift b) }

/-- Actual local lattice q_b O_b inside F_b. -/
def localJq (b : Bad (nativePlaceSelection X.S)) : Set (LocalCompletion (X := X) b) :=
  (fun x : LocalCompletion (X := X) b => (qVFamily X.S b).q * x) '' localCq (X := X) b

/-- Actual J_q = product of the local q_b O_b inside product of completions. -/
def Jq : Set (ProductCompletion (X := X)) :=
  Set.pi Set.univ (fun b => localJq X b)

/-- Actual C_q = product of the local integer lattices O_b. -/
def Cq : Set (ProductCompletion (X := X)) :=
  Set.pi Set.univ (fun b => localCq X b)

/-- The actual product index [C_q : J_q], read as the product of local residue
norm powers with the actual q_v multiplicity. -/
def jqIndex : Nat :=
  ∏ b : Bad (nativePlaceSelection X.S),
    (Ideal.absNorm (b.1).maximalIdeal.asIdeal) ^ qVEffectiveMultiplicity X b

/-- The log of the product index equals the GREEN S3133 realified log-volume. -/
theorem log_jqIndex_eq_qPilotRealifiedLogVolume :
    Real.log (jqIndex (X := X) : Real) = -qPilotRealifiedLogVolume X := by
  rw [qPilotRealifiedLogVolume_eq X]
  simp only [neg_neg]
  unfold jqIndex
  rw [Nat.cast_prod]
  simp only [Nat.cast_pow]
  have hne : ∀ b ∈ (Finset.univ : Finset (Bad (nativePlaceSelection X.S))),
      ((Ideal.absNorm (b.1).maximalIdeal.asIdeal : ℕ) : ℝ) ^
        qVEffectiveMultiplicity X b ≠ 0 := by
    intro b _
    exact pow_ne_zero _ (by
      have h := residueNormBase_gt_one (b.1)
      have hcast : ((Ideal.absNorm (b.1).maximalIdeal.asIdeal : ℝ)) =
          residueNormBase (b.1) := rfl
      rw [hcast]
      exact ne_of_gt (lt_trans (by norm_num) h))
  rw [Real.log_prod (s := Finset.univ)
    (f := fun b : Bad (nativePlaceSelection X.S) =>
      ((Ideal.absNorm (b.1).maximalIdeal.asIdeal : ℕ) : ℝ) ^
        qVEffectiveMultiplicity X b) hne]
  apply Finset.sum_congr rfl
  intro b _
  rw [Real.log_pow]
  rfl

/-- First intended comparison with the lattice index; the local index formula
[C_t : q_b O_b] = absNorm(base)^mult_b is the actual lattice input. -/
def JqLatticeIndexBridge : Prop :=
  jqIndex (X := X) = ∏ b : Bad (nativePlaceSelection X.S),
    (Ideal.absNorm (b.1).maximalIdeal.asIdeal) ^ qVEffectiveMultiplicity X b

/-- The bridge is definitional (same product); recorded for the consumer. -/
theorem jqLatticeIndexBridge_holds : JqLatticeIndexBridge (X := X) := rfl

#print axioms log_jqIndex_eq_qPilotRealifiedLogVolume
#print axioms jqLatticeIndexBridge_holds

end LeanFormal.IUT.XiFPaper.Mzk1P4JqLatticeActual
end
