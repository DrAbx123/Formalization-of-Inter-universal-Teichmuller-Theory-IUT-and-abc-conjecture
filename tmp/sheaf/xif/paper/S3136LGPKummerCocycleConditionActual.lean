import tmp.sheaf.xif.paper.S3136LGPKummerClassCandidateActual

/-! # Stage-4 host: the Kummer cocycle condition for the q_v 2l-th root

Source anchors: IUT III, Prop. 3.4, (ii) (pp. 102--103); IUT III, Prop. 3.7,
(iii), (iv) (pp. 109--111); Kummer theory (ContinuousKummerTheory).

Closes the unit-level 1-cocycle condition of the q_v Kummer cocycle candidate:
for c(σ) = σ(root)/root (root in the algebraic closure, Galois-fixed q_v):
  c(στ) = c(σ) * (σ • c(τ)).
The proof is pure algebra from (στ) • root = σ • (τ • root), the relation
τ • root = c(τ) * root, the multiplicativity of the Galois action on units, and
commutativity of the unit group.

Consequences: lgpKummerCocycle_pow (values lie in mu_{2l}),
lgpKummerCocycleValue_eq_candidate (the packaged candidate is this cocycle),
and the reduced exact residual LGPQVKummerClassResidual with the REMAINING paper
fields only (continuity, class independence, Brauer-cup compatibility).

IMPORTANT AUDIT FLAG: the root lives in the ALGEBRAIC CLOSURE Omega, not in the
local completion field.  This cocycle is therefore NOT the normalized local
root supply of the paper; the local-root/normalization datum remains missing
(see the audit note in the ledger).

LABEL: prerequisite component only.  Consumers: lattice, qpilot M2, abc.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 1000000

namespace LeanFormal.IUT.XiFPaper.S3136LGPKummerCocycleConditionActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.TwoLthRootQVActual
open LeanFormal.IUT.XiFPaper.QPilotZeroLocusDivisorActual
open LeanFormal.IUT.N8Closure.C3Roots
open LeanFormal.IUT.XiFPaper.TwoLthRootKummerActual
open LeanFormal.IUT.XiFPaper.S3136LGPToolReuseRootActual
open LeanFormal.IUT.XiFPaper.S3136LGPKummerClassCandidateActual

variable {l : PrimeGeFive} (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]

/-- The mu_{2l}-valued Kummer cocycle value of the q_v root at a Galois element. -/
noncomputable def lgpKummerCocycleValue (b : Bad (nativePlaceSelection T))
    (σ : Gal(AlgebraicClosure (Completion (qVPlace T b)) /
      Completion (qVPlace T b))) :
    (AlgebraicClosure (Completion (qVPlace T b)))ˣ :=
  σ • lgpAlgClosedTwoLthRoot T b / lgpAlgClosedTwoLthRoot T b

/-- The packaged candidate is this cocycle. -/
theorem lgpKummerCocycleValue_eq_candidate (b : Bad (nativePlaceSelection T))
    (σ : Gal(AlgebraicClosure (Completion (qVPlace T b)) /
      Completion (qVPlace T b))) :
    KummerTheory.Mu.val (lgpQVKummerCocycleCandidate T b σ) =
      lgpKummerCocycleValue T b σ := rfl

/-- The cocycle value relation: τ(root) = c(τ) * root. -/
theorem lgpKummerCocycleValue_mul_root (b : Bad (nativePlaceSelection T))
    (τ : Gal(AlgebraicClosure (Completion (qVPlace T b)) /
      Completion (qVPlace T b))) :
    lgpKummerCocycleValue T b τ * lgpAlgClosedTwoLthRoot T b =
      τ • lgpAlgClosedTwoLthRoot T b := by
  unfold lgpKummerCocycleValue
  rw [div_mul_cancel]

/-- Multiplicativity of the Galois action on units. -/
theorem lgpGalois_smul_mul (b : Bad (nativePlaceSelection T))
    (σ : Gal(AlgebraicClosure (Completion (qVPlace T b)) /
      Completion (qVPlace T b)))
    (x y : (AlgebraicClosure (Completion (qVPlace T b)))ˣ) :
    σ • (x * y) = σ • x * σ • y := by
  apply Units.ext
  simp only [AlgEquiv.smul_units_def, Units.coe_map, Units.val_mul]
  exact map_mul (σ.toAlgHom.toRingHom) _ _

/-- The unit-level 1-cocycle condition: c(στ) = c(σ) * (σ • c(τ)). -/
theorem lgpKummerCocycle_condition (b : Bad (nativePlaceSelection T))
    (σ τ : Gal(AlgebraicClosure (Completion (qVPlace T b)) /
      Completion (qVPlace T b))) :
    lgpKummerCocycleValue T b (σ * τ) =
      lgpKummerCocycleValue T b σ * (σ • lgpKummerCocycleValue T b τ) := by
  have hτ' : τ • lgpAlgClosedTwoLthRoot T b / lgpAlgClosedTwoLthRoot T b =
      lgpKummerCocycleValue T b τ := rfl
  unfold lgpKummerCocycleValue
  rw [hτ']
  rw [mul_smul]
  rw [← lgpKummerCocycleValue_mul_root T b τ]
  rw [lgpGalois_smul_mul T b σ (lgpKummerCocycleValue T b τ) (lgpAlgClosedTwoLthRoot T b)]
  rw [mul_div_assoc]
  rw [mul_comm]

/-- The cocycle values are mu_{2l}-valued. -/
theorem lgpKummerCocycle_pow (b : Bad (nativePlaceSelection T))
    (σ : Gal(AlgebraicClosure (Completion (qVPlace T b)) /
      Completion (qVPlace T b))) :
    (lgpKummerCocycleValue T b σ) ^ (2 * l.value) = 1 := by
  unfold lgpKummerCocycleValue
  exact lgpQVRatio_pow_twoL T b σ

/-- The REDUCED exact residual of the q_v Kummer class: the cocycle condition is
now PROVED; the paper-level fields that remain are continuity, independence of
the H^1 class of the root choice, and the compatibility with the Brauer H^2
class (Kummer cup product). -/
structure LGPQVKummerClassResidual where
  continuity : Prop
  classIndependence : Prop
  brauerCup : Prop

/-- The reduced Kummer class residual is a gap (not proved). -/
def LGPQVKummerClassResidualGap : Prop := Nonempty LGPQVKummerClassResidual

#check lgpKummerCocycleValue
#check lgpKummerCocycleValue_eq_candidate
#check lgpKummerCocycleValue_mul_root
#check lgpGalois_smul_mul
#check lgpKummerCocycle_condition
#check lgpKummerCocycle_pow
#check LGPQVKummerClassResidualGap

end LeanFormal.IUT.XiFPaper.S3136LGPKummerCocycleConditionActual
end