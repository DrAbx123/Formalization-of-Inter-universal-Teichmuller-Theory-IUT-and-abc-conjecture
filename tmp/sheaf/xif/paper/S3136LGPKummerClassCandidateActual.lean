import tmp.sheaf.xif.paper.S3136LGPToolReuseRootActual
import ContinuousKummerTheory.Kummer.Basic

/-! # Stage-4 host: Kummer class candidate for the q_v 2l-th root (component)

Source anchors: IUT III, Prop. 3.4, (ii) (pp. 102--103); IUT III, Prop. 3.7,
(iii), (iv) (pp. 109--111); IUT II theta values.

Using the existing ContinuousKummerTheory library (KummerTheory.Mu and the
Kummer cocycle formalism), this file builds the actual Kummer-cocycle candidate
of the q_v 2l-th root:
* lgpAlgEquiv_smul_qV: the actual q_v unit is fixed by the Galois action;
* lgpQVRatio_pow_twoL: the root ratio σ(root)/root has (2l)-th power one;
* lgpQVKummerCocycleCandidate: the Gal(Ω/K)-indexed mu_{2l}-valued cocycle
  candidate σ |-> σ(root)/root;
* LGPQVKummerClassCandidate + actual inhabitant;
* LGPQVKummerClassMissing/Gap: exact missing data (the 1-cocycle identity, the
  continuity of the cocycle, the independence of the H^1 class of the root
  choice, and the compatibility with the Brauer H^2 class via the Kummer cup
  product).

LABEL: prerequisite component only.  Consumers: lattice IUT-III theta-xmu gap;
qpilot M2; abc value-group splitting. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 1000000

namespace LeanFormal.IUT.XiFPaper.S3136LGPKummerClassCandidateActual

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

variable {l : PrimeGeFive} (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]

/-- The actual q_v unit is fixed by the Galois action (it lies in the base
completion). -/
theorem lgpAlgEquiv_smul_qV (b : Bad (nativePlaceSelection T))
    (σ : AlgebraicClosure (Completion (qVPlace T b)) ≃ₐ[Completion (qVPlace T b)]
      AlgebraicClosure (Completion (qVPlace T b))) :
    σ • qVAlgClosedUnit T b = qVAlgClosedUnit T b := by
  apply Units.ext
  change σ ((qVAlgClosedUnit T b : (AlgebraicClosure (Completion (qVPlace T b)))ˣ) :
      AlgebraicClosure (Completion (qVPlace T b))) =
    ((qVAlgClosedUnit T b : (AlgebraicClosure (Completion (qVPlace T b)))ˣ) :
      AlgebraicClosure (Completion (qVPlace T b)))
  rw [show ((qVAlgClosedUnit T b : (AlgebraicClosure (Completion (qVPlace T b)))ˣ) :
      AlgebraicClosure (Completion (qVPlace T b))) =
    algebraMap (Completion (qVPlace T b))
      (AlgebraicClosure (Completion (qVPlace T b)))
      ((qVCompletionUnit T b : (Completion (qVPlace T b))ˣ) :
        Completion (qVPlace T b)) from rfl]
  exact AlgEquiv.commutes σ _

/-- The root ratio has (2l)-th power one: it is a mu_{2l}-valued function. -/
theorem lgpQVRatio_pow_twoL (b : Bad (nativePlaceSelection T))
    (σ : AlgebraicClosure (Completion (qVPlace T b)) ≃ₐ[Completion (qVPlace T b)]
      AlgebraicClosure (Completion (qVPlace T b))) :
    (σ • lgpAlgClosedTwoLthRoot T b / lgpAlgClosedTwoLthRoot T b) ^
        (2 * l.value) = 1 := by
  have hσroot : σ • ((lgpAlgClosedTwoLthRoot T b) ^ (2 * l.value)) =
      lgpAlgClosedTwoLthRoot T b ^ (2 * l.value) := by
    rw [lgpAlgClosedTwoLthRoot_pow]
    exact lgpAlgEquiv_smul_qV T b σ
  rw [div_pow]
  have hnum : (σ • lgpAlgClosedTwoLthRoot T b) ^ (2 * l.value) =
      σ • ((lgpAlgClosedTwoLthRoot T b) ^ (2 * l.value)) := by
    rw [AlgEquiv.smul_units_def, AlgEquiv.smul_units_def]
    exact (map_pow (Units.map (σ.toAlgHom.toRingHom.toMonoidHom))
      (lgpAlgClosedTwoLthRoot T b) (2 * l.value)).symm
  rw [hnum, hσroot]
  simp
/-- The actual mu_{2l}-valued Kummer cocycle candidate of the q_v root. -/
noncomputable def lgpQVKummerCocycleCandidate
    (b : Bad (nativePlaceSelection T)) :
    (AlgebraicClosure (Completion (qVPlace T b)) ≃ₐ[Completion (qVPlace T b)]
      AlgebraicClosure (Completion (qVPlace T b))) →
      KummerTheory.Mu (2 * l.value)
        (AlgebraicClosure (Completion (qVPlace T b))) :=
  fun σ => KummerTheory.Mu.mk
    (σ • lgpAlgClosedTwoLthRoot T b / lgpAlgClosedTwoLthRoot T b)
    (lgpQVRatio_pow_twoL T b σ)

/-- Bundled Kummer class candidate of the q_v 2l-th root. -/
structure LGPQVKummerClassCandidate (b : Bad (nativePlaceSelection T)) where
  cocycle :
    (AlgebraicClosure (Completion (qVPlace T b)) ≃ₐ[Completion (qVPlace T b)]
      AlgebraicClosure (Completion (qVPlace T b))) →
      KummerTheory.Mu (2 * l.value)
        (AlgebraicClosure (Completion (qVPlace T b)))
  cocycle_eq : cocycle = lgpQVKummerCocycleCandidate T b

/-- The actual Kummer class candidate. -/
noncomputable def lgpQVKummerClassCandidate
    (b : Bad (nativePlaceSelection T)) :
    LGPQVKummerClassCandidate T b where
  cocycle := lgpQVKummerCocycleCandidate T b
  cocycle_eq := rfl

/-- Exact missing data for the paper's Kummer class of the q_v 2l-th root
(IUT III, Prop. 3.4, (ii), pp. 102--103; Prop. 3.7, (iii), (iv), pp. 109--111):
* cocycleCondition: the 1-cocycle identity for the candidate;
* continuity: continuity of the cocycle for the profinite Galois topology;
* classIndependence: independence of the H^1 class of the chosen root;
* brauerCup: compatibility with the Brauer H^2 class (Kummer cup product). -/
structure LGPQVKummerClassMissing where
  cocycleCondition : Prop
  continuity : Prop
  classIndependence : Prop
  brauerCup : Prop

/-- The exact Kummer class gap. -/
def LGPQVKummerClassGap : Prop := Nonempty LGPQVKummerClassMissing

#check lgpAlgEquiv_smul_qV
#check lgpQVRatio_pow_twoL
#check lgpQVKummerCocycleCandidate
#check lgpQVKummerClassCandidate
#check LGPQVKummerClassGap

end LeanFormal.IUT.XiFPaper.S3136LGPKummerClassCandidateActual
end