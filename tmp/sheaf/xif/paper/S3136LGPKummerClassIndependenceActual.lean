import tmp.sheaf.xif.paper.S3136LGPKummerCocycleConditionActual

/-! # Stage-4 host: root-independence (coboundary form) of the q_v Kummer cocycle

Source anchors: IUT III, Prop. 3.4, (ii) (pp. 102--103); Prop. 3.7, (iii),
(iv) (pp. 109--111); standard Kummer theory (ContinuousKummerTheory).

The q_v Kummer cocycle built from a chosen 2l-th root depends on the choice only
up to a coboundary: for any other compatible root system R of the same q_v unit,
  c_R(σ) * c(σ)^{-1} = (σ • δ) * δ^{-1},      δ = R.root(2l)/root,
with δ in the actual mu_{2l} root set.  Hence the H^1 class is root-independent;
only the formal H^1 dictionary and the Brauer cup compatibility remain.

Continuity: the exact continuity statement is recorded as the Prop
lgpKummerCocycleFiberOpen (every mu_{2l}-fiber of the cocycle is open in the
Krull topology); the proof plan uses the Mathlib tools krullTopology and
stabilizer_isOpen_of_isIntegral and is NOT claimed here.

LABEL: prerequisite component only.  Consumers: lattice, qpilot M2, abc.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 1000000

namespace LeanFormal.IUT.XiFPaper.S3136LGPKummerClassIndependenceActual

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
open LeanFormal.IUT.XiFPaper.S3136LGPKummerCocycleConditionActual

variable {l : PrimeGeFive} (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]

/-- The Galois action on units is compatible with division. -/
theorem lgpGalois_smul_div (b : Bad (nativePlaceSelection T))
    (σ : Gal(AlgebraicClosure (Completion (qVPlace T b)) /
      Completion (qVPlace T b)))
    (x y : (AlgebraicClosure (Completion (qVPlace T b)))ˣ) :
    σ • (x / y) = σ • x / σ • y := by
  apply Units.ext
  simp only [AlgEquiv.smul_units_def, Units.coe_map, Units.val_div_eq_div_val]
  exact map_div₀ (σ.toAlgHom.toRingHom) _ _

/-- Generic commutative-group coboundary word identity (tool):
(a/b) * (c/d)^{-1} = (a/c) * (b/d)^{-1}. -/
theorem lgpCoboundaryWord {G : Type*} [CommGroup G] (a b c d : G) :
    (a / b) * (c / d)⁻¹ = (a / c) * (b / d)⁻¹ := by
  simp only [div_eq_mul_inv]
  simp [mul_comm, mul_assoc, mul_left_comm]

/-- Generic coboundary relation: two root-based cocycles differ by the coboundary
of the root ratio. -/
theorem lgpGalois_cocycle_coboundary_relation (b : Bad (nativePlaceSelection T))
    (σ : Gal(AlgebraicClosure (Completion (qVPlace T b)) /
      Completion (qVPlace T b)))
    (r r' : (AlgebraicClosure (Completion (qVPlace T b)))ˣ) :
    (σ • r' / r') * (σ • r / r)⁻¹ =
      (σ • (r' / r)) * (r' / r)⁻¹ := by
  rw [lgpGalois_smul_div T b σ r' r]
  exact lgpCoboundaryWord (σ • r') r' (σ • r) r

/-- Root independence in coboundary form: the cocycle of any compatible root
system differs from the actual one by the coboundary of the root ratio. -/
theorem lgpKummerCocycle_root_independent
    (b : Bad (nativePlaceSelection T))
    (R : NatRootSystem (qVAlgClosedUnit T b))
    (σ : Gal(AlgebraicClosure (Completion (qVPlace T b)) /
      Completion (qVPlace T b))) :
    (σ • R.root (2 * l.value) / R.root (2 * l.value)) *
        (lgpKummerCocycleValue T b σ)⁻¹ =
      (σ • (R.root (2 * l.value) / lgpAlgClosedTwoLthRoot T b)) *
        (R.root (2 * l.value) / lgpAlgClosedTwoLthRoot T b)⁻¹ := by
  unfold lgpKummerCocycleValue
  exact lgpGalois_cocycle_coboundary_relation T b σ
    (lgpAlgClosedTwoLthRoot T b) (R.root (2 * l.value))

/-- The root ratio lies in the actual mu_{2l} root set (the coboundary is
mu_{2l}-valued). -/
theorem lgpRootRatio_mem_mu (b : Bad (nativePlaceSelection T))
    (R : NatRootSystem (qVAlgClosedUnit T b)) :
    R.root (2 * l.value) / lgpAlgClosedTwoLthRoot T b ∈
      muTwoLAlgClosed (l := l) T b :=
  lgpAlgClosedTwoLthRoot_ratio_mem_mu T b R

/-- The exact continuity statement of the Kummer cocycle: every mu_{2l}-fiber of
the cocycle is open in the Krull topology on Gal(Omega/K).  Recorded as a Prop;
the proof plan uses Mathlib's krullTopology and stabilizer_isOpen_of_isIntegral.
NOT claimed. -/
def lgpKummerCocycleFiberOpen (b : Bad (nativePlaceSelection T)) : Prop :=
  ∀ ζ : (AlgebraicClosure (Completion (qVPlace T b)))ˣ,
    ζ ^ (2 * l.value) = 1 →
      IsOpen {σ : Gal(AlgebraicClosure (Completion (qVPlace T b)) /
          Completion (qVPlace T b)) |
        lgpKummerCocycleValue T b σ = ζ}

/-- The REDUCED exact residual after closing the cocycle condition and the
root-independence coboundary: the exact continuity Prop, the formal H^1 class
dictionary, and the Brauer H^2 cup compatibility remain. -/
structure LGPQVKummerClassResidualReduced where
  continuity : Prop
  h1ClassDictionary : Prop
  brauerCup : Prop

/-- The reduced residual is a gap (not proved). -/
def LGPQVKummerClassResidualReducedGap : Prop :=
  Nonempty LGPQVKummerClassResidualReduced

#check lgpGalois_smul_div
#check lgpGalois_cocycle_coboundary_relation
#check lgpKummerCocycle_root_independent
#check lgpRootRatio_mem_mu
#check lgpKummerCocycleFiberOpen
#check LGPQVKummerClassResidualReducedGap

end LeanFormal.IUT.XiFPaper.S3136LGPKummerClassIndependenceActual
end