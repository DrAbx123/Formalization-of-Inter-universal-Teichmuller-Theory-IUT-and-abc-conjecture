import tmp.sheaf.xif.paper.S2264StripQuotientIdActual
import LeanFormal.IUT.IUTII.Frobenioid.Example36CompletionIsometry

/-! # S2268: local bridge from the Q_p model to the sectionKPlace integral closure

Generalizes the S2065/S2056 closure isometry to the paper K-place
`sectionKPlace T b`: the normed algebraic closure at that place is a Q_p-algebra
closure, so it is isometrically isomorphic to `AlgebraicClosure Q_p`.  This gives
an actual integral-units and O^×μ bridge to the S1978 local model. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 8000000

namespace LeanFormal.IUT.XiFPaper.S2268LocalBridgeActual

open LeanFormal.IUT
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.LocalFieldIntegralUnits
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.XiFPaper.S1413SourceKPlaceQComparisonActual
open LeanFormal.IUT.XiFPaper.S2147PaperIntegralClosureOUnitsActionActual
open LeanFormal.IUT.XiFPaper.S2219PaperOUnitsCarrierActual
open LeanFormal.IUT.XiFPaper.S2264StripQuotientIdActual
open LeanFormal.IUT.XiFPaper.S1978LocalFieldOCarrierActual
open LeanFormal.IUT.XiFPaper.S2034OperationKummerActual
open LeanFormal.IUT.IUTII.Frobenioid.Example36

universe u

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable (b : Bad (nativePlaceSelection T))

noncomputable def s2268p : Nat :=
  (completionRationalPrime (sectionKPlace T b)).val

theorem s2268p_prime : Nat.Prime (s2268p T b) :=
  (completionRationalPrime (sectionKPlace T b)).property

noncomputable instance s2268pFact : Fact (Nat.Prime (s2268p T b)) :=
  ⟨s2268p_prime T b⟩

noncomputable def s2268ClosureEquiv :
    SourceAlgebraicClosure (sectionKPlace T b) ≃ₐ[PadicScalarField (sectionKPlace T b)]
      AlgebraicClosure (PadicScalarField (sectionKPlace T b)) := by
  letI := padicCompletionAlgebra (sectionKPlace T b)
  haveI : Algebra.IsAlgebraic (PadicScalarField (sectionKPlace T b))
      (NormalizedCompletion (sectionKPlace T b)) :=
    Algebra.IsAlgebraic.of_finite _ _
  haveI : IsScalarTower (PadicScalarField (sectionKPlace T b))
      (NormalizedCompletion (sectionKPlace T b))
      (SourceAlgebraicClosure (sectionKPlace T b)) :=
    sourceAlgebraicClosureScalarTower (sectionKPlace T b)
  haveI : IsAlgClosure (PadicScalarField (sectionKPlace T b))
      (SourceAlgebraicClosure (sectionKPlace T b)) :=
    IsAlgClosure.ofAlgebraic (PadicScalarField (sectionKPlace T b))
      (NormalizedCompletion (sectionKPlace T b))
      (SourceAlgebraicClosure (sectionKPlace T b))
  exact IsAlgClosure.equiv (PadicScalarField (sectionKPlace T b))
    (SourceAlgebraicClosure (sectionKPlace T b))
    (AlgebraicClosure (PadicScalarField (sectionKPlace T b)))

theorem s2268ClosureEquiv_norm
    (x : SourceAlgebraicClosure (sectionKPlace T b)) :
    ‖s2268ClosureEquiv T b x‖ = ‖x‖ := by
  letI := padicCompletionAlgebra (sectionKPlace T b)
  have hM := NormedAlgebra.norm_eq_spectralNorm
    (PadicScalarField (sectionKPlace T b))
    (L := AlgebraicClosure (PadicScalarField (sectionKPlace T b)))
    (s2268ClosureEquiv T b x)
  have hL := NormedAlgebra.norm_eq_spectralNorm
    (PadicScalarField (sectionKPlace T b))
    (L := SourceAlgebraicClosure (sectionKPlace T b)) x
  rw [hM, hL]
  change spectralValue (minpoly (PadicScalarField (sectionKPlace T b))
    (s2268ClosureEquiv T b x)) =
    spectralValue (minpoly (PadicScalarField (sectionKPlace T b)) x)
  rw [minpoly.algEquiv_eq]

noncomputable def s2268IntegersEquiv :
    Integers (SourceAlgebraicClosure (sectionKPlace T b)) ≃+*
      Integers (AlgebraicClosure (PadicScalarField (sectionKPlace T b))) where
  toFun x :=
    ⟨s2268ClosureEquiv T b x, by
      rw [mem_integers_iff]
      rw [s2268ClosureEquiv_norm T b]
      exact (mem_integers_iff _).mp x.property⟩
  invFun y :=
    ⟨(s2268ClosureEquiv T b).symm y, by
      rw [mem_integers_iff]
      have h := s2268ClosureEquiv_norm T b ((s2268ClosureEquiv T b).symm y)
      rw [AlgEquiv.apply_symm_apply] at h
      rw [← h]
      exact (mem_integers_iff _).mp y.property⟩
  left_inv x := by ext; simp
  right_inv y := by ext; simp
  map_mul' x y := by ext; simp
  map_add' x y := by ext; simp

noncomputable def s2268IntegralUnitsEquiv :
    S2219PaperOUnits T b ≃* LocalOFieldUnits (s2268p T b) :=
  Units.mapEquiv (s2268IntegersEquiv T b).toMulEquiv

noncomputable def s2268MuEquiv :
    S2219PaperOUnitsMu T b ≃* TimesMuQuotient (LocalOFieldUnits (s2268p T b)) :=
  TimesMuQuotient.congr (s2268IntegralUnitsEquiv T b)

/-- The local bridge S2264 exactly when the paper place `v` has rational prime
`s2268p`. -/
noncomputable def s2268LocalBridge
    (v : LocV) (hv : v.1 = s2268p T b) :
    actualOUnitsMu v ≃* S2219PaperOUnitsMu T b := by
  cases v with
  | mk n hn =>
    subst hv
    exact (s2268MuEquiv T b).symm

/-- Exact missing: a paper place `v` whose rational prime is the contracted
prime of `sectionKPlace T b`. -/
def S2268PaperVPrimeMatchRequired
    (T : SourceNativeInitialThetaData.{0} l)
    (b : Bad (nativePlaceSelection T)) : Prop :=
  ∃ v : LocV, v.1 = s2268p T b

/-- An explicit paper place with matching rational prime closes the S2264 local bridge. -/
noncomputable def s2268S2264BridgeOfPlace
    (v : LocV) (hv : v.1 = s2268p T b) :
    S2264ActualLocalBridgeRequired T b :=
  { v := v, bridge := s2268LocalBridge T b v hv }

#check s2268S2264BridgeOfPlace
#check s2268ClosureEquiv_norm
#check s2268IntegersEquiv
#check s2268IntegralUnitsEquiv
#check s2268MuEquiv
#check s2268LocalBridge
#check S2268PaperVPrimeMatchRequired

end LeanFormal.IUT.XiFPaper.S2268LocalBridgeActual
end
