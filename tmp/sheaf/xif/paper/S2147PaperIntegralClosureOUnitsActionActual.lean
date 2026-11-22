import tmp.sheaf.xif.paper.S2146PaperOUnitsGaloisActionActual
import LeanFormal.IUT.ABCBridge.Geometry.FinitePlaceSourceAlgebraicClosure
import LeanFormal.IUT.Foundations.LocalFields.IntegralUnits
import LeanFormal.IUT.IUTII.Frobenioid.Example36CompletionIsometry

/-! # S2147: the integral-closure paper O^× carrier with its Galois action

S2092's `paperOUnits = (Integers (paperKv T b))^×` is the K_v-unit subgroup.  If
the paper O^× is instead the units of the integral closure in F̄_v, the actual
carrier is

  `(Integers (SourceAlgebraicClosure (sectionKPlace T b)))^×`,

and the actual local Galois group is

  `SourceAlgebraicClosure (sectionKPlace T b) ≃ₐ[NormalizedCompletion ...]
     SourceAlgebraicClosure (sectionKPlace T b)`.

The action is the genuine Galois action on the integral closure, not the trivial
action on K_v-units.  Nontriviality of this action is recorded as an exact
missing property (no witness is fabricated). -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 8000000

namespace LeanFormal.IUT.XiFPaper.S2147PaperIntegralClosureOUnitsActionActual

open LeanFormal.IUT
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.LocalFieldIntegralUnits
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.XiFPaper.S1413SourceKPlaceQComparisonActual
open LeanFormal.IUT.IUTII.Frobenioid.Example36

universe u

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable (b : Bad (nativePlaceSelection T))

/-- The actual normed algebraic closure at the paper K-place. -/
abbrev S2147PaperIntegralClosure : Type :=
  SourceAlgebraicClosure (sectionKPlace T b)

/-- The actual integral-closure O^× carrier. -/
abbrev S2147PaperIntegralClosureOUnits : Type :=
  (Integers (S2147PaperIntegralClosure T b))ˣ

/-- The actual local Galois group of the paper K-place on the normed closure. -/
abbrev S2147PaperIntegralClosureGaloisGroup : Type :=
  S2147PaperIntegralClosure T b ≃ₐ[NormalizedCompletion (sectionKPlace T b)]
    S2147PaperIntegralClosure T b

/-- Every local Galois automorphism preserves the spectral norm on the normed
algebraic closure. -/
theorem s2147_integralClosure_norm_eq
    (σ : S2147PaperIntegralClosureGaloisGroup T b)
    (x : S2147PaperIntegralClosure T b) :
    ‖σ x‖ = ‖x‖ := by
  letI := padicCompletionAlgebra (sectionKPlace T b)
  haveI : IsScalarTower (PadicScalarField (sectionKPlace T b))
      (NormalizedCompletion (sectionKPlace T b))
      (S2147PaperIntegralClosure T b) :=
    sourceAlgebraicClosureScalarTower (sectionKPlace T b)
  have hM := NormedAlgebra.norm_eq_spectralNorm
    (PadicScalarField (sectionKPlace T b))
    (L := S2147PaperIntegralClosure T b) (σ x)
  have hL := NormedAlgebra.norm_eq_spectralNorm
    (PadicScalarField (sectionKPlace T b))
    (L := S2147PaperIntegralClosure T b) x
  rw [hM, hL]
  exact spectralNorm_algHom_eq
    (K := PadicScalarField (sectionKPlace T b))
    (A := S2147PaperIntegralClosure T b)
    (B := S2147PaperIntegralClosure T b)
    (σ.toAlgHom.restrictScalars (PadicScalarField (sectionKPlace T b))) x

/-- The induced ring equivalence of the actual integral subrings. -/
noncomputable def s2147IntegersRingEquiv
    (σ : S2147PaperIntegralClosureGaloisGroup T b) :
    Integers (S2147PaperIntegralClosure T b) ≃+*
      Integers (S2147PaperIntegralClosure T b) where
  toFun x := ⟨σ (x : S2147PaperIntegralClosure T b), by
    rw [mem_integers_iff]
    rw [s2147_integralClosure_norm_eq T b σ]
    exact (mem_integers_iff _).mp x.property⟩
  invFun y := ⟨σ.symm (y : S2147PaperIntegralClosure T b), by
    rw [mem_integers_iff]
    have h := s2147_integralClosure_norm_eq T b σ
      (σ.symm (y : S2147PaperIntegralClosure T b))
    rw [σ.apply_symm_apply] at h
    rw [← h]
    exact (mem_integers_iff _).mp y.property⟩
  left_inv x := by
    apply Subtype.ext
    simp
  right_inv y := by
    apply Subtype.ext
    simp
  map_mul' x y := by
    apply Subtype.ext
    simp
  map_add' x y := by
    apply Subtype.ext
    simp

/-- The induced multiplicative equivalence of integral units. -/
noncomputable def s2147IntegralUnitsEquiv
    (σ : S2147PaperIntegralClosureGaloisGroup T b) :
    S2147PaperIntegralClosureOUnits T b ≃*
      S2147PaperIntegralClosureOUnits T b :=
  Units.mapEquiv (s2147IntegersRingEquiv T b σ).toMulEquiv

/-- The genuine Galois action on the integral-closure O^× carrier. -/
noncomputable def s2147PaperIntegralClosureOUnitsGaloisAction :
    S2147PaperIntegralClosureGaloisGroup T b →*
      MulAut (S2147PaperIntegralClosureOUnits T b) where
  toFun σ := s2147IntegralUnitsEquiv T b σ
  map_one' := by
    ext u
    rfl
  map_mul' := by
    intro σ τ
    ext u
    rfl

theorem s2147PaperIntegralClosureOUnitsGaloisAction_apply
    (σ : S2147PaperIntegralClosureGaloisGroup T b)
    (u : S2147PaperIntegralClosureOUnits T b) :
    s2147PaperIntegralClosureOUnitsGaloisAction T b σ u =
      s2147IntegralUnitsEquiv T b σ u := rfl

/-- Exact missing property: a witness that the integral-closure Galois action is
nontrivial.  No such witness is fabricated. -/
def S2147IntegralClosureNontrivialActionRequired
    (T : SourceNativeInitialThetaData.{0} l)
    (b : Bad (nativePlaceSelection T)) : Prop :=
  ∃ (σ : S2147PaperIntegralClosureGaloisGroup T b)
    (u : S2147PaperIntegralClosureOUnits T b),
      s2147PaperIntegralClosureOUnitsGaloisAction T b σ u ≠ u

#check S2147PaperIntegralClosureOUnits
#check S2147PaperIntegralClosureGaloisGroup
#check s2147_integralClosure_norm_eq
#check s2147IntegersRingEquiv
#check s2147IntegralUnitsEquiv
#check s2147PaperIntegralClosureOUnitsGaloisAction
#check S2147IntegralClosureNontrivialActionRequired

end LeanFormal.IUT.XiFPaper.S2147PaperIntegralClosureOUnitsActionActual
end
