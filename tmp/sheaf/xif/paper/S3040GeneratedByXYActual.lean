import tmp.sheaf.xif.paper.S3038Classify
import tmp.sheaf.xif.paper.S2856HfYZRingActual
import tmp.sheaf.xif.paper.S2858AlphaOverActual

noncomputable section
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S3030AffineOriginClassification
open LeanFormal.IUT.XiFPaper.S3038Classify
open LeanFormal.IUT.XiFPaper.S2853E37NegationAutomorphismActual
open LeanFormal.IUT.XiFPaper.S2858AlphaOverActual
open LeanFormal.IUT.XiFPaper.S2856HfYZRingActual
open LeanFormal.IUT.XiFPaper.S2801D6FaithfulActual
open LeanFormal.IUT.XiFPaper.S2847A6ArithmeticActual
open LeanFormal.IUT.XiFPaper.S2844D6F6BaseChangeActual
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 16000000

namespace LeanFormal.IUT.XiFPaper.S3040GeneratedByXYActual

local instance : Fact (Irreducible (Polynomial.X ^ 2 - Polynomial.C (-1) : Polynomial ℚ)) :=
  ⟨gaussianPolynomial_irreducible⟩
local instance : Field K := S2847A6.fieldF
local instance : NumberField K := S2847A6.numberFieldF
local instance : DecidableEq K := Classical.decEq _

abbrev R0 : Type := S2801E37CoordinateRing K
abbrev x : R0 := S2801E37X K
abbrev y : R0 := S2801E37Y K

theorem S3040_alphaKMap (a : K) :
    S2853RingHom K (S3030KMap a) = S3030KMap a := by
  unfold S3030KMap
  simp [S2853RingHom, S2853PolyHom, S2853Subst, MvPolynomial.eval₂Hom_C]

/-- A ring hom of R0 is determined by its values on K, X, Y. -/
theorem S3040_ringHom_ext {ψ χ : R0 →+* R0}
    (hk : forall a : K, ψ (S3030KMap a) = χ (S3030KMap a))
    (hx : ψ x = χ x) (hy : ψ y = χ y) : ψ = χ := by
  apply Ideal.Quotient.ringHom_ext
  apply MvPolynomial.ringHom_ext
  · intro a
    simpa [S3030KMap] using hk a
  · intro i
    fin_cases i
    · simpa [x, S2801E37X] using hx
    · simpa [y, S2801E37Y] using hy

theorem S3040_generatedByXY
    (ψ : R0 →+* R0)
    (hk : forall a : K, ψ (S3030KMap a) = S3030KMap a)
    (hx : ψ x = x) (hy : ψ y = y) : ψ = RingHom.id R0 := by
  apply S3040_ringHom_ext
  · intro a
    rw [hk a]
    rfl
  · exact hx
  · exact hy

theorem S3040_alpha_match
    (ψ : R0 →+* R0)
    (hk : forall a : K, ψ (S3030KMap a) = S3030KMap a)
    (hx : ψ x = x) (hy : ψ y = -1 - y) :
    ψ = S2853RingHom K := by
  apply S3040_ringHom_ext
  · intro a
    rw [hk a]
    exact (S3040_alphaKMap a).symm
  · rw [hx, chartZ_X]
  · rw [hy, chartZ_Y]
    ring

theorem S3040_affineOriginClassification (hdom : IsDomain R0) :
    S3030AffineOriginClassification := by
  intro φ hk hφ2 hx
  rcases S3038_fixesY_or_alpha hdom (φ : R0 →+* R0) hx with hy | hy
  · left
    exact S3040_generatedByXY (φ : R0 →+* R0) hk hx hy
  · right
    exact S3040_alpha_match (φ : R0 →+* R0) hk hx hy

#check S3040_ringHom_ext
#check S3040_generatedByXY
#check S3040_alpha_match
#print axioms S3040_generatedByXY
#print axioms S3040_alpha_match
#print axioms S3040_affineOriginClassification

end LeanFormal.IUT.XiFPaper.S3040GeneratedByXYActual
end