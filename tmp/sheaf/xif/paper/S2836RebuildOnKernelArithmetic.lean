import tmp.sheaf.xif.paper.S2784KernelFieldActual
import tmp.sheaf.xif.paper.S2798StableEverywhere37Actual
import tmp.sheaf.xif.paper.S2786PlaceBlockActual
import tmp.sheaf.xif.paper.S2766MaximalSolvableTopActual
import LeanFormal.IUT.IUTI.InitialTheta.SourcePlaceSelection

noncomputable section
open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.XiFPaper.S2784KernelFieldActual
open LeanFormal.IUT.XiFPaper.S2798StableEverywhere37Actual
open LeanFormal.IUT.XiFPaper.S2786PlaceBlockActual
open LeanFormal.IUT.XiFPaper.S2786SignQuotientActual
open LeanFormal.IUT.XiFPaper.S2766MaximalSolvableTopActual
open LeanFormal.IUT.XiFPaper.S2771Gap1ClosedActual
open LeanFormal.IUT.XiFPaper.S2782Curve37a1Actual
open LeanFormal.IUT.XiFPaper.S2782Semistable37a1Actual
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.IUTII.Frobenioid.Example36
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 16000000

namespace LeanFormal.IUT.XiFPaper.S2836RebuildOnKernelArithmetic

local instance : Fact (Irreducible (Polynomial.X ^ 2 - Polynomial.C (-1) : Polynomial ℚ)) :=
  ⟨gaussianPolynomial_irreducible⟩

/-- The S2786 place selection transported to the kernel-field arithmetic. -/
noncomputable def S2836PlaceSelection : SourcePlaceSelection arithmetic37 where
  V_mod_bad := S2786VmodBad
  V_mod_bad_odd_residue_characteristic := by
    intro p hp
    exact S2786VmodBad_odd p hp
  V_mod_bad_nonempty := S2786VmodBad_nonempty

/-- The Gaussian curve of arithmetic37 is the same base-changed 37a1 curve as
E37QiPunctured. -/
theorem S2836Curve_eq :
    E37QiPunctured.curve = arithmetic37.curve.curve := by
  ext <;> simp [E37QiPunctured, E37Qi, E37, curve37Gaussian, curve37, arithmetic37,
    WeierstrassCurve.baseChange, WeierstrassCurve.map]

/-- Stable reduction everywhere transfers from E37QiPunctured to arithmetic37. -/
theorem S2836_stable :
    arithmetic37.curve.HasStableReductionEverywhere := by
  intro p
  have h := S2798_hasStableReductionEverywhere p
  unfold PuncturedEllipticCurve.HasStableReductionAt at h ⊢
  unfold PuncturedEllipticCurve.HasGoodReductionAt PuncturedEllipticCurve.HasMultiplicativeReductionAt
    at h ⊢
  simp only [NumberFieldFinitePlace.underlyingPrime] at h ⊢
  rw [S2836Curve_eq] at h
  exact h

/-- Field of moduli j = 110592/37 for the kernel-field arithmetic. -/
noncomputable def S2836FieldOfModuli :
    SourceFieldOfModuli arithmetic37 where
  jModuli := (110592 / 37 : GaussianField)
  algebraMap_jModuli := by
    change (110592 / 37 : GaussianField) = E37Qi.j
    rw [S2793FieldOfModuliQiActual.E37Qi_j]

/-- ClauseA for the kernel-field arithmetic, conditional only on S. -/
noncomputable def S2836ClauseA
    (S : SourceSignQuotientData arithmetic37) :
    SourceClauseA arithmetic37 S where
  stable_reduction_nonarchimedean := S2836_stable
  field_of_moduli := S2836FieldOfModuli
  maximal_solvable_extension := ⊤
  maximal_solvable_property := top_isFiniteSolvableGaloisSubextension
  maximal_solvable_contains := maximalSolvableContains_top

#check S2836PlaceSelection
#check S2836_stable
#check S2836FieldOfModuli
#check S2836ClauseA
#print axioms S2836PlaceSelection
#print axioms S2836ClauseA

end LeanFormal.IUT.XiFPaper.S2836RebuildOnKernelArithmetic
end
