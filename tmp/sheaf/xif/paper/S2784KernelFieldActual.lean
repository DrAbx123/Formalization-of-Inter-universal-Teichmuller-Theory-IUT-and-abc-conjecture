import tmp.sheaf.xif.paper.S2782Semistable37a1Actual
import tmp.sheaf.xif.paper.S2771Gap1ClosedActual
import LeanFormal.IUT.IUTI.InitialTheta.ArithmeticData
import LeanFormal.IUT.IUTI.InitialTheta.ConcreteArithmeticExample
import LeanFormal.IUT.Foundations.Geometry.EllipticTorsion
import LeanFormal.IUT.IUTII.Frobenioid.Example36EllipticCurveAnabelioid

noncomputable section
open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.XiFPaper.S2782Semistable37a1Actual
open LeanFormal.IUT.XiFPaper.S2771Gap1ClosedActual
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000

local instance s2784GaussianFact :
    Fact (Irreducible (Polynomial.X ^ 2 - Polynomial.C (-1) : Polynomial ℚ)) := by
  apply Fact.mk
  apply X_pow_sub_C_irreducible_of_prime (p := 2) Nat.prime_two
  intro b hb
  have hnonneg : 0 <= b ^ 2 := sq_nonneg b
  rw [hb] at hnonneg
  exact (not_le_of_gt (neg_lt_zero.mpr zero_lt_one)) hnonneg

namespace LeanFormal.IUT.XiFPaper.S2784KernelFieldActual

instance curve37_isElliptic : curve37.IsElliptic := by
  rw [WeierstrassCurve.isElliptic_iff, curve37_delta]
  exact isUnit_iff_ne_zero.mpr (by norm_num)

/-- The rational curve 37a1, y^2 + y = x^3 - x, base-changed to Q(i). -/
def curve37Gaussian : PuncturedEllipticCurve GaussianField where
  curve := curve37.map (algebraMap ℚ GaussianField)
  isElliptic := inferInstance
  puncture := ⟨WeierstrassCurve.Projective.nonsingularLift_zero⟩

/-- The S2771 rank-two 5-torsion basis for the Gaussian curve. -/
noncomputable def basis37 :
    (Fin 2 → ZMod S2771FiveLabel.value) ≃ₗ[ZMod S2771FiveLabel.value]
      (curve37Gaussian).LTorsion S2771FiveLabel :=
  Classical.choice (S2771_rankTwoTorsionBasis curve37Gaussian)

/-- The actual 5-torsion kernel field K = E37[5]-kernel over Q(i). -/
noncomputable def K37 : IntermediateField GaussianField (AlgebraicClosure GaussianField) :=
  (curve37Gaussian).galoisLTorsionKernelField S2771FiveLabel basis37

/-- Field structure on K, as an intermediate field. -/
instance : Field K37 := inferInstance

/-- Number field structure from the actual kernel-field theorem. -/
instance : NumberField K37 :=
  (curve37Gaussian).galoisLTorsionKernelField_numberField S2771FiveLabel basis37

/-- Algebra over the base Gaussian field. -/
instance : Algebra GaussianField K37 := inferInstance

/-- Finite-dimensionality over the base. -/
instance : FiniteDimensional GaussianField K37 :=
  (curve37Gaussian).galoisLTorsionKernelField_finiteDimensional S2771FiveLabel basis37

/-- Galois property over the base. -/
instance : IsGalois GaussianField K37 :=
  (curve37Gaussian).galoisLTorsionKernelField_isGalois S2771FiveLabel basis37

/-- The theta field tower with Fmod = F = Q(i) and K = E37[5]-kernel. -/
noncomputable def tower37 :
    ThetaFieldTower S2771FiveLabel GaussianField GaussianField K37 where
  sqrtNegOne := gaussianField_sqrtNegOne
  degreePrimeToL := by
    rw [Module.finrank_self]
    exact Nat.coprime_one_left _

/-- The InitialThetaArithmeticData whose K is the actual E37[5] kernel field. -/
noncomputable def arithmetic37 : InitialThetaArithmeticData S2771FiveLabel where
  Fmod := GaussianField
  F := GaussianField
  K := K37
  tower := tower37
  curve := curve37Gaussian

#check K37
#check tower37
#check arithmetic37
#print axioms arithmetic37

end LeanFormal.IUT.XiFPaper.S2784KernelFieldActual
end
