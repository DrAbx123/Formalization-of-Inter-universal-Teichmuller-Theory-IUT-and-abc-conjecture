import tmp.sheaf.xif.paper.S2126Mod29IntegrationActual
import tmp.sheaf.xif.paper.S2057DedekindFrobBridgeActual

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.XiFPaper.S2132D5FactorizationActual

open Polynomial
open LeanFormal.IUT.XiFPaper.S2057DedekindFrobBridgeActual


/-- The quadratic mod-29 factor `x^2 + 6x + 12`. -/
def S2132Factor2 : (ZMod 29)[X] :=
  C (12 : ZMod 29) + C 6 * X + X ^ 2

/-- The degree-ten mod-29 factor: the actual S2126 polynomial. -/
def S2132Factor10 : (ZMod 29)[X] :=
  _root_.f

/-- S2126's `f` is the degree-ten factor. -/
theorem S2132Factor10_eq_s2126 : S2132Factor10 = _root_.f := rfl

/-- The degree-ten factor is irreducible (S2126, kernel checked). -/
theorem S2132Factor10_irreducible : Irreducible S2132Factor10 := by
  unfold S2132Factor10
  exact _root_.s2094_f_irreducible

/-- The explicit integer model of psi_5: 2^36 times the cleared-denominator
polynomial from the S1987 certificate. -/
def S2132Psi5Z : ℤ[X] :=
  C 3814697265625 + C 97656250000000 * X ^ 2 +
    C (-133437500000000) * X ^ 3 + C (-50580000000000) * X ^ 4 +
    C 165057216000000 * X ^ 5 + C 96445440000000 * X ^ 6 +
    C (-89948160000000) * X ^ 7 + C (-27525120000000) * X ^ 8 +
    C (-10234101760000) * X ^ 9 + C (-7322650804224) * X ^ 10 +
    C 1309965025280 * X ^ 11 + C 343597383680 * X ^ 12

/-- Exact remaining factorization data: the integer model maps to psi_5, and
the two explicit factors multiply to its mod-29 reduction. -/
def S2132FactorizationRequired : Prop :=
  S2132Psi5Z.map (Int.castRingHom ℚ) = S2057Psi5Q ∧
  S2132Factor2 * S2132Factor10 =
    S2132Psi5Z.map (Int.castRingHom (ZMod 29)) ∧
  Irreducible S2132Factor2 ∧
  S2132Factor2.natDegree = 2 ∧
  S2132Factor10.natDegree = 10

/-- Conditional constructor of the S2057 mod-29 data from the exact remaining
facts.  The degree-ten irreducibility is supplied by S2126. -/
noncomputable def s2132S2057Mod29Data_of
    (hmodel : S2132Psi5Z.map (Int.castRingHom ℚ) = S2057Psi5Q)
    (hprod : S2132Factor2 * S2132Factor10 =
      S2132Psi5Z.map (Int.castRingHom (ZMod 29)))
    (h2irr : Irreducible S2132Factor2)
    (h2deg : S2132Factor2.natDegree = 2)
    (h10deg : S2132Factor10.natDegree = 10) :
    S2057Mod29FactorizationData where
  integerModel := S2132Psi5Z
  integerModel_map := hmodel
  factor2 := S2132Factor2
  factor10 := S2132Factor10
  product_eq := hprod
  factor2_irreducible := h2irr
  factor10_irreducible := S2132Factor10_irreducible
  factor2_degree := h2deg
  factor10_degree := h10deg

/-- Exact first missing for S2057Mod29FactorizationData after the S2126
irreducibility input: the integer-model identification and the product
equality. -/
def S2132FirstMissing : Prop :=
  S2132FactorizationRequired

end LeanFormal.IUT.XiFPaper.S2132D5FactorizationActual

end
