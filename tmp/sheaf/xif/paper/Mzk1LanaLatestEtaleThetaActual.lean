import tmp.sheaf.lana_latest.Iut.EtaleTheta.MonoTheta
import tmp.sheaf.lana_latest.Iut.EtaleTheta.TateElliptic
import tmp.sheaf.xif.paper.Mzk1QPilotSHEDoubleImageActual

/-! Mainline (A514-2): reference/adapter file for the LANA-latest étale-theta objects and
theorems ([EtTh] Def 2.13(ii) mono-theta environments; Tate theta-function theory) used by
Theorem 3.11's O5 (etHT / theta values / Kummer side), plus the link to our literal Theta
pilot image (`Mzk1QPilotSHEDoubleImageActual.thetaPilotImage`). -/

namespace LeanFormal.IUT.XiFPaper.Mzk1LanaLatestEtaleThetaActual

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

open scoped BigOperators

/-! ## 1. Mono-theta environment (O5 object) -/

/-- **O5 object**: a mono-theta environment ([EtTh] Definition 2.13(ii)): a topological
  group `G`, a subgroup `D` of its automorphism group containing the inner ones, and the
  theta subgroups (the `μ_N`-conjugacy class of the image of the theta section). -/
abbrev O5MonoThetaEnvironment := Iut.EtaleTheta.MonoThetaEnv

/-- The theta subgroups of a mono-theta environment. -/
def o5ThetaSubgroups (M : O5MonoThetaEnvironment) :
    Set (Subgroup M.G) :=
  M.thetaSubgroups

/-- The automorphism subgroup `D` (preimage of `D_Π ⊆ Out(Π)`). -/
def o5AutSubgroup (M : O5MonoThetaEnvironment) :
    Subgroup (MulAut M.G) :=
  M.D

/-! ## 2. Tate theta values and weight families -/

section ThetaValues

variable {K : Type*} [NormedField K] [CompleteSpace K] [IsUltrametricDist K]
variable (t : TateParameter K)

/-- **Theta multiplier** `Aθ = (q·(-1))⁻¹` of `θ(-u)` (Tate uniformisation). -/
def thetaMultiplier : Kˣ :=
  Iut.EtaleTheta.multθ t

theorem thetaMultiplier_eq : thetaMultiplier t = (t.q * (-1))⁻¹ :=
  rfl

/-- Weight families are closed under convolution powers (re-exported). -/
theorem weightFamily_cpow {k : ℕ} {A : Kˣ} {c : ℤ → K}
    (hc : t.IsWeightFamily k A c) :
    ∀ m : ℕ, t.IsWeightFamily (k * m) (A ^ m) (Iut.EtaleTheta.cpow c m) :=
  Iut.EtaleTheta.isWeightFamily_cpow t hc

/-- The convolution-power family evaluates to the power of the generating series
  (re-exported). -/
theorem tsum_weightFamily_cpow {k : ℕ} {A : Kˣ} {c : ℤ → K}
    (hc : t.IsWeightFamily k A c) (u : Kˣ) :
    ∀ m : ℕ,
      (∑' n : ℤ, Iut.EtaleTheta.cpow c m n * (u : K) ^ n) =
        (∑' n : ℤ, c n * (u : K) ^ n) ^ m :=
  Iut.EtaleTheta.tsum_cpow t hc u

/-- **Tate's theorem for theta functions** (re-exported): every weight-`k` theta family
  (`k ≥ 1`, multiplier `θ(-u)^k`) is `(P(X(u)) + Y(u)·Q(X(u)))·θ(-u)^k` off the period
  orbit. -/
theorem exists_poly_of_weightFamily (h12 : (12 : K) ≠ 0) {k : ℕ} (hk : 0 < k)
    {F : ℤ → K} (hF : t.IsWeightFamily k ((Iut.EtaleTheta.multθ t) ^ k) F) :
    ∃ P Q : Polynomial K, ∀ u : Kˣ, Iut.EtaleTheta.OffOrbit t u →
      (∑' n : ℤ, F n * (u : K) ^ n) =
        (P.eval (t.X u) + t.Y u * Q.eval (t.X u)) * t.theta (-u) ^ k :=
  Iut.EtaleTheta.exists_poly_of_isWeightFamily t h12 hk hF

end ThetaValues

/-! ## 3. Link to our literal Theta-pilot image -/

section LiteralThetaPilot

open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.Mzk1QPilotSHEDoubleImageActual

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)

/-- Our literal Theta-pilot image at the label `1` is the actual root family (a real
  theorem from the SHE double-image file, re-exported here as the O5 theta-value entry). -/
theorem literalThetaPilotImage_one (b : Bad (nativePlaceSelection T)) :
    thetaPilotImage T (oneThetaLabel l) b =
      (⟨rootNormedElement T b, rootNormedElement_mem T b⟩ :
        rootNormedExtension T b) :=
  thetaPilotImage_one_apply T b

end LiteralThetaPilot

end

end LeanFormal.IUT.XiFPaper.Mzk1LanaLatestEtaleThetaActual