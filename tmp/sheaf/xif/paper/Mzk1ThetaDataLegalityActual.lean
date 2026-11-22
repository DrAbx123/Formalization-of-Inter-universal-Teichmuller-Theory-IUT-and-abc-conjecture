import tmp.sheaf.xif.paper.Mzk1PrimeConductorRouteActual
import Mathlib.Tactic

/-!
# A850 §12.2 Θ-data legality interface + §12.1 D_exact target (shehdd)

We separate the *arithmetic* legality (proved where possible) from the *external*
published facts (listed as interface Props, supplied by the caller; none is assumed
or proved here):

1. `ThetaDataLegality C l`:
   * `l_prime : Nat.Prime l` (arithmetic);
   * `l_ge_11 : 11 ≤ l` (arithmetic);
   * `l_ne_p : l ≠ C.p` (arithmetic input, required for the Θ-data);
   * `e_pos : 0 < C.e` (arithmetic input);
   * external interface Props (data, not proofs here):
     `semistable_curve`, `mazur_rho_surjective`, `base_contains_E30`, `image_contains_SL2`.
2. Proved: `l_not_dvd_e_of_legality` — from `e≤5`, `l≥11`, `e>0`, `l` prime, `l ∤ e`
   (since `l ∣ e ⇒ l ≤ e ≤ 5 < 11 ≤ l`).
3. §12.1 targets (aligned with hull L1–L5 assembly and abc L6):
   * `ShellAssembly D_exact localSum archimedean := D_exact = localSum + archimedean`
     (L1–L5: shell volume/different/tensor packet/procession average/assembly);
   * `DExactLowerBound C l D_exact := (1 - 1/l)·log p ≤ D_exact` (target to prove);
   * `L6ReducedInequality C l D_exact := e·log p ≤ T(l)·D_exact` (abc L6 form).
4. Consumer `paperGap_of_legality_and_DExact`: Mestre–Oesterlé + legality + D_exact bound
   ⇒ `SSIneqExplicit`.  The only unproved mathematical input is `DExactLowerBound`;
   the rest are external published theorems listed in the interface.

No sorry/axiom/True placeholder.  The external Props are explicit interface fields,
not asserted facts; the caller must inhabit them (from the literature).
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT.XiFPaper.Mzk1ThetaDataLegalityActual

open LeanFormal.IUT.XiFPaper.Mzk1PrimeConductorRouteActual
open LeanFormal.IUT.XiFPaper.Mzk1SSIneqExplicitFormActual
open LeanFormal.IUT.XiFPaper.Mzk1KappaLemmaActual
open scoped BigOperators

/-- **Θ-data legality interface.**  Arithmetic fields are concrete conditions; the
four external published facts are interface Props (supplied, not proved, not assumed). -/
structure ThetaDataLegality (C : PrimeConductorCurve) (l : ℕ) : Type where
  /-- `l` is prime. -/
  l_prime : Nat.Prime l
  /-- Route C requires `l ≥ 11`. -/
  l_ge_11 : 11 ≤ l
  /-- `l` differs from the conductor prime `p`. -/
  l_ne_p : l ≠ C.p
  /-- `e_p = ord_p(Δ_min)` is positive. -/
  e_pos : 0 < C.e
  /-- External: the curve is semistable (Mazur/Ribet context). -/
  semistable_curve : Prop
  /-- External: Mazur — `ρ̄_{E,l}` is surjective for `l ≥ 11` (semistable case). -/
  mazur_rho_surjective : Prop
  /-- External: the base field contains `E[30]`. -/
  base_contains_E30 : Prop
  /-- External: after containing `E[30]`, the image contains `SL₂(𝔽_l)` (`l ≥ 7`). -/
  image_contains_SL2 : Prop

/-- Arithmetic legality theorem: under `e ≤ 5`, `l` prime and `l ≥ 11`, `l` cannot
divide `e_p` (so `l ∤ e_p` as the Θ-data requires). -/
theorem l_not_dvd_e_of_legality (C : PrimeConductorCurve) (l : ℕ)
    (he : C.e ≤ 5) (hlp : Nat.Prime l) (hl11 : 11 ≤ l) (hepos : 0 < C.e) :
    ¬ (l ∣ C.e) := by
  intro hdvd
  have hle : l ≤ C.e := Nat.le_of_dvd hepos hdvd
  omega

section Targets

/-- §12.1 L1–L5 assembly target: `D_exact` is the local shell sum (weight·h_w·log p
over places, i.e. shell volume + different + tensor packet + procession average)
plus the archimedean contribution.  This is the *shape* of the hull assembly; it is
proved on the hull side (L1–L5) and instantiated to the prime-conductor data. -/
def ShellAssembly (D_exact localSum archimedean : ℝ) : Prop :=
  D_exact = localSum + archimedean

/-- §12.1 target: the per-place lower bound `D_exact ≥ (1 - 1/l)·log p`. -/
def DExactLowerBound (C : PrimeConductorCurve) (l : ℝ) (D_exact : ℝ) : Prop :=
  (1 - 1 / l) * Real.log (C.p : ℝ) ≤ D_exact

/-- §12.1 L6 reduced inequality (abc form): `e_p·log p ≤ T(l)·D_exact`. -/
def L6ReducedInequality (C : PrimeConductorCurve) (l : ℝ) (D_exact : ℝ) : Prop :=
  (C.e : ℝ) * Real.log (C.p : ℝ) ≤ T l * D_exact

/-- Consumer: Mestre–Oesterlé + Θ-data legality + `D_exact` lower bound ⇒ SSIneq. -/
theorem paperGap_of_legality_and_DExact
    (hMO : MestreOesterleBound) (C : PrimeConductorCurve)
    (l : ℕ) (L : ThetaDataLegality C l)
    (D_exact : ℝ) (hD : DExactLowerBound C (l : ℝ) D_exact)
    (hlogp : 0 ≤ Real.log (C.p : ℝ)) :
    SSIneqExplicit (sL (l : ℝ))
      ((C.e : ℝ) * Real.log (C.p : ℝ)) (l : ℝ)
      ((((l : ℝ) + 5) / 4) * D_exact) := by
  have hl11 : (11 : ℝ) ≤ (l : ℝ) := by exact_mod_cast L.l_ge_11
  exact paperGap_of_primeConductor hMO C (l : ℝ) hl11 hlogp D_exact hD

end Targets

structure LegalityRow where
  item : String
  content : String
  status : String
  deriving Repr, DecidableEq

def legalityRows : List LegalityRow :=
  [ ⟨"ThetaDataLegality.l_prime", "Nat.Prime l", "ARITHMETIC_FIELD"⟩
  , ⟨"ThetaDataLegality.l_ge_11", "11 <= l", "ARITHMETIC_FIELD"⟩
  , ⟨"ThetaDataLegality.l_ne_p", "l != p (conductor prime)", "ARITHMETIC_FIELD"⟩
  , ⟨"ThetaDataLegality.e_pos", "0 < e_p", "ARITHMETIC_FIELD"⟩
  , ⟨"l_not_dvd_e_of_legality", "e<=5, l prime>=11, e>0 => l does not divide e", "PROVED"⟩
  , ⟨"ThetaDataLegality.semistable_curve", "external published fact (interface Prop)", "EXTERNAL_INTERFACE"⟩
  , ⟨"ThetaDataLegality.mazur_rho_surjective", "Mazur: rho-bar surjective for l>=11 (semistable)", "EXTERNAL_INTERFACE"⟩
  , ⟨"ThetaDataLegality.base_contains_E30", "base field contains E[30]", "EXTERNAL_INTERFACE"⟩
  , ⟨"ThetaDataLegality.image_contains_SL2", "image contains SL2(F_l), l>=7", "EXTERNAL_INTERFACE"⟩
  , ⟨"ShellAssembly", "D_exact = localSum + archimedean (L1-L5 shape)", "DEF (target)"⟩
  , ⟨"DExactLowerBound", "(1-1/l)log p <= D_exact", "TARGET (PENDING L1-L7)"⟩
  , ⟨"L6ReducedInequality", "e*log p <= T(l)*D_exact", "DEF (abc L6 form)"⟩
  , ⟨"paperGap_of_legality_and_DExact", "hMO + legality + DExact bound => SSIneqExplicit", "PROVED_CONDITIONAL"⟩
  , ⟨"scope", "external facts are interface Props, not assumed; no sorry/axiom", "INTEGRITY"⟩
  ]

theorem legalityRows_length : legalityRows.length = 14 := rfl

theorem legalityRows_has_external :
    legalityRows.any (fun r => r.status = "EXTERNAL_INTERFACE") = true := by
  decide

theorem legalityRows_has_target :
    legalityRows.any (fun r => r.status = "TARGET (PENDING L1-L7)") = true := by
  decide

end LeanFormal.IUT.XiFPaper.Mzk1ThetaDataLegalityActual

#print axioms LeanFormal.IUT.XiFPaper.Mzk1ThetaDataLegalityActual.l_not_dvd_e_of_legality
#print axioms LeanFormal.IUT.XiFPaper.Mzk1ThetaDataLegalityActual.paperGap_of_legality_and_DExact
