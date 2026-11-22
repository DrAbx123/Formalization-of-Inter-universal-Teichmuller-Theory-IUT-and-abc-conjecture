/- U-C: sigma-free wrapper of TripodalDictionary (D1b interface).

The parent file `Mzk1ULTripodalDictionaryActual` carries the hypothesis

  variable (hσ : ∀ lam : K_V, IsAlgebraic ℚ (σ lam))

as an explicit argument, because `numberField_FtpdLam (σ lam) (hσ lam)` needs
`σ lam` to be algebraic over ℚ.  For a number field `K_V` this hypothesis is
automatic: any ring hom `K_V →+* ℂ` sends algebraic elements to algebraic
elements (the image of a root of a nonzero polynomial in ℚ[X] is a root of the
same polynomial, using that ℚ → K_V and ℚ → ℂ agree with `σ`).

This file removes the hypothesis:

* `hσ_of_algebraic` : for `[Field K_V] [NumberField K_V]`, any `σ : K_V →+* ℂ`
  and any `lam : K_V`, the value `σ lam` is algebraic over ℚ;
* `hσ_of_algebraic_all` : the same, bundled as the exact shape of `hσ`;
* `logDiff'`/`dFtpd'`/`fFtpd'` : `σ`-free versions of the three per-lambda
  objects, with the hypothesis filled by `hσ_of_algebraic_all σ`;
* `tripodalDictionaryOfConductor'` : the `TripodalDictionary` producer with no
  `hσ` argument.

Every field of the produced dictionary that depends on `hσ` is listed in the
comment of `tripodalDictionaryOfConductor'`: precisely `logDiff`, `dFtpd`,
`fFtpd` (and the proofs `dFtpd_pos`, `fFtpd_pos`, `logDiff_eq`) are built
from the `NumberField ↥(FtpdLam (σ lam))` instance, which needs
`hσ_of_algebraic σ lam`; the remaining fields (`dmod`, `eStar`, `Cd` and their
lemmas) did not use `hσ` in the parent file and still do not.

No `sorry`/`admit`/new axiom: every declaration is checked by the kernel and
`#print axioms` is recorded at the end of the file.
-/
import tmp.sheaf.xif.paper.Mzk1ULTripodalDictionaryActual
import tmp.sheaf.xif.paper.Mzk1ULPointConductorActual
import Mathlib.Tactic

noncomputable section

open scoped BigOperators

namespace LeanFormal.IUT.XiFPaper.Mzk1ULTripodalDictionarySigmaFreeActual

open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.Mzk1ULTripodalFieldActual
open LeanFormal.IUT.XiFPaper.ULTripodalNumberField
open LeanFormal.IUT.XiFPaper.Mzk1ULPaperLettersActual
open LeanFormal.IUT.XiFPaper.Mzk1ULTripodalDictionaryActual

/-- **The `hσ` hypothesis is automatic.**  For a number field `K_V`, a ring
homomorphism `σ : K_V →+* ℂ` sends every element to an algebraic complex
number: if `p : ℚ[X]` is a nonzero polynomial with `aeval lam p = 0`, then
`σ (aeval lam p) = aeval (σ lam) p`, since `σ` commutes with the two
rational structure maps `ℚ → K_V` and `ℚ → ℂ`; hence `aeval (σ lam) p = 0`. -/
theorem hσ_of_algebraic {K_V : Type*} [Field K_V] [NumberField K_V] (σ : K_V →+* ℂ)
    (lam : K_V) : IsAlgebraic ℚ (σ lam) := by
  -- `NumberField K_V` gives `FiniteDimensional ℚ K_V`, hence `Algebra.IsAlgebraic ℚ K_V`.
  have halg : Algebra.IsAlgebraic ℚ K_V := inferInstance
  obtain ⟨p, hp, hp0⟩ := halg.isAlgebraic lam
  refine ⟨p, hp, ?_⟩
  -- `σ` is compatible with the rational algebra structures.
  have hcomp : σ.comp (algebraMap ℚ K_V) = algebraMap ℚ ℂ := by
    ext q
    show σ (algebraMap ℚ K_V q) = algebraMap ℚ ℂ q
    -- both structure maps are the rational cast (the coercions `(q : ℚ)` and `q` are `rfl`-equal)
    rw [show algebraMap ℚ K_V q = (q : K_V) from map_ratCast (algebraMap ℚ K_V) q,
        show algebraMap ℚ ℂ q = (q : ℂ) from map_ratCast (algebraMap ℚ ℂ) q]
    exact map_ratCast σ q
  -- `σ` transports `aeval lam p = 0` to `aeval (σ lam) p = 0`.
  have htr : σ (Polynomial.aeval lam p) = Polynomial.aeval (σ lam) p := by
    simp only [Polynomial.aeval_def]
    rw [Polynomial.hom_eval₂ (p := p) (f := algebraMap ℚ K_V) (g := σ) (x := lam), hcomp]
  rw [← htr, hp0, map_zero]

#print axioms hσ_of_algebraic

/-- Bundled form of `hσ_of_algebraic`, with exactly the shape of the parent
file's hypothesis `(hσ : ∀ lam : K_V, IsAlgebraic ℚ (σ lam))`. -/
theorem hσ_of_algebraic_all {K_V : Type*} [Field K_V] [NumberField K_V]
    (σ : K_V →+* ℂ) : ∀ lam : K_V, IsAlgebraic ℚ (σ lam) :=
  fun lam => hσ_of_algebraic σ lam

#print axioms hσ_of_algebraic_all

/-- The parent file's `logDiff`, with `hσ` discharged by `hσ_of_algebraic_all`. -/
noncomputable def logDiff' {K_V : Type*} [Field K_V] [NumberField K_V]
    (σ : K_V →+* ℂ) (lam : K_V) : ℝ :=
  LeanFormal.IUT.XiFPaper.Mzk1ULTripodalDictionaryActual.logDiff σ (hσ_of_algebraic_all σ) lam

#print axioms logDiff'

/-- The parent file's `dFtpd`, with `hσ` discharged by `hσ_of_algebraic_all`. -/
noncomputable def dFtpd' {K_V : Type*} [Field K_V] [NumberField K_V]
    (σ : K_V →+* ℂ) (lam : K_V) : ℝ :=
  LeanFormal.IUT.XiFPaper.Mzk1ULTripodalDictionaryActual.dFtpd σ (hσ_of_algebraic_all σ) lam

#print axioms dFtpd'

/-- The parent file's `fFtpd`, with `hσ` discharged by `hσ_of_algebraic_all`. -/
noncomputable def fFtpd' {K_V : Type*} [Field K_V] [NumberField K_V]
    (σ : K_V →+* ℂ) (S_bad : Finset ℕ) (lam : K_V) : ℝ :=
  LeanFormal.IUT.XiFPaper.Mzk1ULTripodalDictionaryActual.fFtpd σ (hσ_of_algebraic_all σ) S_bad lam

#print axioms fFtpd'

/-- `logDiff' = log dFtpd'` (transported from the parent file). -/
theorem logDiff'_eq {K_V : Type*} [Field K_V] [NumberField K_V]
    (σ : K_V →+* ℂ) (lam : K_V) : logDiff' σ lam = Real.log (dFtpd' σ lam) :=
  LeanFormal.IUT.XiFPaper.Mzk1ULTripodalDictionaryActual.logDiff_eq σ (hσ_of_algebraic_all σ) lam

#print axioms logDiff'_eq

/-- `d_Ftpd > 0` (transported from the parent file). -/
theorem dFtpd'_pos {K_V : Type*} [Field K_V] [NumberField K_V]
    (σ : K_V →+* ℂ) (lam : K_V) : 0 < dFtpd' σ lam :=
  LeanFormal.IUT.XiFPaper.Mzk1ULTripodalDictionaryActual.dFtpd_pos σ (hσ_of_algebraic_all σ) lam

#print axioms dFtpd'_pos

/-- `f_Ftpd > 0` (transported from the parent file). -/
theorem fFtpd'_pos {K_V : Type*} [Field K_V] [NumberField K_V]
    (σ : K_V →+* ℂ) (S_bad : Finset ℕ) (lam : K_V) : 0 < fFtpd' σ S_bad lam :=
  LeanFormal.IUT.XiFPaper.Mzk1ULTripodalDictionaryActual.fFtpd_pos σ (hσ_of_algebraic_all σ) S_bad lam

#print axioms fFtpd'_pos

/-- **`TripodalDictionary` producer without the `hσ` hypothesis.**

This is the parent file's `tripodalDictionaryOfConductor` with the explicit
argument `(hσ : ∀ lam, IsAlgebraic ℚ (σ lam))` replaced by the discharged
`hσ_of_algebraic_all σ`.

Fields and `hσ`-usage (the parent file's `hσ` enters only through the
`NumberField ↥(FtpdLam (σ lam))` instances):

* `logDiff` := `logDiff' σ`               -- uses `hσ` (via `numberField_FtpdLam`);
* `dFtpd`   := `dFtpd' σ`                 -- uses `hσ` (via `numberField_FtpdLam`);
* `fFtpd`   := `fFtpd' σ S_bad`           -- uses `hσ` (via `numberField_FtpdLam`);
* `dmod`, `eStar`, `Cd`                    -- never used `hσ`;
* `dFtpd_pos`, `fFtpd_pos`, `logDiff_eq`    -- use `hσ`;
* `fFtpd_le_conductor` := `hcond`          -- the substantive per-place input;
* `dmod_le`, `eStar_le`                     -- do not use `hσ`. -/
noncomputable def tripodalDictionaryOfConductor' {K_V : Type*} [Field K_V] [NumberField K_V]
    (σ : K_V →+* ℂ) (S_bad : Finset ℕ) (d : ℕ) (eStar : K_V → ℝ) (Cd : ℝ)
    (heStar : ∀ lam : K_V, eStar lam ≤ Cd)
    (hcond : ∀ lam : K_V, Real.log (fFtpd' σ S_bad lam)
      ≤ LeanFormal.IUT.XiFPaper.Mzk1ULPointConductorActual.pointND (K := K_V) lam) :
    LeanFormal.IUT.XiFPaper.G1D2InterfaceActual.TripodalDictionary K_V d where
  logDiff := logDiff' σ
  dFtpd := dFtpd' σ
  fFtpd := fFtpd' σ S_bad
  dmod := d
  eStar := eStar
  Cd := Cd
  dFtpd_pos := fun lam => dFtpd'_pos σ lam
  fFtpd_pos := fun lam => fFtpd'_pos σ S_bad lam
  logDiff_eq := fun lam => logDiff'_eq σ lam
  fFtpd_le_conductor := hcond
  dmod_le := le_rfl
  eStar_le := heStar

#print axioms tripodalDictionaryOfConductor'

end LeanFormal.IUT.XiFPaper.Mzk1ULTripodalDictionarySigmaFreeActual
end