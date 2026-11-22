import Mathlib.Tactic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import tmp.sheaf.xif.paper.Mzk1HT87F7F8F9InterfaceActual
import tmp.sheaf.xif.paper.Mzk1P8HeightDictionaryActual
import tmp.sheaf.xif.paper.Mzk1P8ActualDisplayHeightActual
import tmp.sheaf.xif.paper.Mzk1G1F6EtaChoiceActual
import tmp.sheaf.xif.paper.Mzk1G1D1ProducerActual
import tmp.sheaf.xif.paper.Mzk1G1JHeightUniformActual
import tmp.sheaf.xif.paper.Mzk1G1DisjointFamilyActual

/-! # P8-P assembly skeleton: (F) producer from L-H/G-K/H-T actual nodes

Route §8.6 L838-863 + §9.1 L871-882: P8-P assembles
* L-H D1 (`LocalHeightCriterion`, from `Mzk1G1D1ProducerActual.d1_of_analyticInput`)
* G-K fixed `phi_i`, `K_V`, `delta_0` (`Mzk1G1DisjointFamilyActual.hasGluedBelyiFamily_of_b1`, needs `b1FiniteProducer`)
* H-T F1-F8 (height transport/conductor/kappa/eta choice/F7/F8)
into the per-triple F9 data, then `P8UniformHeightBound` (`= ABCFreyJProductHeightCriterion`)
and finally the reverse arrow of `abcConjecture_iff_freyJProductHeightCriterion`.

`P8AssemblyInput epsilon` is the *parameterized interface*: its `perTriple` field is exactly
the shape consumed by `routeF9_of_F6_to_F8` (route L850-857). The fields are actual node
outputs, not new mathematical assumptions; this file does not claim ABC closure until they
are constructed. See the mapping/missing-declaration lists at the end of the file.
-/

noncomputable section

namespace LeanFormal.IUT.XiFPaper.P8ProducerAssemblyActual

open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.Mzk1HT87F7F8F9InterfaceActual
open LeanFormal.IUT.XiFPaper.Mzk1P8HeightDictionaryActual
open LeanFormal.IUT.XiFPaper.Mzk1P8ActualDisplayHeightActual

/-- Parameterized P8-P input at a fixed `epsilon`: the actual outputs of the L-H/G-K/H-T
nodes, already assembled into the F6/F7/F8/transport data of route L850-863.

Provenance of `perTriple` (for a fixed ABC triple, `deg = [Q(y):Q] <= n^2`):
* `hOmega` : `h_{omega_Y}(y)` (H-T F1/F4, D1 input);
* `DL` : `D(L)` (H-T §8.2 different, F7);
* `hPi` : `h(pi(y)) = n * h_{O_Y(1)}(y) + err` (F8: `F8PiActual.f8_pi_height_chart0`
  + `F8SecondActual.f8_second_equality_p1ChartHeight` + B3 O(1) bridge);
* the F6 bound `hOmega <= (1+delta) DL + C6` (HT86 + eta choice wrapper);
* the F7 bound `DL <= log rad + C7` (route L828);
* the F8 error bound `|hPi - n/(n-3) hOmega| <= C8` (route L841);
* the height transport `log c <= hPi + C9` (F9 per-triple donor `p8_perTriple_dictionary`
  together with `abcRationalPoint_logHeight₁`).
-/
structure P8AssemblyInput (epsilon : ℝ) where
  n : ℝ
  delta : ℝ
  C6 : ℝ
  C7 : ℝ
  C8 : ℝ
  C9 : ℝ
  heps : 0 < epsilon
  hdelta : delta = min 1 (epsilon / 3)
  hn : 4 ≤ n
  hdelta_n : n / (n - 3) ≤ 1 + delta
  perTriple : ∀ (a b c : ℕ), IsABCTriple a b c →
    ∃ (hOmega DL hPi : ℝ),
      0 ≤ hOmega ∧ 0 ≤ DL ∧
      hOmega ≤ (1 + delta) * DL + C6 ∧
      DL ≤ Real.log (radical (a * b * c) : ℝ) + C7 ∧
      |hPi - n / (n - 3) * hOmega| ≤ C8 ∧
      Real.log (c : ℝ) ≤ hPi + C9

/-- F9 assembly from the parameterized P8-P input (route L850-857). -/
theorem routeF9_all_of_assembly
    (H : ∀ epsilon : ℝ, 0 < epsilon → P8AssemblyInput epsilon) :
    ∀ epsilon : ℝ, 0 < epsilon → ∃ C : ℝ, RouteF9Statement epsilon C := by
  intro epsilon heps
  let D := H epsilon heps
  refine ⟨(1 + epsilon) * D.C7 + (1 + D.delta) * D.C6 + D.C8 + D.C9, ?_⟩
  exact routeF9_of_F6_to_F8 D.n epsilon D.delta D.C6 D.C7 D.C8 D.C9
    D.heps D.hdelta D.hn D.hdelta_n D.perTriple

/-- **Direct F9 ⇒ Frey j-product criterion**: the per-triple dictionary
`p8_perTriple_dictionary` transported along `abcRationalPoint_logHeight₁` gives the
height bound of `ABCFreyJProductHeightCriterion` from `RouteF9Statement`. -/
theorem freyJProductCriterion_of_routeF9
    (h : ∀ epsilon : ℝ, 0 < epsilon → ∃ C : ℝ, RouteF9Statement epsilon C) :
    ABCFreyJProductHeightCriterion := by
  intro epsilon heps
  obtain ⟨C, hC⟩ := h epsilon heps
  refine ⟨6 * C + Real.log 256, ?_⟩
  intro a b c htriple
  have hpoint : Height.logHeight₁ (abcRationalPoint a c) ≤
      (1 + epsilon) * Real.log (radical (a * b * c) : ℝ) + C := by
    rw [abcRationalPoint_logHeight₁ htriple]
    exact hC a b c htriple
  have hdict := p8_perTriple_dictionary htriple
    ((1 + epsilon) * Real.log (radical (a * b * c) : ℝ) + C) hpoint
  nlinarith [hdict.1]

/-- **P8-P producer skeleton**: parameterized assembly of `P8UniformHeightBound`.
`P8UniformHeightBound` is definitionally `ABCFreyJProductHeightCriterion`. -/
theorem p8UniformHeightBound_of_assembly
    (H : ∀ epsilon : ℝ, 0 < epsilon → P8AssemblyInput epsilon) :
    P8UniformHeightBound :=
  freyJProductCriterion_of_routeF9 (routeF9_all_of_assembly H)

/-- ABC from the P8-P assembly skeleton, via the accepted reverse arrow of
`abcConjecture_iff_freyJProductHeightCriterion`. -/
theorem abcConjecture_of_assembly
    (H : ∀ epsilon : ℝ, 0 < epsilon → P8AssemblyInput epsilon) :
    ABCConjecture :=
  (abcConjecture_iff_freyJProductHeightCriterion).mpr
    (p8UniformHeightBound_of_assembly H)

/-! ## Mapping of `P8UniformHeightBound` fields to existing interfaces

`P8UniformHeightBound = ABCFreyJProductHeightCriterion` is
`∀ epsilon > 0, ∃ bound, ∀ (a b c) (h : IsABCTriple a b c),
   logHeight₁ (Frey j) <= 6 * (1 + epsilon) * log (radical (a*b*c)) + bound`.
| Criterion ingredient | Existing/actual interface | Status |
| `log c <= (1+eps) log rad + C` | `Mzk1HT87F7F8F9InterfaceActual.RouteF9Statement` | interface; assembled here |
| `log c` vs Frey j-height | `Mzk1P8HeightDictionaryActual.p8_perTriple_dictionary` + `abcRationalPoint_logHeight₁` | DONE 2026-11-15 (three axioms) |
| F6 | `RouteF6Statement` / `Mzk1G1F6EtaChoiceActual.routeF6_of_F1_to_F5_choice` | eta choice DONE 21:48:23; F5 actual data pending |
| F7 | `RouteF7Statement` | interface, needs `D(L) <= log rad + C` actual (alan §8.2 batch) |
| F8 first | `Mzk1G1F8PiActual.f8_pi_height_chart0` | DONE 21:00:11 |
| F8 second (Cech) | `Mzk1G1F8SecondActual.f8_second_equality_p1ChartHeight` | DONE 21:23:50 |
| F8 O(1) | `Mzk1G1F8O1Actual.f8_second_equality_omegaE_frame` + `Mzk1G1F8BoundsActual` four lemmas | DONE 23:09:52 / 04:03:08; `b3_omegaE_iso` optional/pending obligation (does not block F8) |
| F4 kappa | `Mzk1HT83F4PolyActual` / `kappa_i = r_i/(n-3)` | interface, needs polynomial degree data |
| D1 (L-H) | `Mzk1G1LocalHeightCriterionActual.LocalHeightCriterion` + `Mzk1G1D1ProducerActual.d1_of_analyticInput` + `Mzk1G1JHeightUniformActual.jHeight_relation_deg` | D3/D1a/D1b(D3) DONE; D4 waiting C4 letters |
| G-K | `Mzk1G1DisjointFamilyActual.hasGluedBelyiFamily_of_b1` (needs `b1FiniteProducer` from emmy) + kurt `L_p` + grace `IsProper` for `delta_0` | MISSING `b1FiniteProducer` and `delta_0` construction |

## Missing actual declarations and wiring order
1. `Mzk1ULFtpdNumberFieldActual.numberField_FtpdLam/FmodLam` (DONE 21:14:17) -> sophie `TripodalDictionary`（fFtpd_le_conductor 的 RHS 已改 `Mzk1ULPointConductorActual.pointND`，域=ℚ(λ)） -> `SAr_tripodal`/`dMod`/`eMod` (sophie).
2. david `Mzk1UCC4PaperActual.uc_c4_actual_paper_letters` (DONE 21:25:34) + kurt `neg_MPaper_le_ksThetaHullLogRoot` + sophie `htheta`/`hstepVIII` -> D4 bridge -> `D1AnalyticInput.upper_estimate` (andrew).
3. F8 frame layer DONE (`f8_second_equality_omegaE_frame` + `F8BoundsActual` four lemmas); `b3_omegaE_iso`/`omegaEIsoUnit_eq` are optional/pending obligations (B3 second equality, does not block F8).
4. emmy `Mzk1G1PsiB1Actual.b1FiniteProducer` -> `hasGluedBelyiFamily_of_b1` -> fixed `phi_i`, `K_V`; kurt `L_p` + grace `IsProper` -> `delta_0`/compactness (route §7.2-7.3).
5. alan F1-F5 conductor/kappa/transport actuals (`Mzk1HT81Interface`, `Mzk1HT83F4PolyActual`, `Mzk1HT84F4F5InterfaceActual`) -> F5 statement -> `routeF6_of_F1_to_F5_choice` -> F6 actual.
6. F7 actual `D(L) <= log rad + C` (alan §8.2/4c) -> F7 in `P8AssemblyInput.perTriple`.
7. Assemble `P8AssemblyInput` for each `epsilon` (this file's `routeF9_all_of_assembly`) -> `P8UniformHeightBound` -> `ABCConjecture`.
-/

#print axioms routeF9_all_of_assembly
#print axioms freyJProductCriterion_of_routeF9
#print axioms p8UniformHeightBound_of_assembly
#print axioms abcConjecture_of_assembly

end LeanFormal.IUT.XiFPaper.P8ProducerAssemblyActual
end