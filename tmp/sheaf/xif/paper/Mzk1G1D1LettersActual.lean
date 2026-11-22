import tmp.sheaf.xif.paper.Mzk1G1D1ProducerActual
import tmp.sheaf.xif.paper.Mzk1G1D4BridgeActual
import Mathlib.Tactic
/-!
# D1AnalyticInput from the actual C4/D2 letters (parameterized construction)

Route §6.4 L613-638.  `d1AnalyticInput_of_letters` packages, for a fixed degree bound `d`,
the per-`λ` C4/D2/error letters into `D1AnalyticInput D d`.

Parameter → owner/source map (all are route obligations, not new assumptions):
* `hlarge`: D4 letters — `C0` from D2 second bound (sophie), `dmod`/`emod`/`eta` from
  david `uc_c4_actual_paper_letters` (hP5/htheta/hstepVIII), `hC4` the boxed C4 with
  `Q = h = jHeight` (Lead ruling 2026-11-17), `hSD : S ≤ D + N` from david
  `hcond`/`logDiff` (tripodal dictionary route L615-621), `hlup`/`hlog` from D2;
* `hsmall`: the `jHeight < 1` branch, absorbed by the D3 dictionary constants
  (`Mzk1G1JHeightUniformActual.height_dictionary_deg`, route L634-636);
* `Cd`s equality `hCeq` fixes the constant to the explicit `d4C`.
-/
noncomputable section
universe u
namespace LeanFormal.IUT.XiFPaper.G1D1LettersActual
open LeanFormal.IUT.XiFPaper.G1D1ProducerActual
open LeanFormal.IUT.XiFPaper.G1KvCompactActual
open LeanFormal.IUT.XiFPaper.G1LocalHeightCriterionActual
open LeanFormal.IUT.XiFPaper.G1QHeightActual
open LeanFormal.IUT.XiFPaper.D4BridgeActual

structure D1LetterSource (D : KvData) (d : ℕ) where
  Cd : ℝ
  CK : ℝ
  hCd : 0 ≤ Cd
  hsmall : ∀ (K : Type u) [Field K] [NumberField K] (lam : K),
    Module.finrank ℚ K ≤ d → InKv D lam → jHeight lam < 1 →
      jHeight lam / 6 ≤
        (1 + Cd / Real.sqrt (jHeight lam)) * (discOver K + truncConductor lam)
          + Cd * Real.sqrt (jHeight lam) * Real.log (2 * Cd * jHeight lam) + CK
  hlarge : ∀ (K : Type u) [Field K] [NumberField K] (lam : K),
    Module.finrank ℚ K ≤ d → InKv D lam → 1 ≤ jHeight lam →
      ∃ (C0 dmod emod eta l S : ℝ),
        0 ≤ C0 ∧ 0 ≤ dmod ∧ 0 ≤ emod ∧ 0 ≤ eta ∧
        d4C C0 dmod emod eta = Cd ∧
        d4C C0 dmod emod eta = CK ∧
        0 < l ∧ jHeight lam ≤ l ^ 2 ∧
        l ≤ C0 * Real.sqrt (jHeight lam) * Real.log (2 * C0 * jHeight lam) ∧
        0 ≤ C0 * Real.sqrt (jHeight lam) * Real.log (2 * C0 * jHeight lam) ∧
        (1 / 6 - 2 / l ^ 2) * jHeight lam ≤ (1 + 12 * dmod / l) * S + 10 * (emod * l + eta) ∧
        0 ≤ S ∧ S ≤ discOver K + truncConductor lam

noncomputable def d1AnalyticInput_of_letters {D : KvData} {d : ℕ}
    (L : D1LetterSource D d) : D1AnalyticInput.{u} D d where
  Cd := L.Cd
  hCd := L.hCd
  CK := L.CK
  upper_estimate := by
    intro K _ _ lam hdeg hin
    rcases lt_or_ge (jHeight lam) 1 with hlt | hge
    · exact L.hsmall K lam hdeg hin hlt
    · obtain ⟨C0, dmod, emod, eta, l, S, hC0, hd, he, heta, hCeq, hCK,
        hlpos, hl2, hlup, hlog, hC4, hS0, hSD⟩ := L.hlarge K lam hdeg hin hge
      simpa only [← hCeq, ← hCK] using d4_of_c4_qscale (jHeight lam) S (discOver K) (truncConductor lam) l
        C0 dmod emod eta hge hS0 hSD hlpos hl2 hlup hlog hC4 hC0 hd he heta

#print axioms d1AnalyticInput_of_letters
end LeanFormal.IUT.XiFPaper.G1D1LettersActual
end