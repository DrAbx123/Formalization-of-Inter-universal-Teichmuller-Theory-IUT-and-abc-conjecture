import tmp.sheaf.xif.paper.S2609SSPrimeActual
import tmp.sheaf.xif.paper.S2599TInstancesActual

noncomputable section
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

namespace LeanFormal.IUT.XiFPaper.S2610TTPrimeActual

open LeanFormal.IUT.XiFPaper.S2599TInstancesActual
open LeanFormal.IUT.XiFPaper.S2605LiftSLActual
open LeanFormal.IUT.XiFPaper.S2562HZcMonicCActual
open LeanFormal.IUT.XiFPaper.S2565ConcreteIntegralClosureCActual

abbrev M9 : Submonoid Cb := LeanFormal.IUT.XiFPaper.S2609SSPrimeActual.M
abbrev MT : Submonoid OL := Algebra.algebraMapSubmonoid OL M9
abbrev T' : Type := Localization MT

lemma hMT : Submonoid.powers (algebraMap Cb OL (Cden : Cb)) = MT := by
  ext x
  constructor
  · rintro ⟨n, rfl⟩
    refine ⟨((algebraMap ℤ Cb c) : Cb) ^ n, ?_, ?_⟩
    · exact (Submonoid.mem_powers_iff _ _).mpr ⟨n, rfl⟩
    · rw [map_pow]
      simp [c]
  · rintro ⟨y, hy, rfl⟩
    obtain ⟨n, hn⟩ := (Submonoid.mem_powers_iff y ((algebraMap ℤ Cb c) : Cb)).mp hy
    refine ⟨n, ?_⟩
    rw [← hn, map_pow]
    simp [c]

local instance : IsLocalization MT T := by
  rw [← hMT]
  exact inferInstance

noncomputable def eTT' : T ≃+* T' :=
  (IsLocalization.algEquiv MT T T').toRingEquiv

end LeanFormal.IUT.XiFPaper.S2610TTPrimeActual
end