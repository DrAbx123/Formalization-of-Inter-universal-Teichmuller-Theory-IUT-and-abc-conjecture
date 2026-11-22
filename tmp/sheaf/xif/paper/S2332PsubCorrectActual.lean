import tmp.sheaf.xif.paper.S2322NatIsoDirectActual

noncomputable section
open CategoryTheory Opposite Limits
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S2322NatIsoDirectActual
open LeanFormal.IUT.XiFPaper.S2285RMapNatActual
open LeanFormal.IUT.XiFPaper.S2278QHomNaturalityActual
open LeanFormal.IUT.XiFPaper.S2271QHomEqualizerNatActual
open LeanFormal.IUT.XiFPaper.S2267QHomEqualizerMulActionActual
open LeanFormal.IUT.XiFPaper.S1971ActionStackificationActual
open LeanFormal.IUT.XiFPaper.S2152PointwiseColimitActual
open LeanFormal.IUT.XiFPaper.S1726OrbicurveFPrimeActual
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 8000000
set_option backward.isDefEq.respectTransparency false

namespace LeanFormal.IUT.XiFPaper.S2332PsubCorrectActual

variable (S : Iut.SchemeOverField S1726K)
variable (M N : S2152Q.obj (LocallyDiscrete.mk (Opposite.op S)))

abbrev S2332Obj (T : (Over S)ᵒᵖ) : Type :=
  {g : Iut.SignGroup // S2267fPoint S M T g = S2267gPoint S N T g}

noncomputable def S2332Psub : (Over S)ᵒᵖ ⥤ Type where
  obj T := S2332Obj S M N T
  map {T₁ T₂} p := ↾ (fun h : S2332Obj S M N T₁ => by
    refine ⟨h.1, ?_⟩
    change S2267PT S M T₂ ≫ S1971SchemeAut h.1 = S2267QT S N T₂
    rw [← S2278PT_natural S M p, ← S2278QT_natural S N p]
    rw [Category.assoc]
    have hh : h.1 • S2267PT S M T₁ = S2267QT S N T₁ := by
      simpa [S2267fPoint, S2267gPoint] using h.2
    have hh' : S2267PT S M T₁ ≫ S1971SchemeAut h.1 = S2267QT S N T₁ := by
      simpa [S2267smul_eq] using hh
    rw [hh'])
  map_id T := rfl
  map_comp p q := rfl

#print axioms S2332Psub

end LeanFormal.IUT.XiFPaper.S2332PsubCorrectActual

end
