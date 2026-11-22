import tmp.sheaf.xif.paper.S2278QHomNaturalityActual
import tmp.sheaf.xif.paper.S2192QHomSheavesActual
import tmp.sheaf.xif.paper.S2271QHomEqualizerNatActual
import tmp.sheaf.xif.paper.S2206PConstantSheafActual

noncomputable section
open CategoryTheory Opposite
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S2278QHomNaturalityActual
open LeanFormal.IUT.XiFPaper.S2152PointwiseColimitActual
open LeanFormal.IUT.XiFPaper.S2192QHomSheavesActual
open LeanFormal.IUT.XiFPaper.S2271QHomEqualizerNatActual
open LeanFormal.IUT.XiFPaper.S2206PConstantSheafActual
open LeanFormal.IUT.XiFPaper.S2267QHomEqualizerMulActionActual
open LeanFormal.IUT.XiFPaper.S1726OrbicurveFPrimeActual
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 8000000
set_option backward.isDefEq.respectTransparency false

namespace LeanFormal.IUT.XiFPaper.S2285RMapNatActual

variable (S : Iut.SchemeOverField S1726K)

/-- Explicit R.map formula for the representable sheaf R. -/
theorem S2285R_map_apply
    {T₁ T₂ : (Over S)ᵒᵖ} (p : T₁ ⟶ T₂)
    (h : S2267Point S T₁) :
    (S2192R S).map p h = p.unop.left ≫ h :=
  rfl

/-- Naturality of the pointwise f map. -/
theorem S2285f_natural
    (M : S2152Q.obj (LocallyDiscrete.mk (Opposite.op S)))
    {T₁ T₂ : (Over S)ᵒᵖ} (p : T₁ ⟶ T₂) (g : Iut.SignGroup) :
    (S2192R S).map p (S2267fPoint S M T₁ g) =
      S2267fPoint S M T₂ g := by
  rw [S2285R_map_apply]
  change p.unop.left ≫ (g • S2267PT S M T₁) = g • S2267PT S M T₂
  rw [S2267smul_eq, S2267smul_eq, ← Category.assoc, S2278PT_natural]

/-- Naturality of the pointwise g map. -/
theorem S2285g_natural
    (N : S2152Q.obj (LocallyDiscrete.mk (Opposite.op S)))
    {T₁ T₂ : (Over S)ᵒᵖ} (p : T₁ ⟶ T₂) (g : Iut.SignGroup) :
    (S2192R S).map p (S2267gPoint S N T₁ g) =
      S2267gPoint S N T₂ g := by
  rw [S2285R_map_apply]
  change p.unop.left ≫ S2267QT S N T₁ = S2267QT S N T₂
  exact S2278QT_natural S N p

#print axioms S2285R_map_apply
#print axioms S2285f_natural
#print axioms S2285g_natural

noncomputable def S2285f
    (M : S2152Q.obj (LocallyDiscrete.mk (Opposite.op S))) :
    S2206P0 S ⟶ S2192R S where
  app T := ↾ (fun g : Iut.SignGroup => S2267fPoint S M T g)
  naturality {T₁ T₂} p := by
    ext g
    simpa [S2206P0] using (S2285f_natural S M p g).symm

noncomputable def S2285g
    (N : S2152Q.obj (LocallyDiscrete.mk (Opposite.op S))) :
    S2206P0 S ⟶ S2192R S where
  app T := ↾ (fun g : Iut.SignGroup => S2267gPoint S N T g)
  naturality {T₁ T₂} p := by
    ext g
    simpa [S2206P0] using (S2285g_natural S N p g).symm

end LeanFormal.IUT.XiFPaper.S2285RMapNatActual

end
