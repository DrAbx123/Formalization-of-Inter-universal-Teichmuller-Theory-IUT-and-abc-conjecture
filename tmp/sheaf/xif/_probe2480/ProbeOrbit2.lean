import tmp.sheaf.xif.paper.S2217DedekindFrobTheoremActual
import tmp.sheaf.xif.paper.S2056Psi5RootsActual

noncomputable section
open LeanFormal.IUT.XiFPaper.S2056Psi5RootsActual
namespace ProbeOrbit2

example (σ : Equiv.Perm S2056Root) :
    (letI := Classical.decEq S2056Root; σ.cycleType) = σ.cycleType := by
  classical
  rfl

example (σ : Equiv.Perm S2056Root) :
    (letI := Classical.decEq S2056Root; Fintype.card (Function.fixedPoints σ)) =
      Fintype.card (Function.fixedPoints σ) := by
  classical
  rfl

example (σ : Equiv.Perm S2056Root) :
    (letI := Classical.decEq S2056Root;
      Multiset.replicate (Fintype.card (Function.fixedPoints σ)) (1:ℕ)) =
      Multiset.replicate (Fintype.card (Function.fixedPoints σ)) (1:ℕ) := by
  classical
  rfl

end ProbeOrbit2
end
