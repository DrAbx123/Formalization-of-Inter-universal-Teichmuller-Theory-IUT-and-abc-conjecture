import tmp.sheaf.xif.paper.S2180BasisCompatiblePairActual
open LeanFormal.IUT.XiFPaper.S2180BasisCompatiblePairActual
open LeanFormal.IUT.XiFPaper.S2056Psi5RootsActual
open LeanFormal.IUT.XiFPaper.S2009DicksonActual
noncomputable section
example (e : (Fin 2 → ZMod 5) ≃+ S2056Torsion) (x : S2009Pairs) (Q : S2056NonzeroTorsion) :
    Q ∈ (S2180PairMap e x).1 ↔
      ((Q : S2056Torsion) = e x.1 ∨ (Q : S2056Torsion) = -e x.1) := by
  classical
  simp only [S2180PairMap, Finset.mem_insert, Finset.mem_singleton]
  constructor
  · rintro (h | h)
    · left; exact congrArg Subtype.val h
    · right; exact congrArg Subtype.val h
  · intro h
    rcases h with h | h
    · left; exact Subtype.ext h
    · right; exact Subtype.ext h
