import tmp.sheaf.xif.paper.S1720SourceArithmeticActual
import Mathlib.FieldTheory.PolynomialGaloisGroup
import Mathlib.Data.Finite.Perm
import Mathlib.GroupTheory.Index
import Mathlib.Tactic

noncomputable section
open Polynomial

namespace ProbeGroup

open LeanFormal.IUT.XiFPaper.S1720SourceArithmeticActual
open LeanFormal.IUT.XiFPaper.S1687Torsion23RealizationActual

abbrev F := S1720Field
abbrev G := F ≃ₐ[ℚ] F

example :
    Nat.card G = Nat.card (MulAction.toPermHom G (S1687P.rootSet F)).ker *
      Nat.card (MulAction.toPermHom G (S1687P.rootSet F)).range := by
  let φ := MulAction.toPermHom G (S1687P.rootSet F)
  rw [← φ.ker.card_mul_index, Subgroup.index_ker φ]

end ProbeGroup
