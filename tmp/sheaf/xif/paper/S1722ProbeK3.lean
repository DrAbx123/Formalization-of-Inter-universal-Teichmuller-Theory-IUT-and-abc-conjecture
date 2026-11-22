import tmp.sheaf.xif.paper.S1720SourceArithmeticActual
import Mathlib.FieldTheory.PolynomialGaloisGroup
import Mathlib.Data.Finite.Perm
import Mathlib.Tactic

noncomputable section
open Polynomial

namespace ProbeK3

open LeanFormal.IUT.XiFPaper.S1720SourceArithmeticActual
open LeanFormal.IUT.XiFPaper.S1687Torsion23RealizationActual

abbrev F := S1720Field
abbrev G := F ≃ₐ[ℚ] F
abbrev φ : G →* Equiv.Perm (S1687P.rootSet F) := MulAction.toPermHom G (S1687P.rootSet F)
abbrev K := φ.ker

example (σ : K) (c : S1687P.rootSet F) : (σ : G) (c : F) = (c : F) := by
  have h : φ (σ : G) = 1 := σ.2
  have hc : ((σ : G) • c : S1687P.rootSet F) = c :=
    congrArg (fun f : Equiv.Perm (S1687P.rootSet F) => f c) h
  have hc' : (σ : G) • (c : F) = (c : F) := by
    rw [← Polynomial.rootSet.coe_smul (σ : G) c]
    exact congrArg Subtype.val hc
  simpa using hc'

end ProbeK3
