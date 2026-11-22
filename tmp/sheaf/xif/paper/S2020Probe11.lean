import Mathlib.Tactic
import Mathlib.Algebra.Field.ZMod
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Basic
import tmp.sheaf.xif.paper.S2014DicksonClassificationActual
open Matrix
namespace LeanFormal.IUT.XiFPaper.S2009DicksonActual
example (g : GL2) (h : g • (-( ![1,0] : V2)) = -( ![1,0] : V2)) : g • (![1,0] : V2) = ![1,0] := by
  have h2 : g • (-( ![1,0] : V2)) = -(g • (![1,0] : V2)) := by rw [smul_neg]
  rw [h2] at h
  exact neg_injective h
end LeanFormal.IUT.XiFPaper.S2009DicksonActual
