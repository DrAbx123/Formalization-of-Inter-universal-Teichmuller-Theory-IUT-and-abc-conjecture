import Mathlib.GroupTheory.Subgroup.Basic
import Mathlib.Algebra.Group.Hom.Basic

structure D where
  U : Type
  [cg : CommGroup U]
  rho : PUnit →* MulAut U

#check (fun (L : D) => inferInstance : CommGroup L.U)

noncomputable def useIt (L : D) : Type := TimesMuQuotient L.U

#check useIt
