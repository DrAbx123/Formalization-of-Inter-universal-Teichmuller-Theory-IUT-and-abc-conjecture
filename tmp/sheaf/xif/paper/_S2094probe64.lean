import Mathlib
open Polynomial

example {K : Type*} [Field K] (g : K[X]) (hg : Irreducible g) : True := by
  haveI : Fact (Irreducible g) := ⟨hg⟩
  letI : Field (AdjoinRoot g) := AdjoinRoot.instField
  letI : Algebra K (AdjoinRoot g) := inferInstance
  let pb : PowerBasis K (AdjoinRoot g) := AdjoinRoot.powerBasis hg.ne_zero
  trivial

example {K : Type*} [Field K] (g : K[X]) (hg : Irreducible g) : True := by
  haveI : Fact (Irreducible g) := ⟨hg⟩
  letI : Algebra K (AdjoinRoot g) := inferInstance
  letI : Field (AdjoinRoot g) := AdjoinRoot.instField
  let pb : PowerBasis K (AdjoinRoot g) := AdjoinRoot.powerBasis hg.ne_zero
  trivial

example {K : Type*} [Field K] (g : K[X]) (hg : Irreducible g) : True := by
  haveI : Fact (Irreducible g) := ⟨hg⟩
  let pb : PowerBasis K (AdjoinRoot g) := AdjoinRoot.powerBasis hg.ne_zero
  haveI : Field (AdjoinRoot g) := AdjoinRoot.instField
  trivial
