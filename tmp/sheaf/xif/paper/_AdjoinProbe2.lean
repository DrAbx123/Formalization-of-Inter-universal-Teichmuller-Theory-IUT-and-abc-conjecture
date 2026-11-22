import Mathlib
open Polynomial AdjoinRoot
#check @AdjoinRoot.powerBasis_dim
#check @AdjoinRoot.powerBasis_gen
#synth Fintype (AdjoinRoot (0: (ZMod 5)[X]))
#check @AdjoinRoot.fintype
