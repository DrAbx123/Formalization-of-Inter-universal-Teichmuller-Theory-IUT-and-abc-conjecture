import tmp.sheaf.xif.paper.S2122SplitLemmasScratch

open Polynomial
set_option maxRecDepth 10000
set_option maxHeartbeats 4000000

namespace S2122Mod29Split

theorem s2094_f_irreducible : Irreducible f :=
  irreducible_of_degree_ten hfmonic hfdeg hdvd_nat h2_nat h5_nat

#print axioms s2094_f_irreducible

end S2122Mod29Split
