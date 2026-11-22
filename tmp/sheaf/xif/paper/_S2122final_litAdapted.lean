import tmp.sheaf.xif.paper.S2122SplitLemmasLitScratch

open Polynomial
local instance : Fact (Nat.Prime 29) := ⟨by norm_num⟩
noncomputable section
set_option maxRecDepth 10000
set_option maxHeartbeats 4000000

namespace S2122Mod29Split

theorem s2094_f_irreducible : Irreducible f :=
  irreducible_of_degree_ten hfmonic hfdeg hdvd_nat_lit h2_nat_lit h5_nat_lit

#print axioms s2094_f_irreducible

end S2122Mod29Split
