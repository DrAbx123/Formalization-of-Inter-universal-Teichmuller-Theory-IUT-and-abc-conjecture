# S2449: concrete two-copy identity cover effective descent/amalgam actual

Date: 2026-11-02. Serialized lake env lean -j1.

ACTUAL:
- S2449TwoIdPresieve S := Presieve.ofArrows (fun _ : Bool => S) (fun _ => 1 S).
- S2449TwoId_mem_self : Presieve.ofArrows.mk true.
- S2449TwoId_effDescent : HasEffectiveDescentPresieve (S2029SheafPrestack K) (S2449TwoIdPresieve S), via hasEffectiveDescentPresieve_of_contains_isSplitEpi.
- S2449Amalgam D : Amalgam ... D, chosen from hasEffectiveDescent_iff_amalgam.

EXIT=0, olean 24800, SHA256 0dc4d23e12e5566552d0ff588e0d6e3bfa86a1bf7080aeb25be6ec5f0168fda4, axioms propext/Classical.choice/Quot.sound.

This is a concrete non-single-index cover, but it contains a split epimorphism (identity), so it is still within the S2134 split-epi base case, not a genuinely non-split Cech cover.

General S2445AllCechAmalgamation remains missing; no S2152QIsStack claim; no fake.