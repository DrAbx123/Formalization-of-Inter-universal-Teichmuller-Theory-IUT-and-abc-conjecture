# S2440: H^1 closure and the H^2 exact missing

Date: 2026-11-03. Layer O. Consumers: S2145/S2142/S2138/S2114, S2112.

## Clean H^1 chain (all EXIT=0, axioms propext/Classical.choice/Quot.sound)

S2425H1SurjInternal.lean
  source SHA256 4edbd9167ccad5361c6f6523b0b039ee1b772091ce4383427700a05bf52ed300
  olean  162152 B SHA256 4a54430228c1165a877c8dd1252bbd5dd8f98cc89d52cb07a2fd901f19426d46
  S2425H1Surjective: forall n, Surjective (S2214H1PushforwardHom p n).

S2426H1Lim1Actual.lean (clean after fixing the finite-ML proof)
  source SHA256 2f2aca1616112ef0f84c6615386f954be3d99a00b74016172aa7190e9d186943
  olean  300664 B SHA256 8c92ef7c8bed218da22461a95b8dcf0e6ef1686f1e79688d65e0fce6854fce98
  Clean: S2426MittagLeffler_of_finite, S2426ActualMittagLeffler,
  S2426Lim1_subsingleton_of_surjective, S2426ActualH1Lim1_subsingleton.
  No sorryAx.

S2430H1FinalActual.lean
  source SHA256 2f3aac03588bddfa388290a7a72964ae8facc6b73f0d6fa3dc6852b68f1a621b
  olean  19688 B SHA256 fccc051ef57d2ee1683fe5b591009b86db9878cc4e5da0728cbc65f9add1dd8b
  S2430ActualH1TransitionSurjective, S2430ActualS2145Instance,
  S2430ActualS2142Tower, S2430ActualMittagLeffler,
  S2430ActualH1Lim1_subsingleton (lim1 H1 = 0, no hypotheses).

S2419H1SurjLimitActual.lean source a909cd78... olean 116968 B SHA 3f9d8e88...
S2420H1InstanceFiniteActual.lean source 2c2245a9... olean 28840 B SHA 42e0757d...
S2422H1MLInstanceActual.lean source 842a876e... olean 33936 B SHA bb3dd918...
All EXIT=0, same three axioms.

## H^2 exact missing (clean replacement; dirty S2427 not referenced)

S2427H2CompatCleanActual.lean
  source SHA256 1673b424faf90922f212e367c96f689bb09c1470f403400d4860f9eda366c6c9
  olean  109752 B SHA256 160ceb3a05da6077a27bf42640b563d38bad5c8ace9c3103b74897df0f057852
  EXIT=0, axioms the three standard ones.
  S2427ActualH2Comparison_surjective_iff_nonempty:
    Surjective h2Comparison_actual <-> Nonempty (CompatibleRepresentativeLift_actual),
  a clean instance of S2114's equivalence.  No representative is constructed;
  S2427H2ComparisonSurjectiveRequired / S2427CompatibleRepresentativeLiftRequired
  are the exact missing targets.

S2440H1H2IntegrationActual.lean
  source SHA256 2c7a7545a3ac944113d9fc857440e522678eebcbe81a5953a6cb90874ea30da6
  olean  79840 B SHA256 a33e145cf68ba4c279e4b9e1b2a9c2a8106e2b6deff69fe2253019834ccfe409
  EXIT=0, axioms the three standard ones.
  S2440S2145Instance, S2440MittagLeffler (= lim1 H1 = 0),
  S2440CompatibleRepresentativeLift, S2440_required_iff.

## Exact first missing

An actual inhabitant of
  S2114CompatibleRepresentativeLift (S2145Coeff p) (S2145PowMap p)
    (S2196MuActionTower p).actn (S2196MuActionTower p).compat,
i.e. a compatible choice of continuous 2-cocycle in the inverse limit over each
compatible family of level H^2 classes with the prescribed projections.
Equivalent target: Surjective (S2426ActualH2Comparison p).
No unconditional H^2 surjectivity or CoboundaryLift is claimed.

The dirty file tmp/sheaf/xif/paper/S2427H2CompatRepActual.lean (sorryAx,
EXIT=1) is excluded; only the clean file above is accepted.
