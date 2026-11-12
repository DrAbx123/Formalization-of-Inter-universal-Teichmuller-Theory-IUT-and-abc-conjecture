# S2465: four mapComp branch lemmas actual

Date: 2026-11-02. Serialized lake env lean -j1.

ACTUAL four lemmas (with S2465Map s = if s=1 then id else S2482EllipticInvolution, source composition represented as g*f because SingleObj comp is flip mul):
- S2465_comp_id_id : S2465Map (g*f) ~ S2465Map f >> S2465Map g for f=g=1;
- S2465_comp_id_nonid : same for f=1, g != 1;
- S2465_comp_nonid_id : same for f != 1, g=1;
- S2465_comp_nonid_nonid : same for f != 1, g != 1.
Proofs use explicit Bicategory.rightUnitor/leftUnitor (a:=Xf)(b:=Xf) and S2459InvolutionSquared.symm; no cat_disch.

EXIT=0, olean 132928, SHA256 1f13442d05791cf444a7ce31bdc4660b315e4779fc682d6c303ec14d41986ed5, axioms propext/Classical.choice/Quot.sound.

Next: assemble these four into mapComp of the diagram and handle the three pseudofunctor coherence fields separately (not cat_disch). No cF/cK yet; no fake.