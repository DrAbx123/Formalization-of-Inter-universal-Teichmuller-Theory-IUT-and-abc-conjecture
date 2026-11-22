/- SUPERSEDED. The p1Inv iso/involution facts are provided by emmy's
   `Mzk1G1PsiP1InvBoundaryActual` (DONE 04:14:29, 21 declarations, all with the axiom trio),
   in particular `p1Inv_inv : p1Inv ≫ p1Inv = 𝟙 projectiveLineGlued`, `p1Inv_apply_p1Inv`,
   `p1Inv_image_boundarySetGlued`, `p1Inv_mem_boundarySetGlued_iff`, `p1Inv_image_subset_iff`.
   The unique lemmas this file used to attempt (`chartMorphism0_X_eq_localChart0`,
   `chartMorphismInf_X_eq_localChartInf`, `localChart0/Inf_comp_p1Inv`, `chartMorphism0_comp_p1Inv`)
   are not needed by the active B1/G-C chain. Consumers should import emmy's file instead. -/
import tmp.sheaf.xif.paper.Mzk1G1PsiP1InvBoundaryActual
