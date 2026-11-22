/-
Copyright (c) 2026 LeanFormal contributors. All rights reserved.
-/
import tmp.sheaf.xif.paper.S1933PrePsiSeparableActual

/-!
# S1942: the derivative/gcd certificate for prePsi_5

This file carries the S1933 pipeline from n = 3 to n = 5.  The target is the
exact input S1933Certificate 5 of S1933: an explicit Bezout identity

  A * prePsi_5 + B * (prePsi_5)' = C (c * Delta^k)

over the universal curve Z[a1,a2,a3,a4,a6], together with its consequence
(W.prePsi 5).Separable for every elliptic curve over a characteristic-zero
field.  No TauCeti, no detection, no torsion count and no cardinality argument
is used: the only inputs are the EDS recurrences of Mathlib and the polynomial
identity below.

## The computation behind the certificate

Working over Q(b2,b4,b6) with b8 eliminated by 4*b8 = b2*b6 - b4^2, the
recurrence

  prePsi_5 = prePsi_4 * Psi2Sq^2 - Psi_3^3

expresses prePsi_5 as an explicit polynomial of degree 12 in X.  The extended
Euclidean algorithm applied to (prePsi_5, prePsi_5') over Q(b2,b4,b6)[X] gives
Bezout coefficients; clearing denominators and dividing the common content
produces the small identity

  A * prePsi_5 + B * (prePsi_5)' = 5120 * Delta^5.

Concretely, with P16 = 64 * prePsi_5 and Delta_b = 4 * Delta, the integer
identity checked below is

  A * P16 + B * (P16)' = 320 * Delta_b^5.

After removing the content 20^55 * 5^11 and the seventeen powers of Delta_b,
the polynomials A and B have 218 and 249 monomials respectively.  They are
written out explicitly in the definitions S1942A and S1942B; the identity is
proved over an arbitrary characteristic-zero field by Polynomial.funext at a
generic point, elimination of b8 via S1933_b8, field_simp and ring.  The
universal certificate follows by specialising along
Z[a1..a6] -> FractionRing (MvPolynomial (Fin 5) Z) and descending along the
injective structure map, exactly as in S1933.

## Verification status

No sorry, no admit, no axiom, no opaque.  See the axiom footprint at the end.
-/

noncomputable section

set_option maxHeartbeats 4000000
set_option maxRecDepth 10000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.overlappingInstances false
set_option linter.unusedSimpArgs false

namespace LeanFormal.IUT.XiFPaper.S1942PrePsiFiveActual

open Polynomial WeierstrassCurve
open LeanFormal.IUT.XiFPaper.S1933PrePsiSeparableActual

section CommRing
variable {F : Type*} [CommRing F]

def S1942A (W : WeierstrassCurve F) : F[X] :=
  C ((73466403840 : F) * W.b₆ ^ 6 + (-55953953280 : F) * W.b₄ ^ 3 * W.b₆ ^ 4 + (-59019735040 : F) * W.b₄ ^ 6 * W.b₆ ^ 2 + (-10737418240 : F) * W.b₄ ^ 9 + (-92980016640 : F) * W.b₂ * W.b₄ * W.b₆ ^ 5 + (31415612160 : F) * W.b₂ * W.b₄ ^ 4 * W.b₆ ^ 3 + (19844577280 : F) * W.b₂ * W.b₄ ^ 7 * W.b₆ + (42381826560 : F) * W.b₂ ^ 2 * W.b₄ ^ 2 * W.b₆ ^ 4 + (2435466880 : F) * W.b₂ ^ 2 * W.b₄ ^ 5 * W.b₆ ^ 2 + (1677721600 : F) * W.b₂ ^ 2 * W.b₄ ^ 8 + (2946896640 : F) * W.b₂ ^ 3 * W.b₆ ^ 5 + (-9950508800 : F) * W.b₂ ^ 3 * W.b₄ ^ 3 * W.b₆ ^ 3 + (-3239883200 : F) * W.b₂ ^ 3 * W.b₄ ^ 6 * W.b₆ + (-2296583040 : F) * W.b₂ ^ 4 * W.b₄ * W.b₆ ^ 4 + (876880640 : F) * W.b₂ ^ 4 * W.b₄ ^ 4 * W.b₆ ^ 2 + (-104857600 : F) * W.b₂ ^ 4 * W.b₄ ^ 7 + (659813440 : F) * W.b₂ ^ 5 * W.b₄ ^ 2 * W.b₆ ^ 3 + (207692800 : F) * W.b₂ ^ 5 * W.b₄ ^ 5 * W.b₆ + (30664320 : F) * W.b₂ ^ 6 * W.b₆ ^ 4 + (-86924800 : F) * W.b₂ ^ 6 * W.b₄ ^ 3 * W.b₆ ^ 2 + (3276800 : F) * W.b₂ ^ 6 * W.b₄ ^ 6 + (-15623680 : F) * W.b₂ ^ 7 * W.b₄ * W.b₆ ^ 3 + (-6553600 : F) * W.b₂ ^ 7 * W.b₄ ^ 4 * W.b₆ + (3151360 : F) * W.b₂ ^ 8 * W.b₄ ^ 2 * W.b₆ ^ 2 + (-51200 : F) * W.b₂ ^ 8 * W.b₄ ^ 5 + (120320 : F) * W.b₂ ^ 9 * W.b₆ ^ 3 + (102400 : F) * W.b₂ ^ 9 * W.b₄ ^ 3 * W.b₆ + (-51200 : F) * W.b₂ ^ 10 * W.b₄ * W.b₆ ^ 2 + (320 : F) * W.b₂ ^ 10 * W.b₄ ^ 4 + (-640 : F) * W.b₂ ^ 11 * W.b₄ ^ 2 * W.b₆ + (320 : F) * W.b₂ ^ 12 * W.b₆ ^ 2) +
    C ((-234163353600 : F) * W.b₄ * W.b₆ ^ 5 + (-70644280320 : F) * W.b₄ ^ 4 * W.b₆ ^ 3 + (2055987200 : F) * W.b₄ ^ 7 * W.b₆ + (-80498188800 : F) * W.b₂ * W.b₄ ^ 2 * W.b₆ ^ 4 + (-107173532160 : F) * W.b₂ * W.b₄ ^ 5 * W.b₆ ^ 2 + (-16682291200 : F) * W.b₂ * W.b₄ ^ 8 + (13108262400 : F) * W.b₂ ^ 2 * W.b₆ ^ 5 + (106498744320 : F) * W.b₂ ^ 2 * W.b₄ ^ 3 * W.b₆ ^ 3 + (32018113280 : F) * W.b₂ ^ 2 * W.b₄ ^ 6 * W.b₆ + (3996633600 : F) * W.b₂ ^ 3 * W.b₄ * W.b₆ ^ 4 + (-5435447680 : F) * W.b₂ ^ 3 * W.b₄ ^ 4 * W.b₆ ^ 2 + (1908841600 : F) * W.b₂ ^ 3 * W.b₄ ^ 7 + (-8635384320 : F) * W.b₂ ^ 4 * W.b₄ ^ 2 * W.b₆ ^ 3 + (-3470208640 : F) * W.b₂ ^ 4 * W.b₄ ^ 5 * W.b₆ + (-88752000 : F) * W.b₂ ^ 5 * W.b₆ ^ 4 + (1207817600 : F) * W.b₂ ^ 5 * W.b₄ ^ 3 * W.b₆ ^ 2 + (-82688000 : F) * W.b₂ ^ 5 * W.b₄ ^ 6 + (252552320 : F) * W.b₂ ^ 6 * W.b₄ * W.b₆ ^ 3 + (140262400 : F) * W.b₂ ^ 6 * W.b₄ ^ 4 * W.b₆ + (-51985920 : F) * W.b₂ ^ 7 * W.b₄ ^ 2 * W.b₆ ^ 2 + (1638400 : F) * W.b₂ ^ 7 * W.b₄ ^ 5 + (-2629120 : F) * W.b₂ ^ 8 * W.b₆ ^ 3 + (-2549760 : F) * W.b₂ ^ 8 * W.b₄ ^ 3 * W.b₆ + (880640 : F) * W.b₂ ^ 9 * W.b₄ * W.b₆ ^ 2 + (-12800 : F) * W.b₂ ^ 9 * W.b₄ ^ 4 + (17920 : F) * W.b₂ ^ 10 * W.b₄ ^ 2 * W.b₆ + (-5120 : F) * W.b₂ ^ 11 * W.b₆ ^ 2) * X +
    C ((-1653805900800 : F) * W.b₄ ^ 2 * W.b₆ ^ 4 + (-854974033920 : F) * W.b₄ ^ 5 * W.b₆ ^ 2 + (-98037760000 : F) * W.b₄ ^ 8 + (40217472000 : F) * W.b₂ * W.b₆ ^ 5 + (814703616000 : F) * W.b₂ * W.b₄ ^ 3 * W.b₆ ^ 3 + (177066250240 : F) * W.b₂ * W.b₄ ^ 6 * W.b₆ + (56982528000 : F) * W.b₂ ^ 2 * W.b₄ * W.b₆ ^ 4 + (-46275655680 : F) * W.b₂ ^ 2 * W.b₄ ^ 4 * W.b₆ ^ 2 + (-351902720 : F) * W.b₂ ^ 2 * W.b₄ ^ 7 + (-31514572800 : F) * W.b₂ ^ 3 * W.b₄ ^ 2 * W.b₆ ^ 3 + (1898437120 : F) * W.b₂ ^ 3 * W.b₄ ^ 5 * W.b₆ + (-664243200 : F) * W.b₂ ^ 4 * W.b₆ ^ 4 + (-542520320 : F) * W.b₂ ^ 4 * W.b₄ ^ 3 * W.b₆ ^ 2 + (730096960 : F) * W.b₂ ^ 4 * W.b₄ ^ 6 + (101491200 : F) * W.b₂ ^ 5 * W.b₄ * W.b₆ ^ 3 + (-1210440000 : F) * W.b₂ ^ 5 * W.b₄ ^ 4 * W.b₆ + (385974720 : F) * W.b₂ ^ 6 * W.b₄ ^ 2 * W.b₆ ^ 2 + (-38988800 : F) * W.b₂ ^ 6 * W.b₄ ^ 5 + (78400 : F) * W.b₂ ^ 7 * W.b₆ ^ 3 + (54164480 : F) * W.b₂ ^ 7 * W.b₄ ^ 3 * W.b₆ + (-12318720 : F) * W.b₂ ^ 8 * W.b₄ * W.b₆ ^ 2 + (855040 : F) * W.b₂ ^ 8 * W.b₄ ^ 4 + (-988160 : F) * W.b₂ ^ 9 * W.b₄ ^ 2 * W.b₆ + (102400 : F) * W.b₂ ^ 10 * W.b₆ ^ 2 + (-7680 : F) * W.b₂ ^ 10 * W.b₄ ^ 3 + (7680 : F) * W.b₂ ^ 11 * W.b₄ * W.b₆) * X ^ 2 +
    C ((160869888000 : F) * W.b₆ ^ 5 + (-1151334604800 : F) * W.b₄ ^ 3 * W.b₆ ^ 3 + (-431700377600 : F) * W.b₄ ^ 6 * W.b₆ + (-512618803200 : F) * W.b₂ * W.b₄ * W.b₆ ^ 4 + (-165754736640 : F) * W.b₂ * W.b₄ ^ 4 * W.b₆ ^ 2 + (-146205081600 : F) * W.b₂ * W.b₄ ^ 7 + (588482150400 : F) * W.b₂ ^ 2 * W.b₄ ^ 2 * W.b₆ ^ 3 + (315212871680 : F) * W.b₂ ^ 2 * W.b₄ ^ 5 * W.b₆ + (8366284800 : F) * W.b₂ ^ 3 * W.b₆ ^ 4 + (-133410344960 : F) * W.b₂ ^ 3 * W.b₄ ^ 3 * W.b₆ ^ 2 + (12126069760 : F) * W.b₂ ^ 3 * W.b₄ ^ 6 + (-20751206400 : F) * W.b₂ ^ 4 * W.b₄ * W.b₆ ^ 3 + (-21768098560 : F) * W.b₂ ^ 4 * W.b₄ ^ 4 * W.b₆ + (8923855360 : F) * W.b₂ ^ 5 * W.b₄ ^ 2 * W.b₆ ^ 2 + (-282497280 : F) * W.b₂ ^ 5 * W.b₄ ^ 5 + (36025600 : F) * W.b₂ ^ 6 * W.b₆ ^ 3 + (417318400 : F) * W.b₂ ^ 6 * W.b₄ ^ 3 * W.b₆ + (-136725760 : F) * W.b₂ ^ 7 * W.b₄ * W.b₆ ^ 2 + (-1510400 : F) * W.b₂ ^ 7 * W.b₄ ^ 4 + (2165760 : F) * W.b₂ ^ 8 * W.b₄ ^ 2 * W.b₆ + (-10240 : F) * W.b₂ ^ 9 * W.b₆ ^ 2 + (174080 : F) * W.b₂ ^ 9 * W.b₄ ^ 3 + (-184320 : F) * W.b₂ ^ 10 * W.b₄ * W.b₆ + (-2560 : F) * W.b₂ ^ 11 * W.b₄ ^ 2 + (2560 : F) * W.b₂ ^ 12 * W.b₆) * X ^ 3 +
    C ((-1135681689600 : F) * W.b₄ * W.b₆ ^ 4 + (-2224266117120 : F) * W.b₄ ^ 4 * W.b₆ ^ 2 + (-654465433600 : F) * W.b₄ ^ 7 + (1642154342400 : F) * W.b₂ * W.b₄ ^ 2 * W.b₆ ^ 3 + (1077971927040 : F) * W.b₂ * W.b₄ ^ 5 * W.b₆ + (-52858137600 : F) * W.b₂ ^ 2 * W.b₆ ^ 4 + (-483724615680 : F) * W.b₂ ^ 2 * W.b₄ ^ 3 * W.b₆ ^ 2 + (10882170880 : F) * W.b₂ ^ 2 * W.b₄ ^ 6 + (61959168000 : F) * W.b₂ ^ 3 * W.b₄ * W.b₆ ^ 3 + (-611438080 : F) * W.b₂ ^ 3 * W.b₄ ^ 4 * W.b₆ + (2673262080 : F) * W.b₂ ^ 4 * W.b₄ ^ 2 * W.b₆ ^ 2 + (3067596160 : F) * W.b₂ ^ 4 * W.b₄ ^ 5 + (-4539340800 : F) * W.b₂ ^ 5 * W.b₆ ^ 3 + (-5332512000 : F) * W.b₂ ^ 5 * W.b₄ ^ 3 * W.b₆ + (1644725120 : F) * W.b₂ ^ 6 * W.b₄ * W.b₆ ^ 2 + (-176180800 : F) * W.b₂ ^ 6 * W.b₄ ^ 4 + (228241280 : F) * W.b₂ ^ 7 * W.b₄ ^ 2 * W.b₆ + (-34457920 : F) * W.b₂ ^ 8 * W.b₆ ^ 2 + (4272640 : F) * W.b₂ ^ 8 * W.b₄ ^ 3 + (-4456960 : F) * W.b₂ ^ 9 * W.b₄ * W.b₆ + (-46080 : F) * W.b₂ ^ 10 * W.b₄ ^ 2 + (46080 : F) * W.b₂ ^ 11 * W.b₆) * X ^ 4 +
    C ((2124079718400 : F) * W.b₄ ^ 2 * W.b₆ ^ 3 + (807719731200 : F) * W.b₄ ^ 5 * W.b₆ + (-480855398400 : F) * W.b₂ * W.b₆ ^ 4 + (-2130705838080 : F) * W.b₂ * W.b₄ ^ 3 * W.b₆ ^ 2 + (-432828416000 : F) * W.b₂ * W.b₄ ^ 6 + (1018394726400 : F) * W.b₂ ^ 2 * W.b₄ * W.b₆ ^ 3 + (686589880320 : F) * W.b₂ ^ 2 * W.b₄ ^ 4 * W.b₆ + (-190220451840 : F) * W.b₂ ^ 3 * W.b₄ ^ 2 * W.b₆ ^ 2 + (42262952960 : F) * W.b₂ ^ 3 * W.b₄ ^ 5 + (-42080256000 : F) * W.b₂ ^ 4 * W.b₆ ^ 3 + (-62340684800 : F) * W.b₂ ^ 4 * W.b₄ ^ 3 * W.b₆ + (19306137600 : F) * W.b₂ ^ 5 * W.b₄ * W.b₆ ^ 2 + (-1602412160 : F) * W.b₂ ^ 5 * W.b₄ ^ 4 + (1950726400 : F) * W.b₂ ^ 6 * W.b₄ ^ 2 * W.b₆ + (-332647040 : F) * W.b₂ ^ 7 * W.b₆ ^ 2 + (32386560 : F) * W.b₂ ^ 7 * W.b₄ ^ 3 + (-32540160 : F) * W.b₂ ^ 8 * W.b₄ * W.b₆ + (-325120 : F) * W.b₂ ^ 9 * W.b₄ ^ 2 + (325120 : F) * W.b₂ ^ 10 * W.b₆) * X ^ 5 +
    C ((-961710796800 : F) * W.b₆ ^ 4 + (-2137331957760 : F) * W.b₄ ^ 3 * W.b₆ ^ 2 + (-596416921600 : F) * W.b₄ ^ 6 + (4140464947200 : F) * W.b₂ * W.b₄ * W.b₆ ^ 3 + (1998988738560 : F) * W.b₂ * W.b₄ ^ 4 * W.b₆ + (-1188280903680 : F) * W.b₂ ^ 2 * W.b₄ ^ 2 * W.b₆ ^ 2 + (49612595200 : F) * W.b₂ ^ 2 * W.b₄ ^ 5 + (-166909593600 : F) * W.b₂ ^ 3 * W.b₆ ^ 3 + (-167812526080 : F) * W.b₂ ^ 3 * W.b₄ ^ 3 * W.b₆ + (87574302720 : F) * W.b₂ ^ 4 * W.b₄ * W.b₆ ^ 2 + (-1585222400 : F) * W.b₂ ^ 4 * W.b₄ ^ 4 + (5109132800 : F) * W.b₂ ^ 5 * W.b₄ ^ 2 * W.b₆ + (-1439368960 : F) * W.b₂ ^ 6 * W.b₆ ^ 2 + (35379200 : F) * W.b₂ ^ 6 * W.b₄ ^ 3 + (-92165120 : F) * W.b₂ ^ 7 * W.b₄ * W.b₆ + (-505600 : F) * W.b₂ ^ 8 * W.b₄ ^ 2 + (1079040 : F) * W.b₂ ^ 9 * W.b₆) * X ^ 6 +
    C ((5998841856000 : F) * W.b₄ * W.b₆ ^ 3 + (2205505290240 : F) * W.b₄ ^ 4 * W.b₆ + (-1441135411200 : F) * W.b₂ * W.b₄ ^ 2 * W.b₆ ^ 2 + (230025461760 : F) * W.b₂ * W.b₄ ^ 5 + (-266897203200 : F) * W.b₂ ^ 2 * W.b₆ ^ 3 + (-399774228480 : F) * W.b₂ ^ 2 * W.b₄ ^ 3 * W.b₆ + (117935308800 : F) * W.b₂ ^ 3 * W.b₄ * W.b₆ ^ 2 + (-23378964480 : F) * W.b₂ ^ 3 * W.b₄ ^ 4 + (21915371520 : F) * W.b₂ ^ 4 * W.b₄ ^ 2 * W.b₆ + (-2294323200 : F) * W.b₂ ^ 5 * W.b₆ ^ 2 + (917811200 : F) * W.b₂ ^ 5 * W.b₄ ^ 3 + (-468725760 : F) * W.b₂ ^ 6 * W.b₄ * W.b₆ + (-18104320 : F) * W.b₂ ^ 7 * W.b₄ ^ 2 + (3481600 : F) * W.b₂ ^ 8 * W.b₆ + (163840 : F) * W.b₂ ^ 9 * W.b₄) * X ^ 7 +
    C ((2337428275200 : F) * W.b₄ ^ 2 * W.b₆ ^ 2 + (896414515200 : F) * W.b₄ ^ 5 + (-50836377600 : F) * W.b₂ * W.b₆ ^ 3 + (-817137745920 : F) * W.b₂ * W.b₄ ^ 3 * W.b₆ + (-29747865600 : F) * W.b₂ ^ 2 * W.b₄ * W.b₆ ^ 2 + (-61382983680 : F) * W.b₂ ^ 2 * W.b₄ ^ 4 + (40544547840 : F) * W.b₂ ^ 3 * W.b₄ ^ 2 * W.b₆ + (-2465510400 : F) * W.b₂ ^ 4 * W.b₆ ^ 2 + (672944640 : F) * W.b₂ ^ 4 * W.b₄ ^ 3 + (113149440 : F) * W.b₂ ^ 5 * W.b₄ * W.b₆ + (36902400 : F) * W.b₂ ^ 6 * W.b₄ ^ 2 + (-16811520 : F) * W.b₂ ^ 7 * W.b₆ + (-1443840 : F) * W.b₂ ^ 8 * W.b₄ + (20480 : F) * W.b₂ ^ 10) * X ^ 8 +
    C ((-67781836800 : F) * W.b₆ ^ 3 + (-50659983360 : F) * W.b₄ ^ 3 * W.b₆ + (406209945600 : F) * W.b₂ * W.b₄ * W.b₆ ^ 2 + (152733941760 : F) * W.b₂ * W.b₄ ^ 4 + (-123422330880 : F) * W.b₂ ^ 2 * W.b₄ ^ 2 * W.b₆ + (-16454707200 : F) * W.b₂ ^ 3 * W.b₆ ^ 2 + (-14682388480 : F) * W.b₂ ^ 3 * W.b₄ ^ 3 + (8668446720 : F) * W.b₂ ^ 4 * W.b₄ * W.b₆ + (544678400 : F) * W.b₂ ^ 5 * W.b₄ ^ 2 + (-144335360 : F) * W.b₂ ^ 6 * W.b₆ + (-10936320 : F) * W.b₂ ^ 7 * W.b₄ + (112640 : F) * W.b₂ ^ 9) * X ^ 9 +
    C ((446782832640 : F) * W.b₄ * W.b₆ ^ 2 + (173148733440 : F) * W.b₄ ^ 4 + (-148927610880 : F) * W.b₂ * W.b₄ ^ 2 * W.b₆ + (-18615951360 : F) * W.b₂ ^ 2 * W.b₆ ^ 2 + (-16447488000 : F) * W.b₂ ^ 2 * W.b₄ ^ 3 + (10342195200 : F) * W.b₂ ^ 3 * W.b₄ * W.b₆ + (597043200 : F) * W.b₂ ^ 4 * W.b₄ ^ 2 + (-172369920 : F) * W.b₂ ^ 5 * W.b₆ + (-11796480 : F) * W.b₂ ^ 6 * W.b₄ + (122880 : F) * W.b₂ ^ 8) * X ^ 10

def S1942B (W : WeierstrassCurve F) : F[X] :=
  C ((29285293824 : F) * W.b₄ ^ 2 * W.b₆ ^ 5 + (18579023744 : F) * W.b₄ ^ 5 * W.b₆ ^ 3 + (2939728896 : F) * W.b₄ ^ 8 * W.b₆ + (-2219477760 : F) * W.b₂ * W.b₆ ^ 6 + (-22468759296 : F) * W.b₂ * W.b₄ ^ 3 * W.b₆ ^ 4 + (-7167506752 : F) * W.b₂ * W.b₄ ^ 6 * W.b₆ ^ 2 + (-83411456 : F) * W.b₂ * W.b₄ ^ 9 + (546369408 : F) * W.b₂ ^ 2 * W.b₄ * W.b₆ ^ 5 + (3259667648 : F) * W.b₂ ^ 2 * W.b₄ ^ 4 * W.b₆ ^ 3 + (-129172320 : F) * W.b₂ ^ 2 * W.b₄ ^ 7 * W.b₆ + (1145455168 : F) * W.b₂ ^ 3 * W.b₄ ^ 2 * W.b₆ ^ 4 + (610173728 : F) * W.b₂ ^ 3 * W.b₄ ^ 5 * W.b₆ ^ 2 + (9544208 : F) * W.b₂ ^ 3 * W.b₄ ^ 8 + (-43916736 : F) * W.b₂ ^ 4 * W.b₆ ^ 5 + (-387125536 : F) * W.b₂ ^ 4 * W.b₄ ^ 3 * W.b₆ ^ 3 + (-7755408 : F) * W.b₂ ^ 4 * W.b₄ ^ 6 * W.b₆ + (-11365536 : F) * W.b₂ ^ 5 * W.b₄ * W.b₆ ^ 4 + (-15750448 : F) * W.b₂ ^ 5 * W.b₄ ^ 4 * W.b₆ ^ 2 + (-413440 : F) * W.b₂ ^ 5 * W.b₄ ^ 7 + (13955280 : F) * W.b₂ ^ 6 * W.b₄ ^ 2 * W.b₆ ^ 3 + (620416 : F) * W.b₂ ^ 6 * W.b₄ ^ 5 * W.b₆ + (-52000 : F) * W.b₂ ^ 7 * W.b₆ ^ 4 + (22528 : F) * W.b₂ ^ 7 * W.b₄ ^ 3 * W.b₆ ^ 2 + (8192 : F) * W.b₂ ^ 7 * W.b₄ ^ 6 + (-228480 : F) * W.b₂ ^ 8 * W.b₄ * W.b₆ ^ 3 + (-14784 : F) * W.b₂ ^ 8 * W.b₄ ^ 4 * W.b₆ + (4992 : F) * W.b₂ ^ 9 * W.b₄ ^ 2 * W.b₆ ^ 2 + (-64 : F) * W.b₂ ^ 9 * W.b₄ ^ 5 + (1600 : F) * W.b₂ ^ 10 * W.b₆ ^ 3 + (128 : F) * W.b₂ ^ 10 * W.b₄ ^ 3 * W.b₆ + (-64 : F) * W.b₂ ^ 11 * W.b₄ * W.b₆ ^ 2) +
    C ((-26633733120 : F) * W.b₆ ^ 6 + (23227826688 : F) * W.b₄ ^ 3 * W.b₆ ^ 4 + (25464061440 : F) * W.b₄ ^ 6 * W.b₆ ^ 2 + (4878520320 : F) * W.b₄ ^ 9 + (45049720320 : F) * W.b₂ * W.b₄ * W.b₆ ^ 5 + (-8622932096 : F) * W.b₂ * W.b₄ ^ 4 * W.b₆ ^ 3 + (-8252331520 : F) * W.b₂ * W.b₄ ^ 7 * W.b₆ + (-20706197760 : F) * W.b₂ ^ 2 * W.b₄ ^ 2 * W.b₆ ^ 4 + (-1480780416 : F) * W.b₂ ^ 2 * W.b₄ ^ 5 * W.b₆ ^ 2 + (-665456256 : F) * W.b₂ ^ 2 * W.b₄ ^ 8 + (-1561633920 : F) * W.b₂ ^ 3 * W.b₆ ^ 5 + (3620286208 : F) * W.b₂ ^ 3 * W.b₄ ^ 3 * W.b₆ ^ 3 + (1164229088 : F) * W.b₂ ^ 3 * W.b₄ ^ 6 * W.b₆ + (1169810816 : F) * W.b₂ ^ 4 * W.b₄ * W.b₆ ^ 4 + (-216911456 : F) * W.b₂ ^ 4 * W.b₄ ^ 4 * W.b₆ ^ 2 + (36036448 : F) * W.b₂ ^ 4 * W.b₄ ^ 7 + (-247520736 : F) * W.b₂ ^ 5 * W.b₄ ^ 2 * W.b₆ ^ 3 + (-64864288 : F) * W.b₂ ^ 5 * W.b₄ ^ 5 * W.b₆ + (-15733536 : F) * W.b₂ ^ 6 * W.b₆ ^ 4 + (22622240 : F) * W.b₂ ^ 6 * W.b₄ ^ 3 * W.b₆ ^ 2 + (-965120 : F) * W.b₂ ^ 6 * W.b₄ ^ 6 + (5560480 : F) * W.b₂ ^ 7 * W.b₄ * W.b₆ ^ 3 + (1772928 : F) * W.b₂ ^ 7 * W.b₄ ^ 4 * W.b₆ + (-764160 : F) * W.b₂ ^ 8 * W.b₄ ^ 2 * W.b₆ ^ 2 + (12672 : F) * W.b₂ ^ 8 * W.b₄ ^ 5 + (-36480 : F) * W.b₂ ^ 9 * W.b₆ ^ 3 + (-23808 : F) * W.b₂ ^ 9 * W.b₄ ^ 3 * W.b₆ + (11136 : F) * W.b₂ ^ 10 * W.b₄ * W.b₆ ^ 2 + (-64 : F) * W.b₂ ^ 10 * W.b₄ ^ 4 + (128 : F) * W.b₂ ^ 11 * W.b₄ ^ 2 * W.b₆ + (-64 : F) * W.b₂ ^ 12 * W.b₆ ^ 2) * X +
    C ((110495923200 : F) * W.b₄ * W.b₆ ^ 5 + (41173714176 : F) * W.b₄ ^ 4 * W.b₆ ^ 3 + (1414133760 : F) * W.b₄ ^ 7 * W.b₆ + (11615968512 : F) * W.b₂ * W.b₄ ^ 2 * W.b₆ ^ 4 + (32754023040 : F) * W.b₂ * W.b₄ ^ 5 * W.b₆ ^ 2 + (5715534848 : F) * W.b₂ * W.b₄ ^ 8 + (-5584550400 : F) * W.b₂ ^ 2 * W.b₆ ^ 5 + (-34905503488 : F) * W.b₂ ^ 2 * W.b₄ ^ 3 * W.b₆ ^ 3 + (-10888597568 : F) * W.b₂ ^ 2 * W.b₄ ^ 6 * W.b₆ + (-438907776 : F) * W.b₂ ^ 3 * W.b₄ * W.b₆ ^ 4 + (1953032640 : F) * W.b₂ ^ 3 * W.b₄ ^ 4 * W.b₆ ^ 2 + (-632721184 : F) * W.b₂ ^ 3 * W.b₄ ^ 7 + (2684050496 : F) * W.b₂ ^ 4 * W.b₄ ^ 2 * W.b₆ ^ 3 + (1112935712 : F) * W.b₂ ^ 4 * W.b₄ ^ 5 * W.b₆ + (18498112 : F) * W.b₂ ^ 5 * W.b₆ ^ 4 + (-361984480 : F) * W.b₂ ^ 5 * W.b₄ ^ 3 * W.b₆ ^ 2 + (26518960 : F) * W.b₂ ^ 5 * W.b₄ ^ 6 + (-76914720 : F) * W.b₂ ^ 6 * W.b₄ * W.b₆ ^ 3 + (-42453264 : F) * W.b₂ ^ 6 * W.b₄ ^ 4 * W.b₆ + (13935120 : F) * W.b₂ ^ 7 * W.b₄ ^ 2 * W.b₆ ^ 2 + (-514176 : F) * W.b₂ ^ 7 * W.b₄ ^ 5 + (810320 : F) * W.b₂ ^ 8 * W.b₆ ^ 3 + (731904 : F) * W.b₂ ^ 8 * W.b₄ ^ 3 * W.b₆ + (-205440 : F) * W.b₂ ^ 9 * W.b₄ * W.b₆ ^ 2 + (4032 : F) * W.b₂ ^ 9 * W.b₄ ^ 4 + (-4992 : F) * W.b₂ ^ 10 * W.b₄ ^ 2 * W.b₆ + (960 : F) * W.b₂ ^ 11 * W.b₆ ^ 2) * X ^ 2 +
    C ((414783618048 : F) * W.b₄ ^ 2 * W.b₆ ^ 4 + (213363520512 : F) * W.b₄ ^ 5 * W.b₆ ^ 2 + (23804895232 : F) * W.b₄ ^ 8 + (-7844428800 : F) * W.b₂ * W.b₆ ^ 5 + (-193369826304 : F) * W.b₂ * W.b₄ ^ 3 * W.b₆ ^ 3 + (-40137104384 : F) * W.b₂ * W.b₄ ^ 6 * W.b₆ + (-16138082304 : F) * W.b₂ ^ 2 * W.b₄ * W.b₆ ^ 4 + (8215423104 : F) * W.b₂ ^ 2 * W.b₄ ^ 4 * W.b₆ ^ 2 + (389707008 : F) * W.b₂ ^ 2 * W.b₄ ^ 7 + (6868883712 : F) * W.b₂ ^ 3 * W.b₄ ^ 2 * W.b₆ ^ 3 + (-1366180224 : F) * W.b₂ ^ 3 * W.b₄ ^ 5 * W.b₆ + (223659648 : F) * W.b₂ ^ 4 * W.b₆ ^ 4 + (732454912 : F) * W.b₂ ^ 4 * W.b₄ ^ 3 * W.b₆ ^ 2 + (-204013088 : F) * W.b₂ ^ 4 * W.b₄ ^ 6 + (-7257984 : F) * W.b₂ ^ 5 * W.b₄ * W.b₆ ^ 3 + (353368544 : F) * W.b₂ ^ 5 * W.b₄ ^ 4 * W.b₆ + (-125630560 : F) * W.b₂ ^ 6 * W.b₄ ^ 2 * W.b₆ ^ 2 + (10338816 : F) * W.b₂ ^ 6 * W.b₄ ^ 5 + (292000 : F) * W.b₂ ^ 7 * W.b₆ ^ 3 + (-14603264 : F) * W.b₂ ^ 7 * W.b₄ ^ 3 * W.b₆ + (3514880 : F) * W.b₂ ^ 8 * W.b₄ * W.b₆ ^ 2 + (-223872 : F) * W.b₂ ^ 8 * W.b₄ ^ 4 + (258304 : F) * W.b₂ ^ 9 * W.b₄ ^ 2 * W.b₆ + (-26240 : F) * W.b₂ ^ 10 * W.b₆ ^ 2 + (2048 : F) * W.b₂ ^ 10 * W.b₄ ^ 3 + (-2048 : F) * W.b₂ ^ 11 * W.b₄ * W.b₆) * X ^ 3 +
    C ((-23533286400 : F) * W.b₆ ^ 5 + (249457757184 : F) * W.b₄ ^ 3 * W.b₆ ^ 3 + (92952207360 : F) * W.b₄ ^ 6 * W.b₆ + (90952243200 : F) * W.b₂ * W.b₄ * W.b₆ ^ 4 + (25942199808 : F) * W.b₂ * W.b₄ ^ 4 * W.b₆ ^ 2 + (29879480320 : F) * W.b₂ * W.b₄ ^ 7 + (-115483580928 : F) * W.b₂ ^ 2 * W.b₄ ^ 2 * W.b₆ ^ 3 + (-64285855488 : F) * W.b₂ ^ 2 * W.b₄ ^ 5 * W.b₆ + (-1350604800 : F) * W.b₂ ^ 3 * W.b₆ ^ 4 + (27308207616 : F) * W.b₂ ^ 3 * W.b₄ ^ 3 * W.b₆ ^ 2 + (-2449259904 : F) * W.b₂ ^ 3 * W.b₄ ^ 6 + (3772891392 : F) * W.b₂ ^ 4 * W.b₄ * W.b₆ ^ 3 + (4325257792 : F) * W.b₂ ^ 4 * W.b₄ ^ 4 * W.b₆ + (-1722895872 : F) * W.b₂ ^ 5 * W.b₄ ^ 2 * W.b₆ ^ 2 + (56763328 : F) * W.b₂ ^ 5 * W.b₄ ^ 5 + (4317504 : F) * W.b₂ ^ 6 * W.b₆ ^ 3 + (-78930560 : F) * W.b₂ ^ 6 * W.b₄ ^ 3 * W.b₆ + (21979840 : F) * W.b₂ ^ 7 * W.b₄ * W.b₆ ^ 2 + (248960 : F) * W.b₂ ^ 7 * W.b₄ ^ 4 + (-463360 : F) * W.b₂ ^ 8 * W.b₄ ^ 2 * W.b₆ + (91520 : F) * W.b₂ ^ 9 * W.b₆ ^ 2 + (-33280 : F) * W.b₂ ^ 9 * W.b₄ ^ 3 + (35328 : F) * W.b₂ ^ 10 * W.b₄ * W.b₆ + (512 : F) * W.b₂ ^ 11 * W.b₄ ^ 2 + (-512 : F) * W.b₂ ^ 12 * W.b₆) * X ^ 4 +
    C ((171218810880 : F) * W.b₄ * W.b₆ ^ 4 + (361610588160 : F) * W.b₄ ^ 4 * W.b₆ ^ 2 + (108891635712 : F) * W.b₄ ^ 7 + (-259122945024 : F) * W.b₂ * W.b₄ ^ 2 * W.b₆ ^ 3 + (-176275697664 : F) * W.b₂ * W.b₄ ^ 5 * W.b₆ + (8466094080 : F) * W.b₂ ^ 2 * W.b₆ ^ 4 + (78792557568 : F) * W.b₂ ^ 2 * W.b₄ ^ 3 * W.b₆ ^ 2 + (-1517741056 : F) * W.b₂ ^ 2 * W.b₄ ^ 6 + (-12134642688 : F) * W.b₂ ^ 3 * W.b₄ * W.b₆ ^ 3 + (-916814592 : F) * W.b₂ ^ 3 * W.b₄ ^ 4 * W.b₆ + (237643776 : F) * W.b₂ ^ 4 * W.b₄ ^ 2 * W.b₆ ^ 2 + (-527848832 : F) * W.b₂ ^ 4 * W.b₄ ^ 5 + (816750336 : F) * W.b₂ ^ 5 * W.b₆ ^ 3 + (945289472 : F) * W.b₂ ^ 5 * W.b₄ ^ 3 * W.b₆ + (-314716032 : F) * W.b₂ ^ 6 * W.b₄ * W.b₆ ^ 2 + (29373632 : F) * W.b₂ ^ 6 * W.b₄ ^ 4 + (-38670976 : F) * W.b₂ ^ 7 * W.b₄ ^ 2 * W.b₆ + (6372800 : F) * W.b₂ ^ 8 * W.b₆ ^ 2 + (-705024 : F) * W.b₂ ^ 8 * W.b₄ ^ 3 + (735744 : F) * W.b₂ ^ 9 * W.b₄ * W.b₆ + (7680 : F) * W.b₂ ^ 10 * W.b₄ ^ 2 + (-7680 : F) * W.b₂ ^ 11 * W.b₆) * X ^ 5 +
    C ((-289954142208 : F) * W.b₄ ^ 2 * W.b₆ ^ 3 + (-111477669888 : F) * W.b₄ ^ 5 * W.b₆ + (62400844800 : F) * W.b₂ * W.b₆ ^ 4 + (297121010688 : F) * W.b₂ * W.b₄ ^ 3 * W.b₆ ^ 2 + (62210711552 : F) * W.b₂ * W.b₄ ^ 6 + (-147894045696 : F) * W.b₂ ^ 2 * W.b₄ * W.b₆ ^ 3 + (-99868930560 : F) * W.b₂ ^ 2 * W.b₄ ^ 4 * W.b₆ + (29162786304 : F) * W.b₂ ^ 3 * W.b₄ ^ 2 * W.b₆ ^ 2 + (-6046136576 : F) * W.b₂ ^ 3 * W.b₄ ^ 5 + (6145062912 : F) * W.b₂ ^ 4 * W.b₆ ^ 3 + (9000114176 : F) * W.b₂ ^ 4 * W.b₄ ^ 3 * W.b₆ + (-2880627456 : F) * W.b₂ ^ 5 * W.b₄ * W.b₆ ^ 2 + (227706048 : F) * W.b₂ ^ 5 * W.b₄ ^ 4 + (-278559616 : F) * W.b₂ ^ 6 * W.b₄ ^ 2 * W.b₆ + (49512128 : F) * W.b₂ ^ 7 * W.b₆ ^ 2 + (-4588288 : F) * W.b₂ ^ 7 * W.b₄ ^ 3 + (4601600 : F) * W.b₂ ^ 8 * W.b₄ * W.b₆ + (46336 : F) * W.b₂ ^ 9 * W.b₄ ^ 2 + (-46336 : F) * W.b₂ ^ 10 * W.b₆) * X ^ 6 +
    C ((106972876800 : F) * W.b₆ ^ 4 + (260818182144 : F) * W.b₄ ^ 3 * W.b₆ ^ 2 + (74796171264 : F) * W.b₄ ^ 6 + (-518594088960 : F) * W.b₂ * W.b₄ * W.b₆ ^ 3 + (-252251234304 : F) * W.b₂ * W.b₄ ^ 4 * W.b₆ + (150551294976 : F) * W.b₂ ^ 2 * W.b₄ ^ 2 * W.b₆ ^ 2 + (-6304929792 : F) * W.b₂ ^ 2 * W.b₄ ^ 5 + (21009853440 : F) * W.b₂ ^ 3 * W.b₆ ^ 3 + (21311557632 : F) * W.b₂ ^ 3 * W.b₄ ^ 3 * W.b₆ + (-11091671040 : F) * W.b₂ ^ 4 * W.b₄ * W.b₆ ^ 2 + (204558336 : F) * W.b₂ ^ 4 * W.b₄ ^ 4 + (-654065664 : F) * W.b₂ ^ 5 * W.b₄ ^ 2 * W.b₆ + (182627328 : F) * W.b₂ ^ 6 * W.b₆ ^ 2 + (-4530176 : F) * W.b₂ ^ 6 * W.b₄ ^ 3 + (11811840 : F) * W.b₂ ^ 7 * W.b₄ * W.b₆ + (63232 : F) * W.b₂ ^ 8 * W.b₄ ^ 2 + (-136960 : F) * W.b₂ ^ 9 * W.b₆) * X ^ 7 +
    C ((-670918256640 : F) * W.b₄ * W.b₆ ^ 3 + (-247967760384 : F) * W.b₄ ^ 4 * W.b₆ + (160515136512 : F) * W.b₂ * W.b₄ ^ 2 * W.b₆ ^ 2 + (-25880469504 : F) * W.b₂ * W.b₄ ^ 5 + (29720079360 : F) * W.b₂ ^ 2 * W.b₆ ^ 3 + (45052039680 : F) * W.b₂ ^ 2 * W.b₄ ^ 3 * W.b₆ + (-13154812416 : F) * W.b₂ ^ 3 * W.b₄ * W.b₆ ^ 2 + (2614658304 : F) * W.b₂ ^ 3 * W.b₄ ^ 4 + (-2459493888 : F) * W.b₂ ^ 4 * W.b₄ ^ 2 * W.b₆ + (257187072 : F) * W.b₂ ^ 5 * W.b₆ ^ 2 + (-102008832 : F) * W.b₂ ^ 5 * W.b₄ ^ 3 + (51821568 : F) * W.b₂ ^ 6 * W.b₄ * W.b₆ + (2012928 : F) * W.b₂ ^ 7 * W.b₄ ^ 2 + (-372480 : F) * W.b₂ ^ 8 * W.b₆ + (-18432 : F) * W.b₂ ^ 9 * W.b₄) * X ^ 8 +
    C ((-233258655744 : F) * W.b₄ ^ 2 * W.b₆ ^ 2 + (-89611239424 : F) * W.b₄ ^ 5 + (4707072000 : F) * W.b₂ * W.b₆ ^ 3 + (81270939648 : F) * W.b₂ * W.b₄ ^ 3 * W.b₆ + (2864166912 : F) * W.b₂ ^ 2 * W.b₄ * W.b₆ ^ 2 + (6092158976 : F) * W.b₂ ^ 2 * W.b₄ ^ 4 + (-3946537472 : F) * W.b₂ ^ 3 * W.b₄ ^ 2 * W.b₆ + (252934656 : F) * W.b₂ ^ 4 * W.b₆ ^ 2 + (-64542720 : F) * W.b₂ ^ 4 * W.b₄ ^ 3 + (-17676288 : F) * W.b₂ ^ 5 * W.b₄ * W.b₆ + (-3699712 : F) * W.b₂ ^ 6 * W.b₄ ^ 2 + (1784832 : F) * W.b₂ ^ 7 * W.b₆ + (143360 : F) * W.b₂ ^ 8 * W.b₄ + (-2048 : F) * W.b₂ ^ 10) * X ^ 9 +
    C ((5648486400 : F) * W.b₆ ^ 3 + (4221665280 : F) * W.b₄ ^ 3 * W.b₆ + (-36953487360 : F) * W.b₂ * W.b₄ * W.b₆ ^ 2 + (-13930250240 : F) * W.b₂ * W.b₄ ^ 4 + (11319413760 : F) * W.b₂ ^ 2 * W.b₄ ^ 2 * W.b₆ + (1500503040 : F) * W.b₂ ^ 3 * W.b₆ ^ 2 + (1337751040 : F) * W.b₂ ^ 3 * W.b₄ ^ 3 + (-794191360 : F) * W.b₂ ^ 4 * W.b₄ * W.b₆ + (-49536000 : F) * W.b₂ ^ 5 * W.b₄ ^ 2 + (13224960 : F) * W.b₂ ^ 6 * W.b₆ + (993280 : F) * W.b₂ ^ 7 * W.b₄ + (-10240 : F) * W.b₂ ^ 9) * X ^ 10 +
    C ((-37231902720 : F) * W.b₄ * W.b₆ ^ 2 + (-14429061120 : F) * W.b₄ ^ 4 + (12410634240 : F) * W.b₂ * W.b₄ ^ 2 * W.b₆ + (1551329280 : F) * W.b₂ ^ 2 * W.b₆ ^ 2 + (1370624000 : F) * W.b₂ ^ 2 * W.b₄ ^ 3 + (-861849600 : F) * W.b₂ ^ 3 * W.b₄ * W.b₆ + (-49753600 : F) * W.b₂ ^ 4 * W.b₄ ^ 2 + (14364160 : F) * W.b₂ ^ 5 * W.b₆ + (983040 : F) * W.b₂ ^ 6 * W.b₄ + (-10240 : F) * W.b₂ ^ 8) * X ^ 11

theorem S1942A_map {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (W : WeierstrassCurve R) :
    S1942A (W.map f) = (S1942A W).map f := by
  simp [S1942A, WeierstrassCurve.map_b₂, WeierstrassCurve.map_b₄, WeierstrassCurve.map_b₆,
    Polynomial.map_add, Polynomial.map_mul, Polynomial.map_C, Polynomial.map_X,
    Polynomial.map_pow, map_ofNat]

theorem S1942B_map {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (W : WeierstrassCurve R) :
    S1942B (W.map f) = (S1942B W).map f := by
  simp [S1942B, WeierstrassCurve.map_b₂, WeierstrassCurve.map_b₄, WeierstrassCurve.map_b₆,
    Polynomial.map_add, Polynomial.map_mul, Polynomial.map_C, Polynomial.map_X,
    Polynomial.map_pow, map_ofNat]

end CommRing

section Field
variable {F : Type*} [Field F] [CharZero F]

omit [CharZero F] in
theorem S1942_preΨ_five (W : WeierstrassCurve F) :
    W.preΨ 5 = W.preΨ₄ * W.Ψ₂Sq ^ 2 - W.Ψ₃ ^ 3 := by
  have h := W.preΨ_odd 2
  norm_num at h
  simpa [WeierstrassCurve.preΨ_one, WeierstrassCurve.preΨ_two, WeierstrassCurve.preΨ_three, WeierstrassCurve.preΨ_four] using h

theorem S1942_bezout_five (W : WeierstrassCurve F) :
    S1942A W * W.preΨ 5 + S1942B W * derivative (W.preΨ 5) =
      C (5120 * W.Δ ^ 5) := by
  rw [S1942_preΨ_five]
  refine Polynomial.funext fun t => ?_
  simp only [S1942A, S1942B]
  simp only [WeierstrassCurve.preΨ₄, WeierstrassCurve.Ψ₂Sq, WeierstrassCurve.Ψ₃, WeierstrassCurve.Δ]
  simp only [eval_add, eval_mul, eval_pow, eval_X, eval_C, eval_sub, eval_neg, eval_ofNat,
    eval_natCast, eval_intCast, eval_one, eval_zero, derivative_add, derivative_mul,
    derivative_C, derivative_X, derivative_pow, derivative_sub, derivative_neg, derivative_ofNat,
    derivative_natCast]
  rw [S1933_b8 W]
  field_simp
  ring

theorem S1942Certificate_five : S1933Certificate 5 := by
  refine ⟨5, 5120, S1942A S1933W, S1942B S1933W, by norm_num, ?_⟩
  let K := FractionRing (MvPolynomial (Fin 5) ℤ)
  let φ : MvPolynomial (Fin 5) ℤ →+* K := algebraMap _ _
  let W : WeierstrassCurve K := S1933W.map φ
  have hinj : Function.Injective φ := IsFractionRing.injective _ _
  have h := S1942_bezout_five W
  have hA : S1942A W = (S1942A S1933W).map φ := by
    rw [← S1942A_map φ S1933W]
  have hB : S1942B W = (S1942B S1933W).map φ := by
    rw [← S1942B_map φ S1933W]
  have hpre : W.preΨ 5 = (S1933W.preΨ 5).map φ := by
    rw [WeierstrassCurve.map_preΨ]
  have hΔ : W.Δ = φ S1933W.Δ := by
    rw [WeierstrassCurve.map_Δ]
  rw [hA, hB, hpre, hΔ] at h
  apply Polynomial.map_injective φ hinj
  simpa only [Polynomial.map_add, Polynomial.map_mul, Polynomial.map_C, Polynomial.map_pow,
    Polynomial.map_natCast, Polynomial.map_ofNat, Polynomial.derivative_map, map_mul, map_pow, map_ofNat] using h

theorem S1942_preΨ_five_separable (W : WeierstrassCurve F) [W.IsElliptic] :
    (W.preΨ 5).Separable :=
  S1933separable_of_certificate W S1942Certificate_five

end Field

/-! ## 4. Axiom footprint -/

#print axioms S1942_preΨ_five
#print axioms S1942_bezout_five
#print axioms S1942Certificate_five
#print axioms S1942_preΨ_five_separable

end LeanFormal.IUT.XiFPaper.S1942PrePsiFiveActual
