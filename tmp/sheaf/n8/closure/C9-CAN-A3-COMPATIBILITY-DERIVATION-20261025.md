# C9 A3 — cQ3/cQ4 NATURAL-LANGUAGE DERIVATION

Date: 2026-10-25. Status: P6 OPEN. No Lean.
Source: IUT-III.txt SHA256 822E03DA7E2A7402A3BB406D698BB3374401E3FB102058C80864D6C06139353D.

## 0. Correction

Wrong statement: 'sQ3/sQ4 = cQ3/cQ4'.
Correct statement:
  cQ3 is the compatibility property of sQ3;
  cQ4 is the compatibility property of sQ4;
  cQ3 + cQ4 do NOT imply the composite closed loop.
The closed loop is a separate source assertion in Remark3.9.5(ix).

## 1. Derivation of cQ3

cQ3. sQ3 output (hull -> det^tensor M) is an object of the F^⊣×mu-prime-strip
with natural faithful actions by local Galois groups G_v and units
O^×mu_Fv.

Source anchors: Ob1/Ob2 (lines 7758-7787), Ob3 (7788-7855), Ob3-2
(7820-7845), Ob7-1/Ob7-2 (7994-8082), cQ3 (8264-8345).

Step 1. Hull is O_K^×-stable.
By Ob1, a hull in H is stabilized by multiplication by elements of O_K.
By Ob2, passing from an arbitrary region P to its hull phi(P) gives a region
stabilized by O_K^× and defining the local portion of an arithmetic vector
bundle E_H. Hence E_H carries a natural O_K^× action.

Step 2. Determinant inherits the action.
det^tensor M is a functorial construction on arithmetic vector bundles
(Ob3, Ob3-1, Ob3-2). Therefore the O_K^× action on E_H induces an O_K^×
action on L_H=det^tensor M(E_H).

Step 3. Localization triviality turns the unit action into a root-of-unity
action.
By Ob3-2, choose M sufficiently divisible so that the localization at each
v in V of the det^tensor M output is trivial. Then the O_K^× action on the
localization factors through O_K^× modulo the principal units, i.e. through
the roots of unity/cyclotome. This is precisely the O^×mu_Fv portion of the
F^⊣×mu-prime-strip.

Step 4. G_v action from the Frobenioid.
L_H is an object of the local and global Frobenioids of the codomain
F^⊩▶×mu-prime-strip. Such objects carry the natural local Galois group
action G_v; by Ob7-1, G_v is invariant/coric under the Theta×mu and log-links.
The determinant construction is compatible with the Frobenioid
base-change/pullback morphisms, hence the G_v action on L_H is natural.

Step 5. ⊼-quotient preserves the actions.
The ⊼-formalism (Ob5) is a set-theoretic quotient on the same Frobenioid
data; the G_v and O^×mu actions come from the structure and descend to the
quotient. Therefore sQ3 output is an F^⊣×mu-prime-strip object with natural
faithful G_v and O^×mu_Fv actions. This is cQ3.

## 2. Derivation of cQ4

cQ4. sQ4 (vertical-shift adjustment via the log-Kummer correspondence) yields
F^⊣×mu-prime-strip data compatible with the input data, up to arbitrary
iterates of the log-link.

Source anchors: Ob7 (7961-8096), Ob8 (8097-8127), cQ4 (8346-8366),
Remark3.9.4 log-volume/log-link compatibility.

Step 1. Log-link maps units to additive log-shells.
The log-link sends Frobenius-like units O^× to the additive log-shell m via
log; this is the basic log-link construction (Ob8, Theorem1.5).

Step 2. Vertical shift is a translation by log(O_K^×)=m.
Changing the vertical coordinate in the log-theta-lattice changes log u by
an element of log(O_K^×)=m. Thus on the log-shell, the vertical shift is
translation by m.

Step 3. F^⊣×mu data record log modulo m.
The F^⊣×mu-prime-strip records the local Galois group G_v, the unit group
O^×mu_Fv, and the value group. The value-group portion is the log modulo
log(O_K^×)=m. Hence translation by m is invisible in the F^⊣×mu data.

Step 4. Kummer isomorphism identifies log-shell and value-group data.
The Kummer isomorphism O^×/O^×mu ≅ value group aligns the log-shell data
with the value-group data; changing the vertical coordinate changes the
Kummer class only by a log-link iterate (Ob8, final portion; cQ4).

Step 5. Equivariance.
The log-link and the Kummer isomorphism are G_v-equivariant; the unit
O^×mu action is preserved. Therefore the sQ4 output carries the same type of
G_v/O^×mu actions as the input, compatible up to arbitrary log-link iterates.
This is cQ4.

## 3. What is NOT derived

The individual compatibility cQ3/cQ4 does NOT imply the composite closed
loop
  q-pilot -> LGP-link -> sQ1,sQ2 -> sQ3,sQ4 -> q-pilot.
Remark3.9.5(ix), lines 8383-8431, asserts the closed loop separately: the
chain of poly-isomorphisms through sQ1-sQ4 forms a closed loop, and only a
closed loop completes the projection of the Theta-intertwining onto the
q-intertwining. Skipping sQ3 or sQ4 breaks the loop.

Also, sQ5 (passing to log-volumes) is NOT compatible with F^units×mu data;
source (iQ5) says it forgets local Galois groups/Frobenius-like units. It is
the final coarse quotient applied after the closed loop, not a step
compatible with cQ3/cQ4.

Finally, xi-f exact membership
  Q_can in R_{<=h_can}
is the source's formal conclusion. It is not derived from cQ3/cQ4 alone.

## 4. Status

cQ3: derived.
cQ4: derived.
closed loop: source assertion, not derived from cQ3/cQ4.
xi-f exact membership: source formal conclusion.
P6_can: conditional on xi-f and closed loop.
P6: OPEN. target_accepted=false.