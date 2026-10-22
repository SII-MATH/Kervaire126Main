# Independent audit, round 2

Baseline: `34fb925fd3c30304832e40e1c87938ff00908b67`.
Auditor: `/root/strong_kervaire_audit`. This is an informal mathematical
review, not a new Lean theorem or a discharge of the production source and
comparison obligations. Production files and archived databases were read
only. The previous round's audit remains in `../../audit/audit.md`.

## 1. Moore permanence is equivalent to an order-two theta6

Verdict: **pass**, with the completed objects and source hypotheses explicitly
stated in `../bridge/report.md`.

I read the complete bridge argument and independently compared it to the
actual BHS source statements. `SynRevHom.tex:4-33` supplies an actual lift
to `nu X` for a permanent cycle, under nilpotent completeness and strong
convergence. It also states detection for every actual lift of a nonzero
infinity-page class. This closes the earlier possible inverse-limit gap;
the argument does not infer an actual lift merely from separate finite lifts.

For the 2-complete sphere and Moore spectrum, the short exact homology
sequence for `S -> C2 -> Sigma S` gives the synthetic triangle

    Sigma^(0,1) nu S --tilde2--> nu S --i--> nu C2.

The source of this assertion is Pstragowski Lemma 4.23, restated in
BHS `SynRevIntro.tex:53-60`. BHS `SynRevBigraded.tex:86-118` constructs
the factorization and its assembly square, giving `lambda tilde2 = 2`
for the connecting map in this triangle. Its reduction is the usual h0
extension of Steenrod modules.

The remaining proof has the following checked degrees:

    h7:                 pi_(127,128)(nu S / lambda)
    partial_lambda h7:  pi_(126,129)(nu S)
    x:                  pi_(126,128)(nu S)

The lambda Bockstein reduces to `d2 h7 = h0 h6^2`. If `u=i(h7)` is
permanent, its actual lift gives `i(partial_lambda h7)=0`. Exactness gives
`tilde2 x=partial_lambda h7`, hence `2x=0`. Reduction gives
`h0 rho(x)=h0 h6^2`. The complete Ext space in `(2,128)` has sole generator
`h6^2`, and its h0 product is nonzero; therefore `rho(x)=h6^2`.
Its established nonzero permanence and BHS detection imply that realization
of x is a nonzero, order-two class detected by `h6^2`.

Conversely, the Moore exact sequence lifts an order-two theta6 to a class
in `pi_127 C2` outside `F3`. In that stem the filtration-zero and
filtration-two E2 groups vanish and filtration one is spanned by u.
Strong convergence forces detection by u. There are no incoming
differentials on u, since their source filtration is negative.

Thus the previously missing positive bridge is closed. It does not settle
any differential on u. Completeness is being used for the actual 2-primary
stable question, and the result is not asserted for arbitrary incomplete
filtered objects.

## 2. The proposed d6 into z is excluded

Verdict: **conditional pass**, using the cw210 sphere survival input,
the stated sphere d5 dichotomy, and the already established nonzero d3 on
`x126,6`. A later version comparison found that the needed vanishing of
the sphere d4 on `x127,6` is not established in cw49; see section 6.

The original C2 database at `(11,137)` has five E2 coordinates. Its staircase
consists of three d3 boundaries, a nonzero d4 on coordinate 4, and the
cycle `i(T)=coordinate 3 + coordinate 4`, where

    T = h1 (x125,10,2 + x125,10).

All possible d4 incoming sources at `(7,134)` survive through E5. Thus
`i(T)` is nonzero on E5, not merely a nonzero E2 vector. The sphere E5
target `(11,137)` is at most the span of T: two directions are d2
boundaries, two are d2 sources, and one more is a d4 source. The worker's
local certificate records this entire quotient.

At the possible C2 d6 source `(6,133)`, any combination containing the
top lift v maps under q to `x126,6`. Its known nonzero d3 prevents that
combination from representing an E6 class. The remaining source is the
bottom image `w=i(x127,6)`.

If the sphere d5 on `x127,6` is T, naturality and nonzero i(T) kill w
before E6. If w reaches E6, the sphere d5 is consequently zero and the
sphere class supplies an E6 preimage; any earlier sphere boundary would
also make w a boundary. The entire bottom-image target in `(12,138)`
is already zero on E4, so naturality then gives `d6(w)=0`.

Subject to the stated sphere survival input, this excludes the whole
candidate d6 into z. It leaves the candidate d5 into z, and the actual
d11 on u, unresolved. Without that input, an earlier sphere d4 with zero
bottom image prevents this proof from supplying the required E6 preimage
of w. Thus this section does not assert an unconditional d6 exclusion
from the latest archive, or that z is nonzero on E11.

## 3. A more precise Ctheta5-squared comparison

The archive has a filtration-one map

    F: Ctheta5sq -> Sigma^(-2) C2

with leading images `[125] -> u` and `U[0] -> 0`, where
`U=h0^2 x124,8`. Its configuration is in `ss.json:389`; its restriction
to the bottom sphere is the eta lift `S^2 -> C2`, not the bottom inclusion.

This comparison suggests relating

    d10([125]) = U[0]       and       d11(u) = z.

The leading E2 map alone does not give this implication. The exact
additional input can be formulated using the corrected layered GLR in
Wu, arXiv:2606.02779v2, Theorem 3.24, rather than an unlayered rule.
Any actual use also requires the indicated geometric map and its filtered
lift with the stated calibration; an archived E2 matrix does not itself
construct that map or its coherence data.

Normalize F to a degree-zero filtered map

    f: Sigma^(0,1) nu(Ctheta5sq) -> nu(Sigma^(-2) C2).

The normalized Adams bidegrees are

| Class | (s,t) |
| --- | --- |
| x = shifted top cell | (1,126) |
| x' = shifted U[0] | (11,135) |
| y = shifted u | (1,126) |
| y' = shifted z | (12,136) |

In Wu's notation choose `r=9`, `m=0`, `l=1`, `n=9`, `j=0`.
The source differential is `d_(r+1)=d10`; the result would be
`d_(r-m+l+1)=d11`. The required bottom layer is

    i = r-m-1 = 8.

For example, taking the theorem's bottom page parameter to be infinity
requires the genuine layer-eight extension

    lambda^8 f[U] = lambda^9 [z],

with the corresponding source/target lifts. A smaller finite bottom page
is another possible formulation, but still requires its own actual lift
relation. The source complementarity condition is automatic because m=0.
Bottom complementarity has only one possible crossing: a layer-nine,
jump-zero map from the next source filtration. In this case its source is
the classical `(11,135)` Ctheta5sq group. Its cycle directions are already
d2/d3 boundaries; its other directions support d2/d4. Thus an infinity-page
crossing cannot contribute modulo the target's `B10`. This does not supply
the missing layer-eight extension itself.

### 3.1 Newly located archival extension

A direct read-only query of

    cofseq_C2__CW_2_eta__S0.db

in the original cw210 archive gives

    iC | s  | t   | base | diff | level
     2 | 10 | 134 | 4    | 0    | 9998

Here iC=2 is the eta-lift edge, sphere coordinate 4 is U, target coordinate
0 is z, and level 9998 is a filtration-jump-two extension. This is a useful
new candidate: the classical eta-lift extension `U -> z` is recorded.

Its meaning must not be overstated. The native cofibration ESS is built
from the classical infinity-page data. For example,
`SSeqCpp-master/ss/cofseq.cpp:234-275` explicitly reduces its vectors by
ordinary SS boundaries using `LEVEL_PERM`; the schema contains no finite
lambda-page or layer parameter. Such a row does not certify the precise
layer-eight relation above. Wu Remark 3.2 explicitly distinguishes an
abutment extension from an extension at a specified layer: the former
only gives a sufficiently high layer.

Both U and z have raw SS level 9000. This certifies the encoded absence of
outgoing differentials through the sentinel range; it does not preclude
their being incoming boundaries. In particular z is still allowed to be
hit, and the native code re-reduces the ESS after discovering such a
boundary. The stored nonzero target must not be treated as proof that z
survives to E-infinity or even E11.

There is a reason that replacing "sufficiently high" by layer eight is
substantive. After the displayed powers of lambda, the relation has
original C2 degree `(stem,weight)=(126,129)`, or filtration three.
A possible `d11(u)=z` gives exactly a lambda-torsion ambiguity in this
degree, represented by `lambda^9[z]`. Hence one cannot remove this
ambiguity by assuming the very differential under investigation is zero.

### 3.2 Minimal logical countermodel

Even before considering the recorded abutment extension, leading-map data
alone is insufficient. Over F2 take a filtered chain complex X generated
by a of filtration zero and A of filtration ten, with `d(a)=A`.
Take Y generated by b of filtration one and B of filtration twelve.
For either `epsilon=0` or `epsilon=1`, set

    d(b)=epsilon B,     F(a)=b,     F(A)=epsilon B.

These are filtration-at-least-one chain maps. Both have the same leading
map `a -> b`, `A -> 0`; X has d10, but Y has d11 precisely when epsilon=1.
This is a countermodel to an inference using only leading-map information,
not a proposed model of the actual spectra or of all the archive's data.

## 4. Literature scope

Minami arXiv:2106.14604v6 (2026-09-07), cached in `../bridge/`, asserts
2-divisibility of the Whitehead square on the sphere S127 and hence the
existence of theta6. The introduction explicitly identifies its conclusion
with existence. It does not assert an order-two theta6, decide u, or
compute theta5 squared. Therefore it does not settle either current
obstruction, irrespective of whether its geometric proof is accepted.
This audit has not certified that proof; no such certification is needed
for this scope distinction.

The limited online searches for h5 n squares and strong Kervaire results
do not establish novelty of the local filtration refinements. The BX
nested-bracket strategy is explicitly already in
`Source/BurklundXu/source/kervairev2.tex:620-665`.

## 5. Mixed-product review status

Verdict: **pass**, relative to the explicit classical inputs in
`../theta5/report.md`. For every theta5 detected by `h5^2` and every a6
detected by `h5 n`,

    theta5 a6 in F13 pi_124.

More generally, `theta5 * F6 pi_62` is contained in `F13 pi_124`.

The proof addresses the essential coherence issue rather than replacing
one bracket member by an independently selected convenient one:

1. With the previously calibrated alpha, the E4 Moss theorem gives one
   member of `B=<alpha,2,theta4>` in F6, raised to F10 by the stem-93 gap.
   The full indeterminacy `alpha pi_31 + pi_63 theta4` lies in F10.
   Thus every gamma in B is in F10.
2. Full shuffle and `pi_61=0` give `gamma theta4=0` for every gamma in B.
   All outer brackets are therefore defined, including the ones selected
   by the fourfold product construction.
3. E3 Moss gives one F11 member of each outer bracket
   `<gamma,theta4,2>`. Its complete indeterminacy is in F11 because
   `gamma pi_31` is in F13 and `2 pi_124` is in F11. Hence every member
   of every outer bracket is in F11=F13.
4. The fourfold representative theta then gives `alpha theta in F13`.
   Replacing theta changes this by F12=F13. Replacing alpha changes it
   by a theta product with F8; the complete grade-eight product is zero
   in Ext, so that change is also in F11=F13.

I independently queried all source rows for the two Moss windows. For
the inner E4 application, the stem-63 groups below filtration four contain
only d2 sources and the permanent `h1 h5^2`. For the outer E3 application,
the stem-124 groups below filtration ten are exactly the rows in the
worker's table. In particular, the filtration-seven d5 has target
filtration twelve, equal to the product filtration. It is absent by the
page tested in Moss's condition and is not a crossing. The strict
inequality here was already checked against Moss's original source in
round 1.

The three complete Ext basis elements in `(10,103)` all multiply to zero
with `h4^2`, as recorded by the worker's bounded polynomial certificate.
The proof therefore does not assume a chosen gamma has a convenient
leading representative. Its formulation permits zero detection when
gamma lies in a higher filtration, consistently with the filtered
convergence statement already audited in round 1.

The complete finite stem-124 table proves `pi_124=F10` and `F11=F13`.
The separate claim that c itself is a nonzero infinity-page class is
explicitly stated in AimPaper Fact `theta5sqAF(3)`, line 2164, and table
line 2978; it is not inferred from a level-9000 database row.

This theorem is stronger than a renaming of the AF10 square coefficient:
it removes a possible low-filtration mixed product. It still does not
compute the square. Applying the same nested bracket to theta5 in place
of alpha only puts the inner bracket in F5, with possible detector
`h1 g3`. The new proof's F10 bound depended on alpha's filtration six.
The square refinement `a6^2 in F14` from round 1 likewise does not
determine the common AF10 theta5-square coefficient. Novelty remains
unverified.

## 6. Data-version distinction

The coordinator located a material difference between archived datasets:
the older cw210 data record u at level 9989 (first unknown d11), whereas
the current cw49 archive records it at level 9993 (first unknown d7).
The B worker subsequently found another material difference: sphere
`x127,6` at `(6,133)` has first unknown d4 in cw49, but first unknown d5
in cw210. In cw49 the candidate

    d4(x127,6) = h0^2 x126,8,3

has not been excluded. Its bottom image is zero already in C2 E2, so
naturality with the bottom inclusion cannot exclude it. The supporting
sphere d3 that would make this target a boundary is also still unknown
in cw49. The matching T/i(T) rows therefore do not suffice to transfer
the d6 exclusion to that dataset. Neither discrepancy can be resolved
merely by assigning the larger archive greater authority.

Consequently "u has reached E11" is, at this review point, a statement
about cw210, not an independently established common fact of the current
datasets. The comparison in section 3 identifies what would relate d10
and d11; it does not establish the prior survival of u in the latest data.
The B worker's report records the remaining d7-through-d10 branches;
the conditional comparison in section 7 does not close them.

The permanence/order-two equivalence is a theoretical statement with
low E2 inputs, and the mixed-product theorem uses only sphere calculations
and Toda brackets. These two conclusions are unaffected. The A worker's
targeted cw49 comparison additionally verified all relevant stem-124,
stem-93, and stem-63 rows and all newly used products; its certificate is
`../theta5/crosscheck-result.json`. The d6 exclusion is now explicitly
conditional on the additional sphere d4 vanishing.

## 7. Ordinary naturality can recover E11, conditionally

Verdict: **the naturality implication is valid**. It is distinct from the
layer-eight hidden-extension problem in section 3.

Suppose there is an actual normalized synthetic map

    f: Sigma^(0,1) nu(Ctheta5sq) -> nu(Sigma^(-2) C2)

whose reduction sends the top class x to u and U to zero. Suppose the
actual top class reaches E10 and has `d10(x)` equal to either zero or U.
Because this is one fixed map of actual synthetic spectra, ordinary
lambda-Bockstein naturality applies on every page, with no generalized
Leibniz rule needed. For r=2 through 9 it gives

    d_r(u) = f_r(d_r(x)) = 0.

The source shift and target suspension make this an ordinary degree-zero
map, so differential lengths are unchanged. On E10 it gives

    d10(u) = f_10(d10(x)) = 0,

since an element whose E2 image is zero has zero image on every later
page on which it is defined. There are no incoming differentials on u.
Consequently u is nonzero on E11. This argument says nothing about
d11(u): after x dies by d10 it no longer supplies a source for ordinary
naturality, and the alternative d10(x)=0 is not itself a d11 calculation.

### 7.1 What the geometric sources actually supply

The existence of a classical F is better supported than a bare matrix in
`ss.json`. The active Burklund--Xu quadratic construction in
`Source/BurklundXu/source/kervairev2.tex:444-465,479-519` starts with the
order-two theta5 and gives a map `g:X->S`, where X has cells in dimensions
124,126,127, with the eta and 2 attachments, and the restriction to its
bottom sphere is `theta5^2`. Thus X fits into

    S^124 -> X -> Sigma^126 C2.

Dualizing and shifting by 124 gives the triangle

    Sigma^(-3) C2 -> Sigma^124 DX -> S -> Sigma^(-2) C2.

The dual of g supplies a lift of `theta5^2` through the middle object.
Its null composite with the connecting map therefore extends that map
over `C(theta5^2)`, constructing the required classical F. Its bottom
restriction is the eta lift associated with this triangle. This uses the
actual quadratic-construction cell diagram and its coherent attaching
maps, not just the generic name of a four-cell complex.

The ordinary mod-2 homology map of F vanishes by degree: its source cells
are in dimensions 0 and 125, and its target cells in dimensions -2 and
-1. Hence F has Adams filtration at least one. BHS's filtration-one
factorization theorem produces an actual normalized synthetic lift.

These facts establish **classical F exists** and **an actual filtration-one
synthetic lift exists**. They do not yet identify the reduction of that
lift with every entry of the archived Ext matrix. In particular, the
top-cell value must still be calibrated to be the nonzero class h7[0].
The bottom value is constrained by the eta-lift restriction, and its
product with U is the recorded zero Ext product. The unresolved
calibration is the top value for one actual compatible lift.

BX's synthetic quadratic construction contains promising additional
information: its middle cell maps by `h6^2`, and the adjacent 2 attachment
forces its top value to be h7 by the Hopf-invariant Bockstein. However,
these are cells of the modified synthetic complex in the BX construction.
They are not, merely by having the same classical realization, the cells
of `Sigma^(0,1) nu(Ctheta5sq)` in section 7.

The assembly direction is a concrete issue. With the chosen synthetic
theta5 in degree `(62,64)`, `lambda^2 theta5^2` lies in `(124,126)`.
Its cofiber has bottom cell `(0,0)` and top cell `(125,126)`. The shifted
canonical `Sigma^(0,1) nu(Ctheta5sq)` has bottom `(0,1)` and the same top
`(125,126)`. The immediate assembly comparison goes from the former to
the latter (bottom lambda, top identity). It does not automatically
transport a map out of the former backwards to a map out of the latter.
An additional coherent comparison or factorization is needed to use the
BX top-cell computation as the required canonical calibration.

AimPaper discusses the quadratic theorem at lines 2113-2136 and
the canonical-versus-modified synthetic cofiber distinction at 976-988.
It does not explicitly identify the archived F with the needed
calibrated normalized map. The machine-paper naming convention in
`Source/LWXMachine/source/ms.tex:183-225` specifies cofiber sequences
and allows different homotopy types satisfying a name; it is not itself
a calibration of this synthetic lift. The archives record the Ext
matrix and filtration, but no proof of this remaining comparison was
located in the sources inspected.

Accordingly this audit **does not unconditionally restore E11 survival**.
It records a valid, simpler conditional theorem and a substantially
more precise missing input: certify that one actual filtration-one lift
of the quadratic-construction F has top reduction h7[0]. This is separate
from, and weaker than, the layer-eight extension needed to determine d11.

## 8. The finite Moore lifting condition for the remaining d5

Verdict: **the equivalence and page indexing pass**. This does not solve
the lifting condition or determine the differential.

Let `A=x127,7,2` in `pi_(127,134)(S/lambda)`, put
`D=partial_lambda A` in `pi_(126,135) S`, and let `a=i(A)`.
Its reduction is `rho(D)=h0 b`, where `b=x126,8`. The actual synthetic
Moore triangle and naturality give `partial_lambda a=i(D)`.

Assuming a has already reached E5, the statement `d5(a)=0` is equivalent
to a lifting to `M/lambda^5`. The lambda cofiber sequences identify this
with

    i(D) in im(lambda^4),

or equivalently with `rho4 i(D)=0`. Apply the actual Moore triangle
after tensoring with `S/lambda^4`. Its exact homotopy sequence gives
the precise criterion

    exists beta4 in pi_(126,134)(S/lambda^4),
    tilde2 beta4 = rho4(D).

The weights agree: tilde2 adds one to weight. E5 reach alone instead
gives the analogous beta3 over `S/lambda^3`. The new beta4 is not
required to lift every independently selected beta3; it must reduce to
some compatible beta3. This representative distinction prevents an
obstruction attached to an arbitrary chosen lift from deciding d5.

Reduction of the beta4 equation imposes the exact E2 equality
`h0 rho(beta4)=h0 b`. Passing to a quotient by prior boundaries may
describe possible leading detectors, but it does not establish the
finite-level equation. Boundary corrections in the kernel of h0 remain
possible lift choices. The reported affine detector candidates are
therefore not a certificate of beta4's existence.

Here "reach" refers to vanishing of the relevant outgoing differentials;
nonzero survival also requires the usual incoming-boundary check.
The worker's proposed further 3-by-3 identification of a selected
beta3's obstruction with q(z) requires compatible representative choices
and is not certified by the present audit.
