# The Moore-spectrum obstruction to an order-two theta6

Date: 2026-10-22. Worktree baseline: `34fb925fd3c30304832e40e1c87938ff00908b67`.
Scope: ordinary mathematics and read-only probes of the original cw210 archive;
private experimental copies are confined to this directory. No production Lean,
interface, obligation, or build output was changed. The public fixed Lean object
family does not currently contain C2, so this is not a new Lean theorem.

## Outcome

**No value of d11 has been determined.** There is a precise finite investigation,
with a proved vanishing cutoff, several independently checked map relations,
and a smaller list of earlier differentials needed to certify the target.

Write `u=h7[0]` in the ordinary mod-2 Adams spectral sequence of C2, with
`(s,t)=(1,128)`. The original cw210 database records survival through E11.
Its first possible target is the C2 module generator 368 in `(12,138)`:

```
z = ((h0 h6 x62,10 + h0^4 x125,8)[1]).
```

The notation is the archive's chosen Ext lift, not an unspecified homotopy lift.
The original source row has `base=0,diff=NULL,level=9989`; its target row has
`base=0,diff=NULL,level=9000`. The latter asserts no outgoing differential within
the engine's permanence range; it does not exclude earlier incoming boundaries.
In particular **z has not yet been certified nonzero on E11**.

No page beyond 62 can occur, by the genuine Adams vanishing theorem below.
The remaining finite range must still include classes whose own earlier outgoing
differentials are unknown and might vanish. An initial four-page shortcut
incorrectly discarded those classes; the corrected probe deliberately retains
every row not already a recorded earlier boundary. In particular, the actual
native-engine zero branch next considers d13, so a four-page stopping list is
not valid. The high-target output is only E2 modulo recorded earlier boundaries,
not an E_r dimension or a fully certified list of surviving targets.

## Exact relation to the question

Let `G=pi_126(S)^_2` and let F be its mod-2 Adams filtration. Nonzero permanence
of h6^2 supplies theta in F2 whose image in F2/F3 is h6^2. All representatives of
this fixed detection class form theta+F3. The standard differential
`d2(h7)=h0 h6^2` gives `2 theta in F4`. Consequently

```
o(h6^2) = [2 theta] in F4 G / 2 F3 G
```

is independent of theta, and vanishes exactly when a representative theta+a
has order two. This follows from `2(theta+a)=2theta+2a` and nonzero detection.
The zero E_infinity product h0 h6^2 alone does not compute this obstruction.

For the actual top-cell projection `q:C2 -> Sigma S`, exactness gives
`im(q_*:pi_127 C2 -> pi_126 S)=ker(2)`. If an order-two theta detected by h6^2
exists, take q(a)=theta. Since q does not decrease Adams filtration, a is not
in F3. In the 127-stem of C2, E2 in filtrations 0 and 2 is zero and filtration 1
has sole generator u. Strong convergence therefore forces a to be detected by u.
Thus any certified nonzero outgoing differential on u disproves existence of
an order-two theta6.

The converse needs an additional filtered comparison: a permanent u must admit
a lift a for which q(a) has leading term h6^2. Ordinary E2 naturality gives
q(u)=0, not h6^2. The expected length-one hidden q-extension is related to
`d2(h7)=h0 h6^2` by a geometric-boundary theorem, but the actual filtered
comparison is not proved in this report. The potential low-filtration crossing
sources are absent because C2 filtration 2 in this stem is zero; that degree
check is not a replacement for the comparison theorem. The negative implication
above is independent of this missing converse.

## The finite cutoff is unconditional on the archive

Ravenel, *Complex Cobordism and Stable Homotopy Groups of Spheres*, Theorem
3.4.5(a), states at p=2:

```
Ext_A^(s,t)(F2,F2)=0 if 0<t-s<2s-epsilon(s),
epsilon(s)=1 for s=0,1 mod4; 2 for s=2 mod4; 3 for s=3 mod4.
```

The short exact A-module sequence
`0 -> Sigma F2 -> H^*(C2) -> F2 -> 0` yields an Ext long exact sequence whose
two terms adjacent to `Ext_A^(s,t)(H^*C2,F2)` are sphere Ext in `(s,t)` and
`(s,t-1)`. At stem126 these have stems126 and125. For every s>=64,
`2s-epsilon(s)>=127`, so both are zero. Hence C2 Ext in stem126 vanishes for
s>=64. Since `d_r u` has s=r+1, its target vanishes for every r>=63.
This bounds all possible outgoing differentials by r<=62, within the existing
internal-degree range t<=200. This argument was independently checked by the
assigned mathematical auditor.

Local primary source:
`/inspire/hdd/global_user/czxs25250150/Kervaire126/Source/Ravenel/ravenel.pdf`.
The extracted theorem is in [ravenel.txt](ravenel.txt), line4834. The computer
program's similar-looking cutoff is not used as the proof.

## What was actually certified about z

In C2 `(12,138)`, E2 has coordinates e0,e1,e2,e3 with monomials
`368`, `367`, `25,1,190,1,0`, `3,1,336,1,0`.
The archived differential matrices give:

1. e1 has nonzero d2, with target coordinates `1,4`.
2. e2 is d2 of coordinate2 in C2 `(10,137)`.
3. e3 is d3 of coordinate0 in C2 `(9,136)`.

Thus the complete E4 group is at most the single line e0=z, conditional on
those actual differential identifications. This is an explicit quotient
calculation, not an inference from z's display name. The corresponding raw
rows and source matrices are in [followup-results.json](followup-results.json).

There is no unresolved d4 into this line. The first unresolved incoming
possibility is

```
d5(i x127,7,2) = z,  source (s,t)=(7,134), C2 coordinate1.
```

This bottom image is a C2 d2-cycle although the corresponding separate sphere
generator is not a d2-cycle. Therefore ordinary bottom-map naturality cannot
declare its d5 zero by using a sphere E5 class with the same name.

The potential d6 sources at `(6,133)` are the top-cell lift
`v=gen317=(x126,6)[1]` and `w=i x127,6` (coordinates0 and1).
The actual nonzero disjunction in AimPaper/main.tex:2175 says
`d3(x126,6)=A` or `A+D`, and both alternatives are nonzero. Since q(v)=x126,6
and q(w)=0, naturality forces every combination with coefficient1 on v to
support a nonzero d3. Such combinations cannot survive to supply d6.
This exclusion uses only the known nonzero disjunction and never chooses its
unknown coefficient.

It remains possible that w supplies d6. In the sphere, the first unresolved
outgoing differential on x127,6 is d5, to the E5 line represented by
`h1(x125,10,2+x125,10)`. If this sphere d5 is zero, sphere x127,6 survives to E6.
The entire ordinary bottom-map image in the would-be d6 target `(12,138)`
vanishes by E4: its E2 image is spanned by e2,e3, the two known boundaries.
Ordinary naturality then rules out `d6(w)=z`, provided z is nonzero on E6.
If the sphere d5 is nonzero while its bottom image vanishes, a secondary
comparison is necessary; the ordinary map does not decide the C2 d6.

Filtrations5 and2 contain no C2 source for incoming d7 and d10. The filtration4
source for d8 has known nonzero d3. The unique filtration3 source for d9 is
`h1 h6^2[0]`, monomial `1,1,69,2,0` at `(3,130)`, whose row is exactly
`base=0,diff=NULL,level=9000`. Here NULL at level9000 is not an unknown d9:
it records zero outgoing differentials through page999. There is also an
independent explanation after using Main: h1 and h6^2 are permanent cycles,
and ordinary Leibniz plus bottom-map naturality makes their bottom-image
product a cycle on every page. It may become a boundary, but cannot support
a nonzero d9. These facts leave the specified d5 and the conditional d6 as
the unresolved early-boundary issues.

## Direct map and product probes

[probe.py](probe.py) independently performs F2 reduction and polynomial
normalization against the original archive. It tested 23 direct maps out of
C2 and 25 direct maps into C2, and the products by h0,h1,h2,h3,d0,h5. Results,
all raw coordinates, and input SHA-256 hashes are in
[probe-results.json](probe-results.json). Two explicit gaps are recorded:
the map with t_max136 cannot evaluate the target t138, and the semilinear map
to tmf_C2 was not implemented. Positive-filtration maps are leading-term
evidence only; no unproved shifted-naturality theorem is assumed.

The decisive ordinary projection computation is

```
q(z) = h0 h6 x62,10 + h0^4 x125,8,
```

with sphere coordinates2+4 in `(12,137)`. Coordinate2 is a d2 boundary and
coordinate4 a d3 boundary, so q(z)=0 by E4. Thus q does not distinguish the
two proposed d11 values. Every tested filtration-zero output map that preserves
the candidate z has an unresolved differential on the image of u; every such
map whose image of u is already registered through d11 kills z earlier.
For example C2->CW_2_eta makes u permanent but sends z to a d2 boundary.

The direct incoming maps have nine E2 preimages of u. Seven are already
noncycles by d2. The remaining sources are in DC2h6 (first unknown d4) and
Ctheta5sq (first unknown d10, map filtration1). None is a certified E11
preimage giving an independent known differential. The h0,h1,h2,h3 products
of z vanish already on E2; d0*z is a d4 boundary. These product equations
are compatible with either coefficient and provide no Leibniz contradiction.

## Connection to theta5 squared

The original configuration identifies Ctheta5sq as the cofiber of the chosen
theta5 squared, with top-cell degree125 and a relation expressing the attaching
map as theta5 composed with itself (`ss.json`:1020,1128,1254). Its chosen top-cell
Ext class a=[125] in `(0,125)` has first uncomputed differential d10, with
candidate `h0^2 x124,8[0]` in `(10,134)`. For the actual cofiber, the first
nonzero top-cell differential detects the attaching map's first nonzero
Adams-filtration component. A zero d10 therefore only raises the lower bound
on the filtration of theta5 squared; it is not the statement that the square
vanishes.

The archived map `Ctheta5sq__C2_by_eta` has suspension -2 and filtration1.
Its generator polynomials are

```
[0] -> C2 generator1 (the eta extension),
[125] -> h7[0],
h0^2 x124,8[0] -> 0 in Ext(C2).
```

This is a concrete common structure for the two research directions. It
does not calculate d11: the last zero requires a higher compatible lift to
compare the next obstruction. Since the map has positive filtration, even
translating its leading polynomials into a shifted differential-naturality
statement requires the appropriate actual filtered-map theorem and crossing
conditions. Neither the deprecated zero-layer rule nor an unqualified
generalized Mahowald/Leibniz formula was used.

There is also a concrete still-unknown higher top-cell map on z itself. In
`cofseq_S0__C2__S0.db` the C2 row `(12,138),iC=1` has
`base=0,diff=NULL,level=9998`, a first undetermined length-two q extension.
Its potential sphere target `(14,139)` has the sole remaining candidate
`h1 h4 x109,12`. This is the same named class that appears in AimPaper's
analysis of eta theta5 squared, but an identification of this particular
q-extension with that particular square representative has not been proved.
Consequently Main's result cannot simply be substituted to set the extension
to zero. The exact row is included in the followup output.

For Wu's Theorem4.26 to determine a d11 here, `n+m+l=10`; at least one premise
must supply an independent higher map extension for this diagram. The existing
leading-term map and its zero target product do not supply that premise. This
report does not claim that all parameter choices or all auxiliary triangles
fail; it records no completed application that decides the coefficient.

## Reproduction and limitations

```
timeout 120 python3 local-history/Reports/strong-kervaire-cuts-20261022/theta6/probe.py
timeout 120 python3 local-history/Reports/strong-kervaire-cuts-20261022/theta6/followup.py
```

Both completed within the 4 GiB process limit. Every archive connection is
read-only and immutable. JSON5 parses the original configuration; no sanitized
or seeded experiment database was substituted. Followup output also records
database version rows and the configuration hash.

The independent cw210 proof database is not present locally. Consequently the
original derivations of d2 through d10 on u, and the full dependency chains of
the archived known differentials, remain unaudited. The explicit quotient and
map calculations certify consequences of those inputs, not their chain-level
proofs. The larger archive is version `v126.1.cw210`, Zenodo record14475507;
its proof archive is a separate 601,327,599-byte download.

The first two native-engine branch attempts failed while loading at the 4 GiB
address-space limit (`std::bad_alloc` after25.8s and22.3s, process exit -6), before
the first seed was applied. They are not consistency checks. The coordinator
then authorized one native process at a time with a 12 GiB address-space limit
and a 180-second limit per command. Both private-copy branch experiments ended
with the following results:

| Command | Raw d11=0 branch | Raw d11=z branch |
| --- | --- | --- |
| Add sphere h6^2 permanence | exit0,31.1s | exit0,40.1s |
| Add the selected raw d11 value | exit0,25.3s | exit0,23.4s |
| Global diff_v2 propagation | exit0,137.4s | exit0,130.3s |
| Global synthetic propagation | exit0,46.1s | exit0,44.5s |
| Focused differential search | timeout180s | timeout180s |

Exact commands, assumption sets, executable hash, and before/after snapshots are
in [zero-retry12-branch-results.json](zero-retry12-branch-results.json) and
[nonzero-retry12-branch-results.json](nonzero-retry12-branch-results.json).
The first four commands in each branch completed without finding a
contradiction. The last commands timed out and did not provide a completed
search or a saturation result. The archived native engine is a heuristic
research program; its old unqualified rules are not substitutes for the current
corrected mathematical hypotheses.

The saved source/target states changed only as follows in this neighborhood:

| Item | Before seeding | Raw zero branch | Raw z branch |
| --- | --- | --- | --- |
| u at C2(1,128) | unknown d11 | unknown d13 | recorded d11 to coordinate0 |
| z at C2(12,138) | no outgoing differential recorded | same | recorded incoming d11 |
| C2 d5 source i x127,7,2 | unknown d5 | same | same |
| C2 filtration6 source space | top coefficient unknown d3; bottom unknown d5 | same | same |
| Ctheta5sq top [125] | unknown d10 | same | same |

Adding only h6^2 permanence did not settle the earlier d5/d6 target issues.
Crucially, the raw equation d11(u)=z does not assert that z is nonzero on E11:
if an earlier differential kills z, this raw value becomes zero in the page
quotient. Thus the two accepted raw inputs do not exhibit two realizable
spectral sequences with different actual nonzero differentials.

All processes started for this investigation have exited, including both timed
out child processes. No computation is left running. The two private database
copies remain under `branch-zero/` and `branch-nonzero/` for reproducibility;
the original archive was never opened for writing.

No order-two theta6 has been constructed or ruled out. The immediate mathematical
targets are the two specified early-boundary issues and then d11 on its actual
page quotient. If d11 vanishes, the remaining pages through62 require examination
before the positive bridge could be applied.
