---
author: metadata-migration
created: '2026-10-17T17:47:44'
date: '2026-10-17T17:47:44'
owner_module: ProofTools
scope_id: proof-tools-generalized-leibniz
title: 'Interface scope: proof-tools-generalized-leibniz'
updated: '2026-10-17T17:47:44'
---
Scope of the related interface family `proof-tools-generalized-leibniz`. This note does not assert equivalence with a broader paper statement or mark any proof complete.


- **mathematical_purpose**: 实际三边交换图已在GL1/GL2主证明中组装出同一个右边代表及边界，底边规定目标标签、存活和经典微分的加权读出已证明；左边规定源类匹配已由私有引理完成，仍需一般无交叉转换。

Local crossing-lift progress (2026-10-18): the source lambda division now
retains its actual normalized image equation in the same naturality square.
Given the required image filtration in the smaller quotient, a private
construction supplies a finite extension witness at every allowed length.
The finite lambda target's higher-filtration criterion is exactly membership
in `B_(1+t-(w-k))`; the untruncated bottom-label criterion is membership in
`B_(k+1)`. Essentiality reflects from an image extension through a commuting
square. The separate private left-edge proof now connects the specified
finite source to the specified propagated infinite source, with normalized
shift and lambda compatibility proved internally and no extra assumptions.
Simultaneous source/image filtration lifting and the general crossing
conversions remain unresolved for the frozen interface. The two original
GL proof holes and the public interface are unchanged.

The finite descent has also been assembled at the witness level: a smaller
witness whose actual lambda source supports the given large-quotient
essential extension yields `FiniteHasCrossing`, including the smaller
witness's essentiality, the exact boundary exclusion, and the page/length
bounds. The actual finite lambda infinity map is compared with the fixed
Literature comparison. The unresolved existence step still has to produce
that smaller witness with both required filtrations; no general crossing
conversion or GL completion is claimed.

Independent review (2026-10-18) found an actual-spectrum counterexample to
the paper's general crossing comparison and to the printed GL statement.
The example uses HZ_2, H(Z/4), their finite sums and the actual quotient and
connecting maps. At page = r = 2, m = 0 and l = 2, all printed hypotheses
hold while the conclusion would require a nonzero d_4 from a permanent
HZ class. The low-filtration lambda-torsion obstruction survives division
even though its lambda image vanishes. The complete construction and
independent source checks are recorded in MEMO.md and
`local-history/metadata/interface-reviews/ProofTools/20261018-gl-crossing-lambda-lift/report.md`.
The example has not been realized in the fixed ClassicalObject closure;
the current Lean GL interface has not been formally refuted. Its interface
and two original proof holes remain unchanged. A GL-specific strengthening
that retains the original premises and adds actual same-quotient, same-weight
synthetic conditions is proposed for human review; no semantic change is approved.


Paper locators: thm:e73f481e:1606.


Code provenance: [KIPSourcebbac1fc05843](https://github.com/SII-MATH/Kervaire126/tree/bbac1fc05843bdf2d56057e6114a38839e939378). Exact original source blocks and migration history remain in `local-history/metadata/proof-tools-sources.json`.
