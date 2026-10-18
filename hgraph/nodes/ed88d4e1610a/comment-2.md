---
author: blueprint-authoring
authored_source: blueprint/paper/ProofTools.tex
blueprint_label: paper:6.1
created: '2026-10-17T18:17:10'
date: '2026-10-17T18:17:10'
origin: blueprint-authoring-notes
title: Formal scope and provenance
updated: '2026-10-18T08:22:54.270779+00:00'
---
Mathematical dependency review: [AimPaper source, lines 1623-1656](paper/main.tex.html#L1623). Translate the hypotheses into synthetic extensions, transfer the no-crossing conditions, apply the square corollary, and translate the resulting boundary extension back.

**Formal scope:** public counterparts; scope is specified below.

The public proposition and callable theorem retain the no-crossing hypotheses, degrees, and page ranges. The API currently records a direct proof obligation for the theorem. The proved left edge is now used in both branches, and the minimal bottom-length case is discharged whenever the source no-crossing input comes from the classical boundary or minimal finite length. Both remaining holes concern the crossing inputs; no additional obligation is introduced.

Partial local proof in GeneralizedLeibniz/CrossingLift: a divided source whose image has the required filtration supplies a finite extension witness at any allowed length. The finite lambda target grade vanishes precisely modulo the boundary submodule B_{1+t-(w-k)}; the untruncated bottom-label version gives B_{k+1}. Essentiality reflects from a mapped extension through a commuting square. The separate private left-edge proof now matches the specified finite source with the propagated infinite source, including normalized shifts and lambda compatibility, without extra hypotheses. These steps do not establish simultaneous source/image filtration lifting or either general no-crossing conversion, and neither GL proof hole has been discharged.

The finite lambda square now supplies the full crossing conclusion from a smaller witness whose lambda source supports the prescribed large-quotient essential extension. Both essentiality of the smaller witness and the exact boundary exclusion are proved, with page and length bounds checked. Existence of such a smaller witness with the required source and image filtrations remains unfinished under the original printed hypotheses. The separate finite lambda division theorem supplies it under the added target-kernel crossing condition; it does not discharge the original Proposition cross-f-Er or GL.

The 2026-10-18 review exhibits an actual-spectrum counterexample to the general crossing comparison and to the printed GL statement. For E = HZ_2 and T = H(Z/4), the map T + E to Sigma E + T + E given by (delta,j,2), with page = r = 2, m = 0 and l = 2, satisfies the printed hypotheses but would force a nonzero d_4 from a permanent HZ class. The independent Adams inputs are Lemmas 3 and 4, p. 129 of [MayMilgramBockstein1981](https://math.uchicago.edu/~may/PAPERS/34.pdf); the synthetic comparison and convergence inputs are in Appendix A of [BHS](https://doi.org/10.4310/acta.2023.v231.n2.a1). Low-filtration lambda torsion prevents simultaneous source/image lifting. This is a mathematical general-spectrum counterexample, not a realization in the fixed Lean ClassicalObject closure. The frozen GL interface and its two proof holes remain unchanged; strengthening its crossing premises with actual same-quotient, same-weight conditions requires explicit review and approval. See corrections.yaml and the archived 20261018 GL/crossing review for the full hypotheses and evidence.

A subsequent independent review gives a sphere/shift mathematical counterexample using sigma from S^7 to S^0, page = r = 2, m = 1, l = 3, s = 2, t = 19, three zero source labels and target Pc_0. Proposition A.20, relations (11) and (15), of [BHS](https://doi.org/10.4310/acta.2023.v231.n2.a1) give sigma times lambda Ph_1 = lambda^2 Pc_0; the source represents zero in its specified grade. The full low-stem ring excludes every possible crossing, with h_1^2 d_0 excluded by the d_2(e_0) boundary. The original data in [IWXCharts](https://zenodo.org/records/6987157) independently verify the degrees, boundary and nonzero survival of Pc_0, so the conclusion d_4(0) = Pc_0 is false. The isolated weight 24 in the BHS generator table is explicitly corrected to 23 using its own figures, homogeneous relations and the classical data. This example belongs to the intended sphere object closure, but the comparisons with the deferred fixed Lean model have not been formalized. The independent review does not authorize a public interface change.

A separate level-indexed theorem, now exported through the public entry point, follows the paper's square proof with classical page n, arbitrary lambda level k >= 0, quotient exponent q = n+k-1, and weight w = t+e(f)-k. Its finite input is the actual extension from lambda^k x to lambda^(k+m-e(f)) y; the original infinite input is propagated to bottom level r-n. Absence of essential crossing is required on either the actual left edge or the actual top edge, and also on the actual bottom edge at that same weight. Finite lambda multiplication proves the left edge, and the weighted reverse boundary comparison gives the original classical differential d_(r+l-m)(y) = y_infty. A private zero-level witness comparison relates this language to the original finite extension. These level results have no local proof gaps but retain registered upstream obligations. They do not prove the frozen public statement or change its binding, crossing predicates, or two remaining proof holes.

This entry is bound to the existing Lean declarations. Its status reports their local completion; the scope of correspondence with the article is specified above.

Direct formal counterparts: `KIP126.ProofTools.Standard.generalizedLeibniz`.

The original article number is 6.1; other numbering is generated by the blueprint. Throughout the article, spectra are assumed to be 2-completed, connective, and of finite type. Read this statement together with its original context.

\href{paper/main.tex.html#L1606}{Original statement, hypotheses, and context} · \href{paper/2412.10879.pdf}{Article PDF}