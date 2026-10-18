---
author: blueprint-authoring
authored_source: blueprint/paper/AdamsSynthetic.tex
blueprint_label: paper:3.2
created: '2026-10-17T18:17:10'
date: '2026-10-17T18:17:10'
origin: blueprint-authoring-notes
title: Formal scope and provenance
updated: '2026-10-18T08:16:05.546404+00:00'
---
Mathematical dependency review: [AimPaper source, lines 770-772](paper/main.tex.html#L770). Define bigraded spheres by suspension of the synthetic analogue of an ordinary sphere.

The object definition belongs to AdamsSynthetic. The separate low-weight comparison isomorphisms are stated in \ref{sem:Literature:low-sphere-comparisons}; they do not formalize the all-integral definition here.

**Formal scope:** partial.

Bigraded spheres are public objects; `Smn` is defined by applying `biShift` to the unit. The comparison with $\Sigma^{s-w}\nu(S^w)$ for every integer $w$ in the paper is not supplied as a single directly exported equality or isomorphism theorem.

This entry is bound to the existing Lean declarations below. Its status reports their local completion; the scope of the paper correspondence is qualified by the preceding note.

Direct formal counterparts: `KIP126.Synthetic.Context.Smn`.

Source verification (2026-10-18): Partial source correspondence. The immutable raw statement is exactly Pstragowski’s definition as restated by AimPaper, but the direct binding here is only Smn. The three nu-sphere isomorphisms in weights 1, 2, 3 are separate Literature results. They do not establish the general all-integral formula; retain its existing partial/sketch status. Primary references: [Pst](https://arxiv.org/pdf/1803.01804v3): Definition 4.6; pages 39; arXiv:1803.01804v3, 10 November 2022

Detailed source attribution: (From [LWX126](https://arxiv.org/abs/2412.10879), Definition 3.2, quoting [Pst](https://doi.org/10.1007/s00222-022-01173-2), Definition 4.6; the current binding is partial.)