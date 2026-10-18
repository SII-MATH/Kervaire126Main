---
author: blueprint-authoring
authored_source: blueprint/paper/Literature.tex
blueprint_label: paper:6.11
created: '2026-10-17T18:17:10'
date: '2026-10-17T18:17:10'
origin: blueprint-authoring-notes
title: Formal scope and provenance
updated: '2026-10-18T04:35:45.864357+00:00'
---
**Formal scope:** public correspondence with the scope stated below

The public data deliver the May push-pull diagram and its signed boundary comparison. Removing the sign still requires the stated exponent-two condition.

\item `KIP126.Literature.Standard.may\_pushpull`: [implementation](implementation/index.html#decl:9f9bafae3ac3e1f5)

\item `KIP126.Literature.Standard.may\_signed\_boundary`: [implementation](implementation/index.html#decl:a7f38634d33d0a16)

\item `KIP126.Literature.Route.MayPushpullData`: [implementation](implementation/index.html#decl:2062b7fbc95c00d1)

Source verification (2026-10-18): Partial source correspondence. Keep the original raw block unchanged. May’s TC3 boundary equality has a minus sign; Lean may_signed_boundary preserves it. The unsigned equality printed in AimPaper Lemma 6.11 is only justified after an exponent-two image condition or compatible sign convention is supplied. F2 Adams-page coefficients alone do not imply this condition. Primary references: [May01](https://www.math.uchicago.edu/~may/PAPERS/AddJan01.pdf): Axiom TC3; Lemma 4.6; pages 12–14; Author-hosted January 2001 preprint, 31 pages; numbered statements retain published numbering

Detailed source attribution: (From [LWX126](https://arxiv.org/abs/2412.10879), Lemma 6.11, based on [May01](https://doi.org/10.1006/aima.2001.1995), Axiom TC3 and Lemma 4.6; the general boundary identity is signed.)