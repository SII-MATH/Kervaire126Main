---
author: blueprint-authoring
authored_source: blueprint/paper/Literature.tex
blueprint_label: paper:6.11
created: '2026-10-17T18:17:10'
date: '2026-10-17T18:17:10'
origin: blueprint-authoring-notes
title: Formal scope and provenance
updated: '2026-10-18T08:16:05.557033+00:00'
---
Mathematical dependency review: [AimPaper source, lines 1755-1777](paper/main.tex.html#L1755). May's external tensor-triangulated push-pull result supplies the smash-product diagram; its boundary identity is not proved by a later Mahowald application.

**Formal scope:** public correspondence with the scope stated below

The public data deliver the May push-pull diagram and its signed boundary comparison. Removing the sign still requires the stated exponent-two condition.

Direct formal counterparts: `KIP126.Literature.Standard.may\_pushpull`, `KIP126.Literature.Standard.may\_signed\_boundary`.

Source verification (2026-10-18): Partial source correspondence. Keep the original raw block unchanged. May’s TC3 boundary equality has a minus sign; Lean may_signed_boundary preserves it. The unsigned equality printed in AimPaper Lemma 6.11 is only justified after an exponent-two image condition or compatible sign convention is supplied. F2 Adams-page coefficients alone do not imply this condition. Primary references: [May01](https://www.math.uchicago.edu/~may/PAPERS/AddJan01.pdf): Axiom TC3; Lemma 4.6; pages 12–14; Author-hosted January 2001 preprint, 31 pages; numbered statements retain published numbering

Detailed source attribution: (From [LWX126](https://arxiv.org/abs/2412.10879), Lemma 6.11, based on [May01](https://doi.org/10.1006/aima.2001.1995), Axiom TC3 and Lemma 4.6; the general boundary identity is signed.)