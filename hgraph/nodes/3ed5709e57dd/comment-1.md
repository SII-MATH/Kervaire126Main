---
author: blueprint-authoring
authored_source: blueprint/chapters/Literature.tex
blueprint_label: paper:1.3
created: '2026-10-17T18:17:10'
date: '2026-10-17T18:17:10'
origin: blueprint-authoring-notes
title: Formal scope and provenance
updated: '2026-10-20T04:59:49.866050+00:00'
---
Mathematical dependency review: [AimPaper source, lines 117-126](paper/main.tex.html#L117). Browder is an external input; standard Adams classes and permanence specify its criterion, rather than proving the geometric bridge.

**Formal scope:** public correspondence; external proof and fixed-model comparison pending.

Source: Browder, Theorem 7.1, p. 178; the proof concludes on p. 184. The 4k+2 dimension convention in AimPaper is made explicit by j >= 1. The Lean conclusion uses nonzero survival of the actual standard square in the fixed 2-completed sphere Adams sequence. Its proof obligation includes the stable tangent/normal framing comparison, Pontryagin--Thom passage, 2-completion and class normalization; none is supplied by the new Geometry conclusions.