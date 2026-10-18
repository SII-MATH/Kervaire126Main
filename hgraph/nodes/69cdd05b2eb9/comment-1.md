---
author: blueprint-authoring
authored_source: blueprint/paper/Literature.tex
blueprint_label: paper:3.20
created: '2026-10-17T18:17:10'
date: '2026-10-17T18:17:10'
origin: blueprint-authoring-notes
title: Formal scope and provenance
updated: '2026-10-18T08:16:05.556189+00:00'
---
Mathematical dependency review: [AimPaper source, lines 946-971](paper/main.tex.html#L946). Rewrite the lifted triangle using the normalized maps and their filtration-shift convention; rotations cover the three possible positions.

**Formal scope:** partial

The implementation constructs a normalized triangle and a cofiber comparison for its normalized first arrow. There is no general public theorem deducing that the three prescribed normalized arrows form a distinguished triangle merely from their exponent sum being one. NormalizedTriangleCompatible is a proposition recording the required condition; defining it does not deliver that conclusion.

Direct formal counterparts: `KIP126.Literature.Standard.normalizedTriangle`, `KIP126.Literature.Standard.normalized\_cofiber`.

Source verification (2026-10-18): Partial source correspondence. Keep the original raw block unchanged. The source assumes exponent sum one and uses shifted vertices. The current binding includes a cofiber-comparison obligation and a distinguishedness predicate, not a theorem for the three already selected normalized arrows. Retain partial/sketch status. Primary references: [LWX126](https://arxiv.org/abs/2412.10879): Notation 3.19; Proposition 3.20; pages 19; Repository-frozen AimPaper/main.tex and AimPaper/2412.10879.pdf

Detailed source attribution: (From [LWX126](https://arxiv.org/abs/2412.10879), Proposition 3.20; the current binding is partial.)