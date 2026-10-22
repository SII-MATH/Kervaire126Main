---
author: blueprint-authoring
authored_source: blueprint/chapters/Main.tex
blueprint_label: paper:1.4
created: '2026-10-17T18:17:10'
date: '2026-10-17T18:17:10'
origin: blueprint-authoring-notes
title: Formal scope and provenance
updated: '2026-10-21T15:04:38.152500+00:00'
---
The local argument retains its actual upstream dependencies; the final theorem is fully closed only when those dependencies are closed.

Mathematical dependency review: [AimPaper source, lines 2212-2214](paper/main.tex.html#L2212). The last-differential dichotomy and the incompatibility of conditions (3) and (5) imply permanence. Theorem 7.1 repeats this target, not an independent prerequisite.

**Formal scope:** Public correspondence.

The sole public theorem takes the nonzero standard-class family H on the fixed sphere system. The fixed Milnor family is one instance. Uniqueness in bidegree (1,64) identifies H_6 with the fixed h_6, so this family formulation expresses the same permanence target as Theorem 7.1 and retains a common permanent representative with nonzero limiting image. Identification of the fixed background with the paper's 2-completed system remains upstream.

Formal counterparts: `KIP126.Main.h6\_sq\_permanent`.

The original paper presents this conclusion twice. A single displayed node carries paper:1.4 and paper:7.1 as aliases, with one set of dependencies and consumers. Both original statements remain checked verbatim.

Original statements: [Theorem 1.4](paper/main.tex.html#L128), [Theorem 7.1 and its proof](paper/main.tex.html#L2106); article PDF: paper/2412.10879.pdf.