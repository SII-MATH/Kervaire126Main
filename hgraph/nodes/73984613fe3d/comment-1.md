---
author: blueprint-authoring
authored_source: blueprint/paper/ProofTools.tex
blueprint_label: paper:2.12
created: '2026-10-17T18:17:10'
date: '2026-10-17T18:17:10'
origin: blueprint-authoring-notes
title: Formal scope and provenance
updated: '2026-10-18T08:16:05.570094+00:00'
---
Mathematical dependency review: [AimPaper source, lines 483-505](paper/main.tex.html#L483). Use the representative criterion to choose a common source and transport its images around the commutative square.

**Formal scope:** partial; no direct public binding.

The existing theorem `square\_frames` works in one convergent synthetic tower, using actual representatives on the four edges and no-crossing synchronization. It covers the special case in which the target edge also has no crossing. The general chase under the weaker $k$-range condition of the paper, and the comparison with a general classical $f$-extension spectral sequence, remain unavailable.

Original statement and context: paper/main.tex.html#L461; paper/2412.10879.pdf.

The private representative-frame lemma is an internal proof step, not a direct public counterpart of this statement. It remains in the Lean source; this paper entry has no Lean binding.