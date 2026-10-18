---
author: blueprint-authoring
authored_source: blueprint/paper/ProofTools.tex
blueprint_label: paper:2.15
created: '2026-10-17T18:17:10'
date: '2026-10-17T18:17:10'
origin: blueprint-authoring-notes
title: Formal scope and provenance
updated: '2026-10-18T06:58:29.995864+00:00'
---
**Formal scope:** partial; no direct public binding.

The private theorem `square\_frames` supplies a commutative four-edge square with synchronized representatives; its conclusion identifies the image along the right edge with the lower-right representative. The present model uses `TowerExtensionEquation` and `TowerNoCrossing` in a convergent synthetic tower. The bridge to the general classical $f$-extension spectral sequence of the paper remains a separate obligation.

Original statement and context: paper/main.tex.html#L555; paper/2412.10879.pdf.

The private representative-frame lemma is an internal proof step, not a direct public counterpart of this statement. It remains in the Lean source; this paper entry has no Lean binding.