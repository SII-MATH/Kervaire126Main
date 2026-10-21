---
author: blueprint-authoring
authored_source: blueprint/chapters/ProofTools.tex
blueprint_label: sem:ProofTools:ss-cutoff-square-specialization
created: '2026-10-21T09:07:44'
date: '2026-10-21T09:07:44'
origin: blueprint-authoring-notes
title: Formal scope and provenance
updated: '2026-10-21T11:29:00.632843+00:00'
---
This is the mathematical cutoff square suggested by SetCwDiffSynthetic, category.cpp:497--515. The code's logged k is the cutoff kappa, not the lambda level k of this proposition. No assertion here turns a recorded zero range into the required crossing-free right-edge extension.

**Formal scope:** The public theorem proves the actual quotient-boundary conclusion at every level with its complete mathematical hypotheses. The exponent and range calculations are private auxiliary steps, not extra conclusion bindings.