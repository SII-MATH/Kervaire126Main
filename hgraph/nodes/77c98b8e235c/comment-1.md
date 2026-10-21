---
author: blueprint-authoring
authored_source: blueprint/chapters/ProofTools.tex
blueprint_label: sem:ProofTools:ml-finite-core
created: '2026-10-21T05:06:27'
date: '2026-10-21T05:06:27'
origin: blueprint-authoring-notes
title: Formal scope and provenance
updated: '2026-10-21T06:13:14.837302+00:00'
---
**Formal scope:** The complete fixed-model classical-input core is proved internally by finite_quotient_mahowald_leibniz_core. Its three exhaustive normalization cases retain the original triangle, construct the specified-label Bockstein lift and actual May representative, prove u is a K-cycle, and give the exact image of every same-label representative under (A). The actual shift comparisons and signed top target are retained in each case; finite_may_signed_target_eq_top_at_level identifies that actual target with the single highest-layer inclusion, using highest-layer uniqueness. These private proofs inherit registered upstream obligations and have no public Blueprint binding.