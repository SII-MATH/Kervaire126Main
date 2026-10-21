---
author: blueprint-authoring
authored_source: blueprint/chapters/ProofTools.tex
blueprint_label: sem:ProofTools:ss-image-certificate
created: '2026-10-21T07:20:01'
date: '2026-10-21T07:20:01'
origin: blueprint-authoring-notes
title: Formal scope and provenance
updated: '2026-10-21T07:20:01'
---
Fixed source: ss/category.cpp:541--710. Ordinary leaf: 559--564; recursive nonzero-image branch: 569--595; zero-image branch and immediate status stop: 598--622; target and kernel conditions: 624--671; crossing clauses: 673--705. The sole immediate failure allowed by the crossing loop is return 12, not wrapped recursive failures. At line 696 a nonzero candidate lying in U is rejected; reversing that membership would change the rule.

**Formal scope:** This is an unbound mathematical definition of the tested finite data. It neither asserts a given-label synthetic extension for every successful node nor supplies the normalization and label comparisons needed for such an assertion.