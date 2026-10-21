---
author: blueprint-authoring
authored_source: blueprint/chapters/ProofTools.tex
blueprint_label: sem:ProofTools:cprime
created: '2026-10-20T15:49:27'
date: '2026-10-20T15:49:27'
origin: blueprint-authoring-notes
title: Formal scope and provenance
updated: '2026-10-21T06:13:14.838984+00:00'
---
Mahowald--Leibniz composition under finite-layer surjectivity is a project-derived classical assertion. The fixed-model proposition FiniteLayerSurjectivityMahowaldLeibnizStatement is proved internally by finite_layer_surj_statement, retaining the two actual input differentials and every surjectivity layer. Its output uses the selected normalized first-quotient operation. Identifying that operation with the Ext boundary of the same homology short exact sequence remains a separate comparison. The private proof inherits registered upstream construction and comparison obligations; it is not a new public interface or a direct Lean binding for this Ext-formulated theorem.