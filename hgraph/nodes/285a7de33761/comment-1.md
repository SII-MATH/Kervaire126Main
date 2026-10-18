---
author: blueprint-authoring
authored_source: blueprint/paper/AdamsSynthetic.tex
blueprint_label: paper:3.3
created: '2026-10-17T18:17:10'
date: '2026-10-17T18:17:10'
origin: blueprint-authoring-notes
title: Formal scope and provenance
updated: '2026-10-18T06:58:29.969476+00:00'
---
The synthetic category and its comparison map are background. This definition binds the single-lambda quotient object; higher-power quotients are defined separately in \ref{sem:AdamsSynthetic:lambda-quotients}.

**Formal scope:** partial.

The natural transformation $\lambda$ is the field `SyntheticCategory.lam`, and the quotient objects are public. A complete public comparison theorem covering both the construction of $\lambda$ from the comparison map for $\nu$ and the equivalence $X/\lambda\simeq(S/\lambda)\wedge X$ has not yet been supplied.

This entry is bound to the existing Lean declarations below. Its status reports their local completion; the scope of the paper correspondence is qualified by the preceding note.

Direct formal counterparts: `KIP126.Synthetic.Context.XModLambda`.