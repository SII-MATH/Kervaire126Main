---
author: blueprint-authoring
authored_source: blueprint/paper/AdamsSynthetic.tex
blueprint_label: paper:3.3
created: '2026-10-17T18:17:10'
date: '2026-10-17T18:17:10'
origin: blueprint-authoring-notes
title: Formal scope and provenance
updated: '2026-10-17T18:17:10'
---
**Formal scope:** partial.

The natural transformation $\lambda$ is the field `SyntheticCategory.lam`, and the quotient objects are public. A complete public comparison theorem covering both the construction of $\lambda$ from the comparison map for $\nu$ and the equivalence $X/\lambda\simeq(S/\lambda)\wedge X$ has not yet been supplied.

This entry is bound to the existing Lean declarations below. Its status reports their local completion; the scope of the paper correspondence is qualified by the preceding note.

Bound declarations (private names are resolved through stable source references, without changing their visibility):

\begin{itemize}

\item `KIP126.Synthetic.Context.SyntheticCategory`: [implementation](implementation/index.html#decl:5dcf33287750315a)

\item `KIP126.Synthetic.Context.lambdaPow`: [implementation](implementation/index.html#decl:6a8ce148634e58e6)

\item `KIP126.Synthetic.Context.XModLambda`: [implementation](implementation/index.html#decl:a0f2a285d56161c8)

\item `KIP126.Synthetic.Context.XModLambdaN`: [implementation](implementation/index.html#decl:6447fe7926ae97c5)

\end{itemize}