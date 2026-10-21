---
author: blueprint-authoring
authored_source: blueprint/chapters/ProofTools.tex
blueprint_label: sem:ProofTools:ss-partial-adams-data
created: '2026-10-21T07:20:01'
date: '2026-10-21T07:20:01'
origin: blueprint-authoring-notes
title: Formal scope and provenance
updated: '2026-10-21T07:20:01'
---
Fixed source: ss/main.h:20--25; ss/staircase.cpp:58--101; ss/ss.cpp:13--42 and :193--242; src/linalg.cpp:86--210. In particular, the image-membership assertion in GetImage is debug-only. The comparison of the recorded flag with actual Z/B data is part of the soundness problem, not an additional input containing the desired outputs.