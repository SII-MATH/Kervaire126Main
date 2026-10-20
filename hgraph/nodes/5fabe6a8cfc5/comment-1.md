---
author: blueprint-authoring
authored_source: blueprint/chapters/Literature.tex
blueprint_label: sem:Literature:closed-framed-manifolds
created: '2026-10-18T11:19:44'
date: '2026-10-18T11:19:44'
origin: blueprint-authoring-notes
title: Formal scope and provenance
updated: '2026-10-20T04:59:49.855931+00:00'
---
Fixed upstream source versions: [KIPSource5aa845241533](https://github.com/SII-MATH/Kervaire126/tree/5aa845241533b763c37a1d5fc70cce9708c4e68e), [KIPSourcebbac1fc05843](https://github.com/SII-MATH/Kervaire126/tree/bbac1fc05843bdf2d56057e6114a38839e939378). Interface scope notes are retained as native hgraph node comments; historical migration records are local archives.

These are actual mathlib manifold and smooth vector-bundle data, with no construction holes. Their representations are module-private: ordinary imports expose the three geometric object types without changing the analytic instance environment of the older modules. A full-body representation audit verifies the actual compactness, smoothness and frame data and their independence from project spectral objects. The stable tangent/normal comparison needed by the literature theorem belongs to the pending Browder input.