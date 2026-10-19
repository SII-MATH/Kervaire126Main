---
author: blueprint-authoring
authored_source: blueprint/semantic/Main.tex
blueprint_label: sem:Main:weak-representative-route
created: '2026-10-18T14:03:28'
date: '2026-10-18T14:03:28'
origin: blueprint-authoring-notes
title: Formal scope and provenance
updated: '2026-10-19T06:19:35.682708+00:00'
---
Fixed upstream source versions: [KIPSourcebbac1fc05843](https://github.com/SII-MATH/Kervaire126/tree/bbac1fc05843bdf2d56057e6114a38839e939378). Interface scope notes are retained as native hgraph node comments; historical migration records are local archives.

The local argument retains its actual upstream dependencies; the final theorem is fully closed only when those dependencies are closed.

This entry states the same incompatibility conclusion as paper:7.9 and binds its existing public Main theorem. The remaining text explains its retained proof, without binding private helpers. The user retained this route after the upstream fidelity review. The two original conditional statements at paper:7.16 and paper:7.18 are now proved from this independently established incompatibility. Their direct local Toda and unmultiplied extension arguments are not asserted here. Main's local assembly still inherits the registered upstream obligations. A separate audit proved the complete fixed-model filtration--lambda comparison signature from existing upstream inputs, without using that target or Main, but its production proof remains pending. No public interface or fixed object was changed, and no mathematical novelty claim is made.