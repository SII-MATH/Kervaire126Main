# graded_compose approved interface implementation

Baseline HEAD: `2c703812db7edb830b995c53e9fe648747a66429`.
Baseline `KIP126/AdamsSynthetic/Standard/Operations.lean` SHA-256: `63bb1c57b1bc949af0553c8baebc6e4ef95090be38594e0a83b26e9f837ad1d0`.
Final SHA-256: `252cb6eaaed020bda17f6671b68205b43a21b7d450e9e59a7cdd13e9c385d59c`.

Only assigned production file Operations.lean modified. No metadata, tests, registry, lock, Lake shared output, or other source file changed by this worker.

## Actual completion

- Apply report C: only public `graded_compose` is marked `@[no_expose]`; ordinary consumers use its declared polynomial bilinearity and `graded_compose_homogeneous` law.
- Both `graded_compose` and `graded_compose_homogeneous` now have complete implementations with no direct sorry. The private construction extends actual shifted composition over the weight direct sum, proves associativity and centrality of lambda, and promotes the additive map to polynomial bilinearity.
- Preserve `graded_module` and `graded_lambda_smul` code verbatim.
- Explicitly preserve `graded_compose._proof_1` at its original name, universe list `[]`, and exact kernel type fingerprint `13301073175485286128`. The long explicit SMul instance projections deliberately preserve the original kernel representation. A letI type, or differently inferred semiring parent projection, would only be definitionally equal and would change the locked fingerprint.
- Add `import all KIP126.AdamsSynthetic.Enrichment` for its existing private homogeneous associativity/regrading helpers. This is same-module internal use permitted by AGENTS; no responsibility or public export moves.
- Avoid broad simp on public weightHomComp and weightHomInclusion so no lazy eq_1 exports appear.

## Validation actually performed

`lake env lean /tmp/KipComposeApproved.lean` with the fixed Lean v4.32.2 toolchain, escalation required because sandbox loader cannot start the toolchain, exited 0. This is an exact source replay with one extra `import Lean` and diagnostic commands only. No `-o` used; no shared build outputs written. Output `/tmp/kip-compose-approved.log`.

Capture `/tmp/kip-compose-approved-exports.json` compares all 873 currently imported/exported AdamsSynthetic declarations against both named and generated sections of the existing lock: zero additions, zero type/universe changes, no missing declaration owned by Operations. It is an Operations replay, not a full root ordinary-consumer capture, and does not assert that all 1825 root exports have been enumerated here. Summary `/tmp/kip-compose-approved-summary.json`.

`graded_compose` fingerprint `8046296169434938693`, homogeneous theorem fingerprint `8232704509103874837`, original helper fingerprint `13301073175485286128`, all unchanged; all three report direct_sorry=false.

Existing downstream `gradedEnrichment`, `graded_associative`, `graded_left_unit`, `graded_right_unit` are included in the successful source replay. Remaining existing declarations with sorry emit the expected warnings; this is not a sorry-free module claim.

## Dependencies and limits

The proof consumes the fixed synthetic category/background, exactness.shiftAdditive, quotients.coherence and its homogeneous shifted-composition laws, actual lambda naturality, the already implemented polynomial module, and mathlib direct-sum/module lemmas. The old report identified syntheticCofiber and quotients in the transitive closure; these background responsibilities remain upstream. No use of the disputed ordinary-sphere separation or exponent-two statement, no False.elim, no circular use of gradedEnrichment or its derived associativity, no new axiom, assumption, result package, or unproved responsibility.

Full ordinary root consumer, all-module export/privacy/trust audits, source inventory and complete lake build remain with the coordinator, as assigned. This worker did not run lake build, edit metadata, commit, or publish.


## Follow-up: full-root Synthetic namespace lazy congr export fixed

Coordinator full-root public capture discovered an additional `KIP126.Synthetic.Context.biShiftAddIso.congr_simp` outside the AdamsSynthetic namespace inspected by the first 873-entry diagnostic. That initial subset audit was insufficient to establish the whole root export condition.

A sequential diagnostic identified first creation in private `totalComp`, then after fixing it in `totalComp_lambda_central`. Both arose from simp traversing concrete shift isomorphism arguments. Replaced four additive-field simp traversals with explicit rewrites, and replaced the centrality simplifier with repeated associativity rewrites and direct inverse/hom cancellation. No option changes, filters, or lock changes.

Final Operations SHA-256: `b170aa7f3c878d4b79b11a911fcf149e01a76d16a8d5403a45ac5ae463ec9f00` (supersedes the previous final hash).

`lake env lean /tmp/KipComposeCongrTrace.lean` exited 0. This replay removes comments and adds diagnostic commands before declarations; every marker, including END after all Operations declarations, reports the exported `biShiftAddIso.congr_simp` absent. Log: `/tmp/kip-compose-congr-trace.log`. The actual final whole-root capture remains assigned to the coordinator; this diagnostic only establishes this particular accidental declaration is no longer created by Operations.
