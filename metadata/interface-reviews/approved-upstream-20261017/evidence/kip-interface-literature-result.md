# Literature interface worker result

- Baseline HEAD: `2c703812db7edb830b995c53e9fe648747a66429`.
- Owned production file: `KIP126/Literature/Standard.lean` only.
- Baseline file SHA-256: `f73c1ad8b6fda516b8fac98758492b67e258e4692ce280b11719d6922f114377`.
- Result file SHA-256: `8ba89e65cd91d11783ea3aa08fc83f5891337c1f7aaa6e8abfb39ae440072bd6`.
- Read repository AGENTS.md and supplied protocol.md. No metadata, locks, tests, shared build cache, or other production files changed.

## Applied: tmf_convergence approved public implementation

The complete `section TmfConvergenceTransport` is byte-for-byte the corresponding section of `metadata/interface-reviews/Literature/20261017-01-tmf-convergence-exposure/evidence/Standard-public-candidate.lean`.

The former private `tmfConvergenceActualTransport` body is now the public `tmf_convergence` body at line 252; the old public `sorry` duplicate is removed. No change to its type, object, universe, or exposed attribute. This restores precisely the public implementation whose 19 `_proof_1` … `_proof_19` exports were authorized. Fresh export checking must still confirm this against current imports.

No direct sorry remains in this section. The file's textual sorry count drops 108 → 107. No target self-reference or use of `stem62_exponent_two` occurs in the transport body. Existing evidence records 33 transitive pending dependencies (31 AdamsSynthetic, `Standard.tmf`, `Standard.tmfIso`); these remain pending and must not be counted as solved.

## Blocked: stem62 signature and theta5_order_two proof

The approved scheme A is the exact signature change:

```lean
public theorem stem62_exponent_two :
  ∀ a : HomotopyGroup (C := Spectrum) 62 SphereSpectrum,
    (∃ n : ℕ, (2 ^ n : ℕ) • a = 0) → a + a = 0 := by
  sorry
```

This would preserve the existing stem62 direct pending responsibility. However the next public theorem currently has the only proof:

```lean
public theorem theta5_order_two :
  theta5 + theta5 = 0 := stem62_exponent_two theta5
```

With the approved signature its body has type
`(∃ n : ℕ, (2 ^ n : ℕ) • theta5 = 0) → theta5 + theta5 = 0`, not the target. A true independent proof of the premise is absent from current available fixed-object interfaces. The assigned task expressly forbids a new sorry, axiom, responsibility, circular proof, or additional public premise. Therefore the production stem62 signature has NOT been changed in this worker patch: changing it alone leaves the owned production file ill-typed. Exact unapplied signature diff is `/tmp/kip-interface-literature-stem62-signature.diff`.

Evidence:

- `theta5` at line 168 is an opaque pending fixed homotopy class, with no constructive 2-primary source in its current body.
- `theta5_detection` at line 179 only asserts `ClassicalTheta5Detected`; definition `KIP126/Literature/Classical.lean:60` is the mod-2 classical detection relation, without a 2-primary premise.
- `theta5_filtration_gap` only compares detected representatives in filtration 6; it does not provide an integral 2-primary decomposition or remove odd summands.
- `theta5_lift` at line 1723 is derived from prescribed realization lifting and detection; it has no order-two conclusion for its arbitrary supplied lift.
- `bx_order_two` at line 1758 concerns a distinct fixed synthetic class `bxTheta5`; no equality identifies its realization with `theta5`. Substituting it changes the specified object.
- The private `ClassicalResults.theta5_order_two` in `Classical.lean:139` only projects its old arbitrary exponent-two input; it is a conditional helper with no constructed fixed instance. It is not independent proof evidence.
- Report `20261017-01-stem62-integral-exponent/report.md:151-172` explicitly identifies this same prerequisite and warns that detection alone does not settle odd-primary indeterminacy.

This is a precise current-proof blockage, not a proof that the chosen theta5 cannot have order two. Coordinator needs either an actual independent selected-theta5 comparison/order-two proof or an explicit authorized responsibility repair; do not silently apply the invalid old body after narrowing stem62.

## Actual checks

- Python structural check: exact complete public candidate transport section: PASS.
- Python check: no direct `sorry` in transport, private duplicate removed: PASS.
- SHA-256 and git diff reviewed: changes confined to authorized file and tmf subsection.
- No Lean or Lake execution by this worker, as requested while coordinator repairs execution environment and schedules shared outputs.
- Full source inventory, current kernel/type check, 19-export exact comparison, old signatures comparison, trust capture and lake build remain for coordinator.

## Subsequent coordinator-approved isolated validation

Command actually run via escalation with fixed toolchain, writing only `/tmp` outputs:

```sh
/root/.elan/toolchains/leanprover--lean4---v4.32.2/bin/lake env lean \
  -o /tmp/kip-interface-literature-Standard.olean \
  -i /tmp/kip-interface-literature-Standard.ilean \
  KIP126/Literature/Standard.lean
```

Exit 1 before type checking the owned file: the concurrently introduced upstream module `KIP126.AdamsSynthetic.Standard.ClassicalSupport` lacks its compiled `.lake/build/lib/lean/KIP126/AdamsSynthetic/Standard/ClassicalSupport.olean`. Exact log: `/tmp/kip-interface-literature-lean.log`. This is an import-build blockage, not evidence that the candidate body type checks in current state.

Full combined candidate file (tmf body + approved stem62 signature, with old theta5 body preserved to make the exact missing proof visible): `/tmp/kip-interface-literature-Standard-candidate.lean`.
Full combined patch against baseline HEAD: `/tmp/kip-interface-literature-complete-candidate.patch`.
This combined candidate is intentionally not claimed to compile: theta5_order_two is missing the new 2-primary premise. Production remains tmf-only until the coordinator decides how to handle this authorized signature change and the pre-existing derived proof gap.
