# Main shuffle reproof in the actual finite lambda quotient

Assignment scope: only `KIP126/Main/SectionSeven/AnyYShuffle.lean` and `KIP126/Main/Internal/Theta/Shuffle.lean`. Other workers own LowEta, the b class, lambda-kernel, high125 and downstream wrappers. No other production file changed by this worker in this assignment.

Baseline HEAD inherited from session: `2c703812db7edb830b995c53e9fe648747a66429`.
Initial file hashes:
- AnyYShuffle: `dbd56e9a1bcce6ffeeb579aaddd316eebded0ab35990dca6a370eb2dc6f28d18`.
- Theta/Shuffle: `f949051534e8a22d8fee72a08d15cd80f841e1677445b435435ee1b2228ff7d2`.
Final hashes:
- AnyYShuffle: `9bf2cd2522b2cf034bed9f918319922cff37a181a6c94ba0cf9536ec9e226f9a`.
- Theta/Shuffle: `7868d66a183d6ca2ba06f7104498a2e5429e14a19a31b9e2eda7d70f34fabe0c`.

## Mathematical changes actually proved

1. AnyY: remove the untruncated eta uniqueness parameter and associated source-fixing lemmas. The actual end target is `XModLambdaN S 9`; specialize the private exact shuffle to this target and use `eta_action_source_iso_fixed_in_finite_quotient 9 ...` on the iterated eta action. The raw Toda shuffle, its complete indeterminacy cancellation, the source normalization and lambda coherence remain actual constructions. Both the potentially nontrivial source automorphism and the sign are removed only in this finite quotient.

2. Theta: remove the untruncated eta uniqueness parameter. The private conclusion is now exactly the necessary finite statement
   `quotientClass 9 (lambdaMultiply 2 (sphereProduct h0 z)) = quotientClass 9 (lambdaMultiply 3 (sphereProduct eta (sphereProduct theta b)))`.
   The doubled untruncated Toda calculation still produces an automorphism; postcompose that genuine equation with `XModLambdaN.incl S 9` before removing the automorphism. Its invariance is proved from the actual finite eta action, then transported through lambda twice with the pre-existing fully faithful shift argument. The final extra lambda multiplication is also applied to the finite-quotient equality. No equality back in the untruncated sphere is asserted.

The chosen theta and b order-two hypotheses, bracket membership and all real mathematical premises are unchanged. No public Main declaration, public premise, object association or export was intentionally changed: all changed theorem signatures are private internal consumer statements. No sorry, axiom, result package, new pending obligation, False.elim, or circular invocation was introduced. `unique`/`huq` do not occur in either final file.

## Real upstream dependencies

The new argument directly consumes the final LowEta helper
`eta_action_source_iso_fixed_in_finite_quotient (n)(hn)(eta){k l}(x)(a)`, constructed by separation_interfaces in LowEta, whose conclusion fixes the action in the actual quotient target. This remains dependent on the registered upstream spectral/page calculations and selected quotient algebra compatibility. The shuffle also retains the existing synthetic triangulated structure, exact/fully faithful shifts, actual Toda operations, coherence and sphere action laws. Those upstream responsibilities are not counted as eliminated by this local reproof.

## Actual validation

Using the fixed v4.32.2 toolchain, escalation required for the process launcher, both original production paths passed bare Lean (exit 0) with `/tmp/kip-shuffle-overlay` first in LEAN_PATH. This overlay is a full file-symlink mirror of existing project outputs with actual LowEta and these two newly compiled modules replacing only their respective links. It does not write any shared `.lake/build` output.

Both were subsequently compiled with `-o /tmp/kip-shuffle-overlay/<original module path>.olean`, again exit 0. Complete logs:
- `/tmp/kip-main-any-y-shuffle.log`
- `/tmp/kip-main-theta-shuffle.log`

The overlay LowEta is the final source from separation_interfaces SHA `4944aaa62da6b331cc6af4655e8b4105ca5a9dee5610184500eaa181608b6bb4`, including its validated generic finite action/source-automorphism theorem.

## Remaining integration assigned to coordinator/other worker

- Root-owned exact patch: `/tmp/kip-main-shuffle-consumers.patch`, changing WeakRepresentative three private shuffle parameters to q9 equalities and its correction proof to apply lambda directly to that finite equality; AnyYError only drops the obsolete eta_unique argument. This patch was supplied without modifying those production files; its final build is coordinated by root.
- b worker owns the two Theta/TodaExistence and SectionSeven/ThetaToda private wrappers. They confirmed matching q9 return types, removing obsolete eta uniqueness and preserving theta/b order-two premises.
- Public Main interface, full source inventory, complete `lake build`, trust/dependency audit and final publication/cache work remain the coordinator's responsibility. Local module compilation is not a proof of those global checks.

Final whitespace-only cleanup removed a trailing space after `exact heq.trans hnq'`; mathematical/source terms are unchanged. Root has integrated the supplied consumer patch into production.
