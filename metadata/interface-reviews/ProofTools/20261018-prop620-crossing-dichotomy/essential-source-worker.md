# Essential short-source extraction worker

基线为 `aad718722aa01dfce361f40645fc776037d1078f`；输入哈希以本目录 `baseline.json` 为准。已读仓库规则与 `/root/.agents/skills/kip-upstream-session/references/protocol.md`。本轮生产写入只限 `KIP126/ProofTools/Paper/ExtensionEssentialSource.lean`；未改公共入口、接口锁、上游源码、测试或待补清单。共享工作区其他变更未回退。

## 已完成目标

两条辅助引理均为 `private`，位于 `@[expose] section`，只供同模块 `import all` 消费：

1. `tower_essential_shorter_same_target`：对任意同一 synthetic tower/convergence/map，给定长度正的 equation、非零指定目标与原 equation 非本质，提取 `0<a≤n` 的 essential 短 equation。新目标仅按 `s+n=(s+a)+(n−a)` 重索引，元素本身未改变。
2. `finiteExtension_essential_shorter_source`：对同一固定标准模型中的实际 `FiniteExtensionWitness W`，输入 `W.target≠0` 和 `¬W.Essential`，得到 `0<a≤n−e(f)`、经典 `x′∈cycles X ((r−1)−a)`、`finiteExtensionCorrectionLabel` 的真实 E∞ 代表 z，以及同一实际有限归一化映射中从 z 到 W.target 的 essential 短 equation。

没有引入代表选择公理、额外数学假设、结果包或新待补责任。后一条不是只选择 `a=1` 的可能非本质 equation；它确实保证提取的短 equation essential。精确 Lean 类型见生产文件 `:113–133`。

## 证明与终止

泛型证明先用现有同目标高源判据取得一条高源代表方程。然后在有限集合 `1≤a≤n.toNat` 中，以 `Nat.findGreatest` 选择仍有实际高源代表命中指定目标的最大 a。

对该代表取关联分次 z。如果短 equation 仍非本质，同目标零源判据给出另一个命中原目标的实际代表，其源分次为零，故实际源提高到 `s+a+1`。若 a<n，这与 a 的最大性冲突；若 a=n，filtered-map compatibility 使其映像处于目标下一层，迫使指定目标为零，与前提冲突。因此短 equation essential。

有限归一化 specialization 使用 `inessential_length_strict` 排除 `n=e(f)` 空边界，再消费已经证明的 `finite_crossing_target_bound` 将 a≤n 加强到 a≤n−e(f)。这避免直接调用 `finite_normalized_image_filtration` 时的 `i<q` 边界问题。原 W 的长度上界随后保证 a<r−1，`correction_label_exists` 在准确有限 λ 商中解码经典 cycle 标签。

没有以原命题 6.20、待构造 dichotomy、Main 最终目标或目标自身作为依赖。generic max 的 predicate 只量化现有实际代表与同一个目标的关联分次相等式，不是新假设。

## 消费与职责

已将精确签名和完成通知发送给独占 `ExtensionCrossingDichotomy.lean` 的主 worker `prop620_descent_public`。其调用形式为：

```lean
finiteExtension_essential_shorter_source X Y f r n s t x y W hy hne
```

由协调者安排生成本文件 `.olean` 后，主 worker 可用同模块 `import all KIP126.ProofTools.Paper.ExtensionEssentialSource` 消费。该 worker 没有接手其差集/晚页 crossing 分支，也没有改其文件。

## 实际验证与传递责任

实际执行：

```sh
lake env lean KIP126/ProofTools/Paper/ExtensionEssentialSource.lean
```

最终 **exit code 0**，无错误、无 `sorry` 警告。首轮仅有 dependent Nat-cast transport 的局部类型错误，修复后泛型检查 exit 0，追加 actual finite specialization 后再次检查 exit 0。按协调者允许采用 `require_escalated`，未运行 `lake build`、未写共享构建 `.olean`。

本目录 `EssentialSourceDependencyEvidence.lean` 是该生产文件的逐字副本再追加两条 `#print axioms`，已实际执行 Lean，**exit code 0**。泛型 lemma 的结果为 `[propext, Classical.choice, Quot.sound]`，无 `sorryAx`；actual lemma 为 `[propext, sorryAx, Classical.choice, Quot.sound]`。后者消费固定 `model`、已有 `finite_crossing_target_bound`、标准 finite-label comparison 等，仍带这些上游已登记待构造的传递责任，不将其记作本轮消除。新增两条 lemma 本身没有直接证明洞。局部通过不等于全项目或上游所有数学责任完成。

`metadata/proof-obligations.json` SHA-256 仍为 `be2c30804b01991af0731aeaa0619b1738ccf93f0ac76c4271b4945844dd2aad`；`ExtensionIndeterminacy.lean` 仍为基线 `1720fccd565456ad350d489a3da09eacecce316d5d9626077b71e5fdad71c34c`。
