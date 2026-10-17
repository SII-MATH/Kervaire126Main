# 6.20 删除差集条件后的独立核验

基线提交：`aad718722aa01dfce361f40645fc776037d1078f`。协议：`/root/.agents/skills/kip-upstream-session/references/protocol.md`。本核验者只读生产、公共记录与候选，不参与候选实现；唯一交付为本报告及如需的同目录审计证据，不改接口、入口、Tests 或他人文件，不运行 lake build。

任务依据：王老师消息 `om_x100b620ca1ac9ca4c1bb712f5951ae8`、群位置 1496，提出先删掉差集条件；本聊天用户授权核对后继续补证。当前核验的是**固定同一个 y、b=0，且不再要求 x′∉Z_late**的修正版，不将其冒称为印刷原文未经修订的完整证明。

## 数学陈述核验：通过

保留同一实际 X、Y、f 与其归一化映射，令 e=e(f)，p=(t−s,t+e)，并有：

- `2≤r′<r`；
- `e≤n≤r′−2+e`；
- 同一个 x∈Z_{r−1}^{s,t}、同一个 y∈Z_{r−1−n+e}^{s+n,t+n}；
- 晚页 extension `d_n^{f,E_r}(x)=y` essential；
- 早页 extension 为该同一 x、y 的 equation。

拟证修正版为：早页原扩张非本质，当且仅当存在

\[
0<a\le n-e,\quad x'\in Z_{r'-1-a}^{s+a,t+a}(X),
\quad d_{n-a}^{\hat f_{r'-1}}(\lambda^a x')
=\lambda^{n-e}y.
\]

右侧最后方程取同一早 λ 商、同一 stem、同一 synthetic weight t+e、同一个早页原目标 E∞ 元素。没有新的 y′，没有非 liftability 条件，也没有额外要求该较短方程 essential 或其源非零。原文最后方程没有写这两个额外要求，不能在核验时默加。

### 必要方向的直接证明，不需要新的迭代引理

对一个已知方程，非本质性的定义等价于同一目标属于实际高源不定性：存在早商实际类 A∈F^{s+1}，其映像在 F^{s+n}，并检测指定的原目标。该等价可由两个同首项代表相减得到，旧 `WangBzeroExactTarget.lean` 已给出完整 actual tower 版本。

若 `n>e`，甚至可以直接取 a=1：取 A 在 `F^{s+1}/F^{s+2}` 的首项，由同一早商的真实 E∞ 坐标

\[
E_\infty^{s+1,t+1,t+e}(\Sigma^{0,e}\nu X/\lambda^{r'-1})
\cong Z_{r'-2}^{s+1,t+1}(X)/B_2^{s+1,t+1}(X)
\]

选到经典循环 x′。其标签正是 λx′，A 本身支持同目标、长度 n−1 的较短 equation。若该首项为零，也允许 x′=0 及 inessential 的短 equation；它仍满足源存活条件，因为有实际代表 A 的像进入目标层。不能误把“零首项”混同为上轮已被非零 d₀ 杀掉的首项。

这使整个固定目标证明无需提取非 liftable 首项，也无需更换目标。此前 HZ/16 例子的 u 首项直接成为合法见证，原障碍已经消失。

### 充分方向

任取上述 a>0 的短 equation，其实际代表属于 F^{s+a}⊂F^{s+1}，且仍映到指定原目标余类。这正是原长度 n 方程的高源不定性，因此原早页 extension 非本质。此方向不需要晚页 essential。

## 必须核对的边界与真实前提

### n=e 不能草率删除晚页 essential

此时右侧 `0<a≤n−e` 无解。若没有晚页 essential 或非零目标前提，取 y=0 的零扩张，左侧却为真；故不能把修正版无条件推广为任意单早页 witness 的定理。

原前提足以排除此问题：晚页 essential 蕴含其实际 synthetic E∞ 目标非零；由合法条带内 ρ 的 E∞ 单射，以及同一 y 标签在 ρ 下的自然性/代表唯一性，早页目标也非零。归一化最短长度处无高源不定性，因此早页原扩张 essential，两边均为假。

候选拟复用以下现有完整证明链，数学上足够且不循环：

- `minimal_length_finite_tower_no_crossing`：从 normalized finite source λ 除法、quotient bottom-filtration 和实际映射自然性，得到高源像 filtration 下界；
- `tower_essential_iff_target_nonzero_of_no_crossing`：从无高源 crossing，推出每个同源代表的目标首项相同，所以已知 equation essential iff 其目标非零。

已独立读取 `GeneralizedLeibniz/CrossingFinite.lean` 和 `GeneralizedMahowald/ShortSource.lean` 中这些定理的实际证明体。它们不调用新的 6.20 iff，也不依赖非 liftability 结论。其底层标准 synthetic 模型/刚性仍属于项目现有上游责任，需在最终传递审计如实保留。

特别 `r′=2` 时 q=1，只可能 n=e；上述最短长度结果包含 q=1，没有因 λ 除法要求 `1<q` 而遗漏此边界。反之 n>e 强迫 r′≥3，因此 a=1 分支有合法 q−1>0。

### y=0 或经典边界

若原 y 的实际 synthetic 标签为零（包括落入分母 `B_{1+n−e}` 的情形），则晚页 essential 不可能成立。不能通过只看经典 y≠0 来替代这一判断。早晚目标比较应从实际 `finite_target_rho` 及 `HasInfinityRepresentative.unique` 得到，不在公共陈述另加目标相容假设。

### 目标 rho 单射的精确范围

在靶 `(s+n,t+n,t+e)`，条带指数是 k=n−e。原长度下界给 k≥0，早页上界给 k≤r′−2<r′−1，且 r′≥2 保证 q′=r′−1>0。因此 `rho_infty_injective` 的全部有效窗条件满足。单射用于传递目标非零，不声称 ESS 各页单射。

### 短源标签与分次

源经典分次 `(s+a,t+a)`、乘 λ^a、归一化 shift e 后，实际三分次必须是 `(s+a,t+a,t+e)`。短长度 n−a 的靶为 `(s+n,t+n,t+e)`，恰是原目标。循环层为 `Z_{r′−1−a}`，分母为 `B_{1+a}`；`a≤n−e≤r′−2` 保证其循环索引至少 1。无需丢掉分母导致的零标签，也不能把源改成较小商的 extension 而省略乘 λ 后的标签比较。

## 对公开签名的建议

沿用 ProofTools 的固定 `model`，显式给出同一 X/Y/f、r′/r/n/s/t/x/y 及晚、早两个 witness，晚 witness essential，合法页/长度范围。两 witness 目标相容应在私有证明内部通过标签自然性导出。

较短源标签定义可封装实际 `(r′−1)` 商内 `finiteNuLabel model X ... e (s+a) (t+a) a x′`，只做已证明相等的指标 regrade。RHS 必须同时包含经典循环条件、该标签的实际 E∞ 代表、同早商 normalized map 的短 equation，并直接使用早 witness 的原目标（必要时只作整数指标相等的 transport）。

不建议公开一个另加“早目标≠0”“早晚目标相容”“最短长度无 crossing”或“经典标签存在性结果包”为额外前提的替代定理。这些都应从原前提和现有真实接口证明。

## 生产候选独立核验：通过（保留既有上游待补）

本报告初稿时文件尚未交付；后续已完整读取并独立编译实际最终候选及其审计快照。核验对象为 `KIP126/ProofTools/Paper/ExtensionIndeterminacy.lean`，365 行，SHA-256：

```text
1720fccd565456ad350d489a3da09eacecce316d5d9626077b71e5fdad71c34c
```

最终只有两个新增数学公共声明：`:191` 的 `finiteExtensionCorrectionLabel`、`:300` 的 `finiteExtension_inessential_iff_shorter`。其余构造、代表转换、最短长度和目标相容辅助声明均保持 private；标签使用 `no_expose` 封装其私有选择，但公共 kernel 类型完全可消费。

### 完整类型、对象与前提

独立工具对两个**实际生产常量**输出了完整 elaborated kernel 类型及 universe 参数，见同目录 `IndependentProductionAudit.lean` 的可重跑命令。两者 universe 参数数组均为空，因为使用项目已固定的 `Standard.model`；未许诺任意 D 上的构造，也没有悄悄更换 C/Syn 实例。

标签完整参数为：`X Y : ClassicalObject`、`f : X.obj model.auxiliary ⟶ Y.obj model.auxiliary`、`q : ℕ`、`s t : ℤ`、`a : ℕ`，以及 `x′ : Ambient model X (s+a,(t−s)+(s+a))`；返回同一 normalized source quotient q 上 `(s+a,(t−s)+(s+a),t+e(f))` 的实际 E₂ 标签。

主定理完整参数为：同一 X/Y/f、`rEarlier rLater : ℕ`、`n s t : ℤ`、`x : classical.Page 2 (s,t)`、`y : classical.Page 2 (s+n,t+n)`、同 x/y 的 `Wlater : FiniteExtensionWitness ... rLater ...` 与 `Wearly : FiniteExtensionWitness ... rEarlier ...`，另有 `rEarlier≤rLater` 和 `Wlater.Essential`。结论是

```text
¬ Wearly.Essential ↔
  ∃ a : Nat, 0<a ∧ a≤n−e(f) ∧
  ∃ x′ : Ambient model X (s+a,(t−s)+(s+a)),
    x′∈cycles model X ((rEarlier−1)−a) (...) ∧
    ∃ z, HasInfinityRepresentative (actual source family) 2
      (s+a,(t−s)+(s+a),t+e(f))
      (finiteExtensionCorrectionLabel X Y f (rEarlier−1) s t a x′) z ∧
      TowerExtensionEquation (same early convergent map)
        (t−s,t+e(f)) (s+a) (n−a) z
        (arithmetic transport of Wearly.target).
```

上面 `actual source family`、`same early convergent map` 和 transport 的全部表达式已在生产源 `:300–321` 及独立输出 kernel 类型中逐项核对；它们依次是原 `model.family.obj`、原 `model.convergentMap` 的 q=`rEarlier−1` 两个 quotient 及 `finiteExtensionMap ... q`，以及只证明 `s+n=(s+a)+(n−a)` 的 `eqToHom`。无任取映射或 target 参数。

与纸面严格早晚页相比，`≤` 还包含相同页的自反情形，是本证明有效的加强。`2≤rEarlier`、`e≤n≤rEarlier−2+e`、经典 source/target cycle 和原方程均已包含在 Wearly 的完整结构字段中，并未遗漏。晚页结构保留其原 cycles 与检测代表。定理不要求额外目标非零、no-crossing、标签存在性包或早晚代表相容作为公共前提。

### lambda 标签的对象关联：不是任意 source 自同构

这项单独作了语义核验，不能仅以 `correction_label_exists` 的满射性就宣布通过。

1. 新标签从同一 X 的 unshifted `finiteTargetLabel ... a x′` 出发。这是现有 `targetNuLabel` 的 λ^a 标签再经指定商包含映射送入 q 商，非任意新选经典类。
2. 然后使用 `(essShift (0,e)).page` 作实际垂直归一化 shift。该比较的 `representative_iff` 把所有永久标签的 E∞ 代表送到 `towerInfinityIso`，而后者由同一 convergence 和 filtered-piece iso 定义；`filtered.ambient_eq` 则绑定实际 `shiftHomotopyClass`。因此在 RHS 所要求的 cycles/实际代表范围内，此步是同一真实类的 shift。
3. 最后以 `correctionShiftIso.inv` 从 `shift(quotient q (νX))` 回到 `quotient q (shift νX)`。它取自 `quotient_shift_exists`，该存在命题有商包含与三角连接投影的交换条件；新增私有 `correctionShiftIso_incl`（`:177–187`）实际从 `choose_spec.1` 证明所取 iso 的包含方块交换。这里没有允许任意源自同构作为参数。
4. 证明 `correction_label_exists`（`:204–258`）反向使用同一 iso、同一 filtered shift，再调用实际 finite E∞ 坐标选出经典 cycle x′，随后按同一路径送回原 z。故它同时保留实际 source 对象、分次、shift、商和同一经典标签解释。

通过的精确含义是：**经真实 shift/商比较解释的 λ^a x′，在同一 normalized quotient 的 E∞ 上代表同一类**。没有宣称新标签与旧 `model.comparison.nuE2 X e ... a x′` 版本的 `finiteNuLabel` 在任意非永久 E₂ 输入上 `rfl` 相等；现有 E2Comparison 没有一般 shift-page 兼容字段，不能伪造这个更强断言。这不构成本定理的额外未证前提：新公共标签已经由实际比较给出，而定理只消费其实际 E∞ 代表。

### 真实证明体和关键边界

- `:260–283` 从晚 target_rep 经真实 rho、`finite_target_rho`、代表唯一性导出早目标相容，再用有效窗 E∞ 单射传递非零。没有增加公共绑定假设。
- `:285–295` 在 n≤e 的情形调用前述既有最短长度无 crossing 与非零目标 essential 判据，排除早非本质；包含 q=1。
- 正向 `:331–345` 确实先得 n>e、q>1，再从同一早 map 的高源代表取 s+1 首项，调用 `correction_label_exists` 并取 a=1。短方程使用原 br 和原 hbr，因此目标严格是 Wearly.target。
- 反向 `:346–362` 从短方程的实际 ar、br 直接把源 filtration 降到 s+1，保持同一 f-image 与同一个 target grade，再套高源不定性判据。它不需要额外排除 short source=0 或 short equation inessential。

未发现目标循环、自调用、退化模型、已知矛盾消去、换对象、越过模块封装或把新责任转移给上游的行为。

## 独立实际检查与完整依赖闭包

首先将最终生产源原样复制成 `IndependentCandidateAudit.lean`，仅追加打印类型与依赖的命令，独立 `lake env lean` exit 0；这验证的证明文本与上述生产 SHA 一致。快照的普通上游 imports 会隐藏部分 proof body，初步闭包 341/602 只是下界，**不作为最终完整依赖结果**。

生产模块由协调者完成构建后，另写 `IndependentProductionAudit.lean`，使用与 `scripts/CaptureTrust.lean` 一致的 475 条 import（全数学模块 `import all`），在真实生产常量上递归检查完整类型和证明体，记录直接 sorry、项目公理、Main 与 ProofTools 依赖，并逐条与现有责任清单匹配。实际重跑 exit 0，结果为：

| 实际公共根 | 项目常量闭包 | 既有上游直接待补 | ProofTools 待补 | Main 依赖 | 项目公理 | 未登记待补 |
| --- | --- | --- | --- | --- | --- | --- |
| finiteExtensionCorrectionLabel | 567 | 33 | 0 | 0 | 0 | 0 |
| finiteExtension_inessential_iff_shorter | 822 | 38 | 0 | 0 | 0 | 0 |

两个根的真实 `collectAxioms` 都是 `[propext, sorryAx, Classical.choice, Quot.sound]`。其中 sorryAx 来自**已登记、仍未完成的上游对象与定理**；不能把本次局部补证描述成最终无 sorry 依赖证明。

主定理 38 条上游直接待补为：AdamsSynthetic 的标准范畴/对象/系统及比较构造（29 条），实际 shift 相关四条 `shift_representative_iff, shift_filtered, shift_page, shift_ambient_eq`，`synthetic_homotopy_separated`，以及 Literature 的 `eInfinity_finite_labels, eInfinity_finite, eInfinity_nu, eInfinity_rho_finite`。全部与现有 `metadata/proof-obligations.json` 精确名称匹配。未新增公理或责任，没把这些来源事实当作已完成构造。

注意 worker 单文件环境得到的 602/28 也属于封装边界下的部分闭包，不应用其替代本次完整环境 822/38。

本核验者还实际读取了普通 `import KIP126.ProofTools` 的 `Tests/ProofTools/Consumers.lean` 中新消费、n=e 边界及私有名称不可见检查，以及协调者的真实构建日志：模块/入口构建 2821 jobs 成功；专项普通消费构建 2823 jobs 成功。没有依赖 worker 的批准作为独立结论。

只读 Lean 命令均未带 `-o`，不写共享构建缓存；本核验没有运行 lake build。完整全仓库构建与接口锁/来源记录整合由协调者继续完成，不把两个专项构建当成已完成全仓库检查。

## 输入哈希与最终结论

核验前后生产源 SHA 一致。其余关键输入：

```text
828ee5a5aa06e1f390b036a043230ed417446fa7be11a4e27eecc4a565135c4b  AimPaper/main.tex
be2c30804b01991af0731aeaa0619b1738ccf93f0ac76c4271b4945844dd2aad  metadata/proof-obligations.json
```

早期审计脚本曾漏写 `module` 导致 import-all 报错，修正后实际通过；未将失败初稿记为通过。原始数学证据、历史反例和之前等待人审的报告均保留，没有回退其他工作者变更。

**目标级结论：数学陈述、实际候选实现、标签对象关联、同一目标、有限范围与边界均通过独立核验。** 本次补齐的是用户授权删除差集后的固定目标 iff，本地 ProofTools 新责任为零；既有上游 38 条待补仍存在。没有阻止协调者继续普通整合与全仓库检查的新数学阻塞。
