---
title: Toda 检测与任意代表扩张的缺口
archived_from: local-history/metadata/interface-reviews/Main/20261018-gray-toda-anyy/report.md
archived_sha256: bade7e530ed09c4aaf36ee78048489bd9641bb4931818c16f1eeb1274ee2f58e
summary: "两项完整条件命题现已由独立的前提排除定理证明，类型与固定对象不变；Main/ProofTools 闭包无本地待补，仍继承 116 项上游责任。原文局部 Toda 与代表误差论证的缺口保留，不构成满足完整前提的反例。"
issue_id: "Main-20261018-gray-toda-anyy"
responsibility_module: "Main"
targets:
  - "AimPaper Lemma 7.16 / blueprint paper:7.16"
  - "AimPaper Corollary 7.18 / blueprint paper:7.18"
baseline_commit: "3764cde353550932b36c54c4afff021961dc7e55"
worktree: "/inspire/hdd/global_user/czxs25250150/Kervaire126Main"
candidate_source_commit: "uncommitted private evidence, frozen SHA-256 e4bb7a6e290d2ccc0074770aa1cf41fd857e6beb3a2fbd8f29edcb6d719cebde"
api_file_and_sha256: "metadata/main-api.json; exact SHA-256 in evidence/source-hashes.json"
source_file_and_sha256: "full independently read source list in evidence/source-hashes.json"
reporter_agent: "/root/main_gray_review"
independent_of_discoverer_and_implementer: true
evidence_level: "Lean kernel-checked fixed-object obstruction to an intermediate mechanism, conditional on registered upstream constructions; NOT a counterexample satisfying the complete paper hypotheses"
status: pending-human-review
human_decision: null
---

# Main 两个灰节点：Toda 检测与任意代表扩张的独立人审报告

本报告员没有参与候选发现或实现，只读取原文、定义和证明体，在分配的报告目录内独立重放并审计。规则采用仓库当前 `AGENTS.md` 与 `/root/.agents/skills/kip-upstream-session/references/protocol.md`。用户的当前授权是：沿 AimPaper 补两个原结论，原有公共接口不变。**本报告未修改任何生产源码、公共接口锁、待补清单、Blueprint 或 corrections.yaml，也未自行批准替代陈述。**

## 人类决定范围：当前无需立即确认

**继续方案 A（原目标、原公共接口）已经得到用户授权，本轮不重复请求许可，也不因本报告暂停非争议证明。** 当前没有需要用户立即确认的问题；本报告未改变任何接口。

下文方案 B 的“任意代表关联分次检测”尚未完整证明，不能作为本轮即时批准问题；方案 C 是已完成的 bracket 成员辅助结论，不能冒充原 Corollary。两者只供后续候选评审时精确比较：如果未来确实建议把原节点改为这些较弱目标，届时必须提供已验证候选、原/新完整签名、下游影响，并取得针对该变化的明确授权。

报告协议要求的 `pending-human-review` 与 `human_decision: null` 只表示没有人类批准过本文讨论的目标修订；它们不撤销既有补证明授权，不意味着当前必须等待用户。原文 Lemma 7.16 的同一 bracket 检测继续独立研究，最新投影不定性进展见下文。

## 原接口、背景与问题成因

### 固定对象、量词和源码接口

所有范畴、宇宙、实例、谱塔、收敛、商与类都取自已经固定的 `KIP126.AdamsSynthetic.Standard.model`，没有可另选的模型参数。记

- `Qn := XModLambdaN (S_0_0 : SyntheticSpectrum) n`；
- `Y := KIP126.Computation.Standard.Y : sphereSequence.Page 2 (11,136)`，即 `h₀²x₁₂₅,₉,₂`；
- `T := KIP126.Computation.Standard.T : sphereSequence.Page 2 (14,139)`，即 `h₁h₄x₁₀₉,₁₂`；
- `h0 := KIP126.Literature.Standard.syntheticH0 : BiHom 0 1 S_0_0`；
- `eta := KIP126.Literature.Standard.eta : BiHom 1 2 S_0_0`。

实际源为 `π_(125,132) Q9`，不是未截断球，也不是任意抽象滤过群；精确扩张的未乘 λ 目标为 `π_(125,139) Q9`，其 λ⁶ 像在 `π_(125,133) Q9`。

现有 `SectionSeven/Predicates.lean` 中的完整接口是**私有谓词**，不是已登记的公共证明。两个灰节点当前都没有完整公共结论可供“补其证明体”；不能把谓词或部分辅助结果当成原结论的公共形式化绑定。以下为原谓词原样主体，`open` 的对象与上述固定模型一致：

```lean
private def FiniteDetected (n : ℕ) (_hn : 0 < n) (s t : ℤ) (k : ℕ)
    (x : sphereSequence.Page 2 (s,t))
    (a : BiHom (t-s) (t-k) (XModLambdaN (S_0_0 : SyntheticSpectrum) n)) : Prop :=
  DetectsNonzero (model.convergence (.quotient n .sphere)) (s,t,t-k)
    ((family.quotientProjection syntheticSphere n).pageMap 2 (s,t,t-k)
      (comparison.sphereE2 s t k x)) a

private def AnyYH0Extension (Y : sphereSequence.Page 2 (11,136))
    (T : sphereSequence.Page 2 (14,139))
    (h0 : BiHom 0 1 (S_0_0 : SyntheticSpectrum)) : Prop :=
  ∀ y : BiHom 125 132 (XModLambdaN (S_0_0 : SyntheticSpectrum) 9),
    FiniteDetected 9 (by decide) 11 136 4 Y y →
    ∃ t : BiHom 125 139 (XModLambdaN (S_0_0 : SyntheticSpectrum) 9),
      FiniteDetected 9 (by decide) 14 139 0 T t ∧
      sphereAction h0 y = lambdaMultiply 6 t ∧ lambdaMultiply 6 t ≠ 0
```

Corollary 的待证明类型是上述原谓词在固定 `Y,T,h0` 的特化，前提完整保留：

```lean
(hc3 : KIP126.Main.Stem126D6Vanishes)
(hc5 : KIP126.Main.EtaExtensionDetection)
⊢ AnyYH0Extension KIP126.Computation.Standard.Y
    KIP126.Computation.Standard.T KIP126.Literature.Standard.syntheticH0
```

`hc3` 不是只断言一个形式零式，而是实际第六页共同代表上的
`HasDifferential model.classical.sphere 6 (8,134) (14,139) W 0`。
`hc5` 是存在未截断 U 代表 `u : BiHom 124 134 S_0_0`，满足其非零检测，且 `λ³ηu` 被 `(14,139,133)` 的 λ⁶T **检测**，这里没有擅自增加非零目标前提。现有公共 `eta_extension_detection_choice_equivalence` 把存在式与原文 `(5′)` 的“对每个 U 代表”互换。

Lemma 7.16 使用同一 `a11 : BiHom 123 132 Q11` 以及实际 `a9 := a11 ≫ rho 9 11`。`AlphaOneProperties a11` 包括 Q11/Q9 中同一个 V 标签非零检测、对每个未截断 U 代表的两条 a₂/a₃ 校正式，以及精确 `λ³ h₀ a9 = 0`；完整源码摘录见 `evidence/original-statements.md`。其目标是 bracket

```lean
ModuleTripleToda (lambdaMultiply 3 a9) syntheticH0 eta z
```

非空，并且其中**每个原成员 z** 满足 `FiniteDetected 9 ... 11 136 4 Y z`。该模 Toda 的实际箭头链是 η、h₀、λ³a9，末箭头才落在 Q9。不定性来自 `λ³a9 · π_(2,3) S` 与 `η · π_(124,130) Q9`，不能换成任意 Q9 自同态作用。若只证明某个与 z 的像相同但未保留 bracket 关系的 y 检测，仍未证明本目标。

### 原文约定与成因分类

独立读过 `AimPaper/main.tex:2470–2584` 全部陈述和证明，以及 `(3)`、`(5′)` 所在 `2181–2206,2244–2265`。原文 `302–304` 明确把 `{x}` 定义为**所有被 x 检测的同伦类**，`[x]` 是其中一个或一般代表；Corollary `2572` 又明确说 “For any homotopy class [λ⁴Y]”。没有找到把该量词限制为同一个 Toda bracket 或同一 Q9 内实际 λ⁴ 可除源的约定。这样限制会改变前提/量词。

独立确认的分类是：

- **Lemma 7.16：证明不足。** 原文从存在可被 λ² 消去的低层代表，跳到原 bracket 不能具有该低层分量；还在 `2559–2560` 从非零 η 像相等转为原像相等。两种推断需要额外的真实不定性/核论证。它们不构成原完整条件命题为假的证据。
- **Corollary 7.18：任意代表的精确提升机制有已核的固定对象障碍。** “差的 h₀ 像不由 λ⁶T 检测”只说明关联分次位置，不能推出精确等式或可吸收性。下述真实 Q9 元素给出不能被允许目标代表变化吸收的高层误差。
- **不是现有公共接口实现错误。** 现有 `anyy_bracket_exact_target` 只断言 bracket 成员的精确关系，其量词比原 Corollary 小，源码没有冒充完整 Corollary。
- **未证明完整条件命题为假。** 下述证据不提供满足 `hc3 ∧ hc5` 的固定模型。已知 Main 下游正证明这两个条件不相容；本审查不调用该结论来构造证据，也不把不相容前提下的条件命题称为反例。

## 真实前提与对象核对

| 前提或对象条件 | 是否满足 | 独立证据及局限 |
| --- | --- | --- |
| 同一个固定 synthetic sphere 及实际 Q9 | 是 | 候选所有 `BiHom`、商、谱塔和收敛均显式使用 Standard.model；没有替换模型或实例。 |
| Cor 源 `(125,132)`、目标 `(125,139)`、h₀ 像 `(125,133)` | 是 | 逐行检查了源码及独立 Lean 重放。 |
| 任意检测源、允许随源变的 T 代表 | 是 | `AnyYH0Extension` 完整类型；候选并未偷偷把 T 固定为一个先选的同伦类。其 λ⁶ 像不变是证明出来的。 |
| δ 在同一源群且至少 F¹²，加入 δ 保持原 Y 检测 | 是 | 实际构造更强 `δ ∈ F¹⁵`，`detected_y_perturbation` 对每个原 Y 检测代表 y 证明 y+δ 仍为同一检测。 |
| δ 的 h₀ 像非零 | 是，依赖既有上游 | `actual_top_error_exists` 的完整固定对象证明；没有假设 hc3/hc5。 |
| 允许 T 代表之差可吸收 h₀δ | 否 | 两个 T 检测代表之差在 F¹⁵；现有 `anyy_lambda_six_filtration_fifteen_zero` 使其 λ⁶ 像为零。 |
| 旧 AF14,k7 generator449 候选是合法 finite cycle | 否，已撤回 | `cycles c` 对应到 E_(c+1)，k7 的窗口 Z₂/B₈ 要求 d₂=0，而该 generator 的 d₂ 非零；新证据使用 k8 的 Z₁/B₉。 |
| 原文全部 hc3/hc5 前提 | **未作为反例满足** | 候选不用这些前提，也没有构造它们同时成立的环境，因此只反驳中间机制。 |
| 某个 Y 检测源必然存在 | 对最后不相容引理是显式条件 | 最后引理以 y 与检测 hy 为输入。不能把这个条件抹掉后宣称原完整 Cor 为假。 |
| 无新的公理或 sorry、无下游矛盾捷径 | 已独立编译；完整闭包结果见后附审计 | 审计显式排除 `Final` 的排除定理、`table1`、`h6_sq_permanent`、`target_nu_divisible`。 |

## 独立证据与复现

### 1. 实际顶层误差，不是抽象模型

固定候选文件 `evidence/Obstruction.lean` 是实现者交付的精确冻结副本，SHA-256 为
`e4bb7a6e290d2ccc0074770aa1cf41fd857e6beb3a2fbd8f29edcb6d719cebde`。报告员逐行独立核对并运行：

```sh
lake env lean local-history/metadata/interface-reviews/Main/20261018-gray-toda-anyy/evidence/Obstruction.lean
```

**独立重放 exit 0，日志 `evidence/candidate-replay.log` 无诊断。没有生成或覆盖共享 olean。**

关键步骤如下，标签、页数和对象分别核对：

1. 取 `x = basis .sphere 15 140 3 = h₀ · generator449`。源三分次为 `(15,140,132)`，λ level 为 8，故 Q9 的有限窗口是 **Z₁/B₉**。Z₁ 是整个 E₂；不需要假设这个 x 的 d₂ 为零。
2. `finite_sphere_infinity_exists` 把该 cycle 的真实有限标签送到 Q9 的 E∞；实际收敛的 associated-graded 商映射满射产生 `δ : BiHom 125 132 Q9`，标签 x 检测 δ，因此 δ∈F¹⁵。没有任意挑选一个与真实 Q9 无关的滤过群。
3. 实际 `finite_action` 给出 h₀δ 的标签 `h₀x = basis .sphere 16 141 3 = h₀² · generator449`，三分次 `(16,141,133)`，仍为 level 8、Z₁/B₉。
4. 表格 claim 372 / row 3256 给出这个目标 E₂ 类的非零 d₂，目标是 `(18,142)` 的 basis1，其非零性由 `basis_correct` 的实际 F₂ 坐标同构证明。所有 B₉ 都包含在 Z₂，所以该 E₂ 类不在 B₉。
5. 实际有限标签的非边界判据因此给出 `h₀δ≠0`。

最终核验的无条件中间结论是：

```lean
∃ δ : BiHom 125 132 Q9,
  FiltrationAtLeast model.syntheticTower 15 δ ∧ sphereAction syntheticH0 δ ≠ 0
```

它否定“同一 Q9 的高源误差必被 h₀ 杀掉”这个补证引理。这里的 λ⁸ 是 E₂ 标签 level；**不是声称已经在同一 Q9 找到了一个未乘 λ 的同伦类，使 δ 等于其 λ⁸ 倍。**

### 2. 更换目标代表不能吸收这个误差

对任意两个由同一 T 非零检测的 `t,t′ : BiHom 125 139 Q9`，真实检测差定理给 `t−t′ ∈ F¹⁵`。既有 `AnyYPeeling.lean:80` 证明 `λ⁶F¹⁵ = 0`，所以 `λ⁶t = λ⁶t′`。

若存在由 Y 检测的 y，则 y+δ 也由 Y 检测。假如完整 `AnyYH0Extension` 同时适用于 y 和 y+δ，分别取其允许的 t 与 t′，上述等式迫使
`h₀(y+δ)=h₀y`，进而 `h₀δ=0`，与步骤 1 矛盾。冻结文件最后已经证明完整类型：

```lean
(y : BiHom 125 132 Q9)
(hy : FiniteDetected 9 (by decide) 11 136 4 Y y)
⊢ ¬ AnyYH0Extension Y T syntheticH0
```

这个结论的精确强度是“**Y 检测集合非空时，无条件任意代表精确扩张不成立**”。它没有提供 `hc3∧hc5` 的见证，不能包装成原 Corollary 7.18 的完整条件反例。

### 3. 传递依赖与循环审计

`evidence/audit_existing.lean` 审计六个已有根，包括精确 bracket 目标、目标高层 λ⁶ 消去、F¹²=F¹⁴ 间隙、弱代表剥离、alpha-one 存在及 `(5)/(5′)` 选择等价。`evidence/audit_candidate.lean` 对冻结候选十个新声明逐个核查。

审计环境显式 `import all` 当前全部生产模块，以免 ordinary import 隐藏私有证明体造成错误闭包；数学证明只依赖其真实类型和证明体中出现的常量。遍历全部项目依赖边，在 Mathlib/Lean 边界停止；Mathlib/Lean 不可能回调本项目声明。另核准基础逻辑公理。它不使用“导入过整个 Main”来冒充证明调用。

当前实际验证状态记录在 `evidence/validation.json`：冻结反例机制、Toda 归约和正向 AnyYExtension 各自独立无 -o 重放均 **passed / exit 0**；完整项目闭包审计当前 **blocked / exit 1**，原因是源清单已列入 `KIP126.AdamsSynthetic.Internal.Source.AdamsSequence`，但它的 `.olean` 缺失。协调者本轮实际执行的全量 `lake build` 已 **exit 1**：另一个并行会话的 `AdamsSequence.lean:376` 类型不匹配、`:378` heartbeat 超限、`:415` 未知常量；另有 `metadata/geometry-api.json` 缺失使 sourceInventory/geometryApi 失败。报告员独立读取了完整构建日志的失败段，并在 validation 中记录原日志 SHA。报告没有修改这些会话外文件。

这是实际构建与缓存证据边界，不是候选数学反例的新增前提；本报告此时**不声称完整闭包已通过，也不提供不完整的责任计数冒充完整数量**。

在本报告独立回放时的快照中，七份 API 锁、原待补清单、Main 入口、Main `PaperResults.lean` 和 `Conditions.lean`，共 11 文件均与分配的基线 SHA 一致，见 `evidence/selected-baseline-check.json`。**这不是最终工作区仍逐字相同的声明。** 协调者随后确认另一会话继续更新 `literature-api.json` 与 `proof-obligations.json`；这些不属于本报告或本次 Main 私有辅助证明的写入。其余六份原 API 锁（含 Main）在协调者该次记录时仍与原基线相同。现有上游未证依赖仍在；候选可编译不等于整个固定模型已无待补。

### 4. Lemma 7.16 的未决范围与最新进展

原 `main_weak_high_representative` 的类型只产生某个 F¹¹ 的 y 并保持 `λ²h₀y≠0`，没有证明 y 仍属于原 bracket。`ηA=ηB≠0` 也不能在没有核控制时推出 A=B。独立反例审查的有限 F₂ 模型只说明这两个逻辑步骤缺前提，不识别实际 synthetic sphere，不能作为原命题反例。

本次继续证明已推进到实际投影 `ρ_(3,9):Q9→Q3`。报告员独立读取并重放了完整 `TodaDetection.lean` 冻结副本，SHA-256 `7c3159d687499d6a8e4e96db2e27bec3b696bf6d154a41f1fd18fce696055b22`，`evidence/toda-replay.log` 无诊断，exit 0。实际已证明：

- `alpha_toda_restrict_three_unique`：对同一 a11 与 AlphaOneProperties、同一原 bracket 的任意两个成员 z₁,z₂，实际 `z₁≫ρ_(3,9)=z₂≫ρ_(3,9)`，不需要 hc3/hc5。证明保留完整 Toda 不定性恒等式；左项用 α 投影后 λ³=0，右项用**来自 Q9** 的 η 不定性在 F¹¹ 因而投影为零，并未假定所有 Q3 η 像都为零。
- `alpha_toda_detected_iff_restrict_three_zero`：在原 hc3/hc5、同一 a11/ha 及原成员关系 hz 下，
  `FiniteDetected 9 ... 11 136 4 Y z ↔ z≫ρ_(3,9)=0`。逆向先从原 z 的实际 Q3 投影为零推回 z∈F¹¹，再对**原 z** 使用精确 bracket 目标和已证 λ²h₀ 非零检测判据；没有替换原成员。

因此，投影层级上的完整不定性已受控制。**当前尚缺这个唯一 Q3 二阶操作值等于零，而不是笼统的全部不定性缺失。**

另外，报告员复制并独立重跑了反例审查员的 `finite_models.py`：三个有限 F₂ 机制模型全部通过，证据在 `evidence/finite-model-results.json`。它们只检验低层剥离、η 消去、高层误差吸收这三种抽象推断，不是 fixed sphere 或完整 hc3/hc5 前提模型；真正固定对象证据是上面的 Obstruction.lean。

### 5. 已完成的正向任意代表结果

报告员另独立读取并重放了生产文件 `AnyYExtension.lean` 的冻结副本，SHA-256 `f9f34ab3a32124ef65a1e93a082b83600d47e0b079df7d9d93475d088cd3665d`，`evidence/anyy-positive-replay.log` 无诊断，exit 0。六个私有引理证明：

- 同一 Y 检测的 y,y′ 满足 `h₀(y−y′)∈F¹⁵`；
- 继续乘 λ² 后该差为零，因此 `λ²h₀y` 与源代表选择无关；
- 同一 T 检测的 t,t′ 满足 `λ⁶t=λ⁶t′`；
- **若已经给出真实 y₀ 的 Y 检测及精确式 `h₀y₀=λ⁶t`**，则对任何 Y 检测代表 y 有 `λ²h₀y=λ⁸t`，在 hc3 下右边非零。

这是真实的内部证明进展，不是需要重新授权的目标变更。最后一条显式保留已经构造初始 y₀/等式的局部输入，不能把尚缺的初始同一 bracket 检测假装成新的公共前提；也不能从乘 λ² 后的等式取消 λ²，回报原 Corollary 已完成。

## 方案及精确差异

### 方案 A：保留原接口与原论文目标，继续内部证明

这也是当前用户已授权的路线，不需要新批准。任何补证必须保持同一实际 bracket、原 y、原 Q9 与所有量词。

- Lemma：继续计算唯一 Q3 bracket 投影，或从同一个实际 Q11 alpha-one lift 及 nullhomotopy 构造投影为零；不能换一个无成员关系的高层 y。
- Corollary：不能再把 `∀δ∈F¹⁴,h₀δ=0` 当作无条件充分引理——它已有更高 F¹⁵ 的固定对象反证。若继续原条件命题，需要说明如何使用完整 `(3),(5′)`，并如实区分其不相容性与原代表机制。用已经依赖后续整套推导的 `Final` 直接 `False.elim` 不回答本次沿原文的证明要求。
- 保留现有 public 名称、类型、前提、导出及锁，不引入新的上游“可消去所有误差”责任。

### 方案 B：候选改为任意源代表的关联分次检测

这是拟议替代命题，不是已批准接口，不声称本报告已完成它。完整旧目标如上 `AnyYH0Extension`；候选新目标在同样 `hc3,hc5` 下为：

```lean
∀ y : BiHom 125 132 Q9,
  FiniteDetected 9 (by decide) 11 136 4 Y y →
  DetectsNonzero (model.convergence (.quotient 9 .sphere)) (14,139,133)
    ((family.quotientProjection syntheticSphere 9).pageMap 2 (14,139,133)
      (comparison.sphereE2 14 139 6 T))
    (sphereAction syntheticH0 y)
```

差异：源量词、源检测、固定 Q9 和前提不变；保留非零 T 标签检测；**删去实际 `∃t, FiniteDetected T t ∧ h₀y=λ⁶t` 的可除结论**。该候选允许 F¹⁵/F¹⁶ 高层误差，避免与顶层 δ 机制冲突。它比精确扩张弱，不能直接替代所有需要可除性的调用方。后续若证明该候选，也必须明确标为修订命题，不能给原文全文自动绑定“已完成”。

### 方案 C：只对原 Toda bracket 成员保留精确等式

完整候选是已有 `anyy_bracket_exact_target` 的实际类型：在 `hc3,hc5,a11,AlphaOneProperties a11` 下，对每个满足原 `ModuleTripleToda (λ³a9) h₀ η z` 的 z，存在同一 Q9 中被 T 检测的 t，满足 `h₀z=λ⁶t≠0`。

它已经有正确局部证明，不要求改变任何现有公共接口。与原 Corollary 的精确差异是：**把“所有 Y 检测代表”换成“同一个实际 bracket 的成员”**，并保留该 bracket 的 alpha-one 参数关联。除非另有定理把所有 Y 检测代表识别为 bracket 成员，否则不能提升回原 Corollary；顶层 δ 证据表明这种无条件识别也不能成立。

限制源为某种 λ⁴ 可除子集是另一个未验证选项。必须先明确是在同一 Q9 中可除，还是有限商之间的 λ⁴ 三角像；两者不同。本文没有足够证据推荐该选项，不把它偷偷加入“原文解释”。

## 下游影响

- **直接目标：** `blueprint/paper/Main.tex` 中 `paper:7.16` 和 `paper:7.18`，以及各 hgraph 原生节点附件；目前必须保留真实未完成边界。
- **现有私有接口：** `SectionSeven/Predicates.lean` 的 `FiniteDetected`、`ModuleTripleToda`、`AnyYH0Extension`，`AlphaOneProperties` 及 `AnyYTarget.anyy_bracket_exact_target`。本报告不改它们。
- **现有已完成公共 Main：** `metadata/main-api.json` 没有这两个完整定理；本报告不要求改任何旧条目。公共 `Paper.FiniteDetected` 的含义也不应为避开误差而缩小。
- **已有 Main 后续证明：** `SectionSeven/NuTarget.lean` 使用 bracket 精确目标，再用 `main_weak_high_representative` 和 `weak_y_detected_of_f11_and_nonzero`，之后走 `nu_target_full_of_nonzero`；它没有调用这两个尚不存在的完整定理。因此本次问题不自动推翻已经采用弱代表路线的 Main 最终证明。不得反向调用该最终证明来伪装完成这两个灰节点。
- **模块责任：** 当前计算、比较与收敛输入仍分别属于 E2Computation、AdamsCalculations、Literature、AdamsSynthetic；不得新增一个“误差全部被 h₀ 杀死”的上游公理来转移 Main 缺口。
- **记录：** 如以后有人类批准原文修正，由协调者在唯一维护源 `corrections.yaml` 记录，引用原文与 Blueprint，不能另造平行修正清单。本报告只是 Git 忽略的人审证据。
- **验证：** 若以后真正新增/导出完整定理，协调者需单独取得相应公开范围授权，并更新唯一归属接口锁、普通导入消费和信任审计；生产修改后运行源码清单检查与 `lake build`。本报告员只做无 olean 的独立证据检查，不以此替代全量构建。

## 阻塞范围与继续项

确实被否定的步骤：无条件 `h₀F¹⁴=0`；把任意更高误差自动吸收进一个仍由 T 检测的目标；把 AF14,k7 的非 d₂-cycle 当作合法有限代表。不能继续借这些步骤拼出原 Corollary。

未被本报告冻结的任务：同一 bracket 的 Q3 投影计算、Q11 alpha-one/nullhomotopy 相容性、已证不定性边界的收尾、对已完成私有机制的独立审计，以及保持旧 public 接口的其他 Main 推导。报告不因一个未核猜想暂停整个模块。

## 人类审核记录

`human_decision: null`。截至本报告，用户只授权继续补原结论并保持原公共接口；没有针对本报告方案 B/C 的明确批准。agent 的进展、建议或批准私有证据整理均不构成数学陈述修改授权。

## 2026-10-19 独立增补：原条件命题的本地责任已经消除

本节由未参与候选实现的 `/root/main_audit` 独立核验，基线为 `0e940a5108088ad73a19415721060012a8aad779`，工作区为 `/inspire/hdd/global_user/czxs25250150/ops/tmp/prooftools-main-proofs-20261019`。本节保留上述历史证据和原有 `pending-human-review` / `human_decision: null`，不批准方案 B/C，也不撤销历史上对直接代表机制的障碍结论。此前“没有公共完整定理”“仍有两个 Main 直接证明洞”的叙述是当时快照；以下为当前结果。

当前用户要求补 Main 的 `sorry` 并绑定灰节点，未要求独立完成原文的直接局部证明。候选没有改变公共类型、前提、对象或导出；因此本次正常补证明不需要接口调整批准。本节只核验候选及实际依赖，不把补证明授权写作对其他接口方案的人审批准。

### 目标级结论与固定类型

- **通过：** `KIP126.Main.Paper.lemma_toda2ext` 的本地直接责任消除。完整 kernel 类型指纹为 `299194068720801273`，宇宙参数为 `[]`。
- **通过：** `KIP126.Main.Paper.corollary_2ext125` 的本地直接责任消除。完整 kernel 类型指纹为 `2927248977343468461`，宇宙参数为 `[]`。
- **通过：** `sem:Main:weak-representative-route` 绑定既有公共 `KIP126.Main.eta_extension_excluded_of_d6_vanishes`。该声明实际定义在 `KIP126/Main/H6SquarePermanent.lean:16`，列入 Main 接口锁，kernel 类型指纹为 `17210897524146462465`，宇宙参数为 `[]`。节点正文明确陈述同一互斥结论，不绑定私有代表构造或辅助证明。

两项条件定理的 `public theorem` 到 `:= by` 之前的完整源码签名与本次基线逐字相同，SHA-256 分别为 `6eb2f57ffbb8fcb37359f23559f656ee5cd76597c1ea600f3d7e167d9c86458e` 和 `b1f9999282174941e545a5cc0cd4cdbe51e321ad28ec0a4defd6812e6a3ed30d`；kernel 指纹及宇宙与未更改的 `interface/baselines/main-api.json` 逐项相符。所有 Q11→Q9 关联、同一 bracket 的非空性及全成员量词、任意 Y 检测源、允许随源变化的 T 代表和精确未乘额外 λ 的等式均保留。

`Conditions.lean`、排除定理文件及其 `SectionSeven/Final.lean`、`NuTarget.lean`、`CofiberRigidity.lean` 与本次基线一致。`hc3` 仍是固定 W 在实际第六页的零微分；W 确为 `x_126_8_4 + x_126_8`。`hc5` 仍保留实际未截断 U 代表及 λ³ηu 的指定检测，未另加非零目标假设。T、Y、模型、实例和有限商没有被替换。

### 证明体、互斥来源与非循环性

当前两证明体分别在 `PaperResults.lean:110,124` 调用：

```lean
False.elim (KIP126.Main.eta_extension_excluded_of_d6_vanishes hc3 hc5)
```

这是原有真实假设 `hc3` 和 `hc5` 的互斥，不是一个无前提的 `False` 公理。独立阅读的实际路线是：

1. 公共排除定理调用 `SectionSeven.Final` 的私有结论。
2. `Final` 用 `target_nu_divisible hc3 hc5` 得到同一实际 T 的 λν 可除关系，并用同一 Cν 底胞的有限页生存/非边界窗口排除它。
3. `NuTarget` 先构造原 bracket 成员及其精确 h₀ 目标，再保留非零 λ²h₀ 值去除低滤过项，检测得到的高滤过代表，接上已证第九商 ν 扩张及乘法计算。它不声称去除后的代表仍在原 bracket，也不使用任意 Y 代表的未乘额外 λ 的扩张。
4. `CofiberRigidity` 通过实际底胞标签、E₆ 生存、B₅ 边界窗口、λ⁴ 检测和 λν 合成为零取得矛盾。这里出现的内部 `False.elim` 仍来自该可除关系与底胞非零性的冲突。

源码导入闭包含 453 个项目模块，无导入环；排除定理的源码导入闭包不含 `PaperResults`。更强的 kernel 实际类型和证明体常量闭包核验也确认：排除根完全不含 `lemma_toda2ext` 或 `corollary_2ext125`，两项新结果不能成为该排除证明的循环输入。旧的 `KIP126.ProofTools.Standard.generalizedLeibniz` 和 `KIP126.ProofTools.Standard.generalizedMahowald` 同样不在闭包中。

### 实际检查与精确上游责任

只读无 `-o` 审计探针 `/tmp/MainAudit20261019.lean` 对当前实际生产模块使用 `import all`，逐个遍历根的完整 kernel 类型及可见证明体中使用的常量；该导入仅用于独立审计。普通 `import KIP126.Main.PaperResults` 的单独消费探针也成功读取两项公共定理。两项探针均使用固定工具链的绝对路径执行 `lake env lean`，exit 0，没有写生产 olean。最初探针因 `OriginalStatements.olean` 缺失失败的事实保留在本轮日志；协调者编译当前目标后，完整探针才成功运行，未用缺失证明体推断完成。

| 根 | 实际项目声明闭包节点数 | 传递直接待补 | Main/ProofTools 待补 | 项目公理 / synthetic sorry |
| --- | ---: | ---: | ---: | ---: |
| `lemma_toda2ext` | 11091 | 116 | 0 | 0 / 0 |
| `corollary_2ext125` | 11088 | 116 | 0 | 0 / 0 |
| `eta_extension_excluded_of_d6_vanishes` | 11085 | 116 | 0 | 0 / 0 |

三个根的传递直接待补集合完全相同：AdamsSynthetic 39、Literature 50、E2Computation 23、AdamsCalculations 4。**116 项的名称、实际责任模块和完整 kernel 类型指纹逐项匹配当前待补清单**，没有未登记项；全部实际项目常量均可审计，没有隐藏为无证明体 axiom 的项目输入。三个根的公理集合仍为 `Classical.choice`、`propext`、`Quot.sound`、`sorryAx`。

完整 116 项清单、各根完整 kernel 打印类型、类型指纹、宇宙、源码 SHA-256、编译产物哈希以及原始依赖图哈希记录在本提案的 `evidence/conditional-proof-audit-20261019.json`；该证据 SHA-256 为 `344975c3160a65a4d15814f68c6b33a8da34fc040eb7f9f8c77110d0853639f6`。完整逐边原始图保留在 `/tmp/main-audit-20261019.json`；该临时文件的位置和 SHA-256 也存于证据中，不把临时文件视作永久归档。审计没有刷新接口锁、修改检查或增添许可责任；全仓库 `lake build` 及共享待补清单更新仍由协调者串行执行。

### 结论的准确范围

这次核验通过的是**原有两个完整条件命题的本地证明**，以及灰节点对相同公共互斥结论的准确绑定。原文直接路线所需的同一 bracket 的共同 Q3 值为零、以及任意源代表的未乘额外 λ 的误差吸收论证仍未独立补出；历史固定对象误差证据继续有效。本次没有从乘 λ² 的等式取消 λ²，没有把新高滤过代表冒认为原 bracket 成员，也没有改变条件命题的量词。

由于 116 项上游构造和定理仍待完成，本节不宣称固定模型的无条件一致性已获证明，也不宣称整个目标已经没有 `sorryAx`。未发现本次候选借用已知无前提矛盾的证据；依赖已登记上游责任与完成这些责任是两回事。当前可继续上游补证、直接原文构造研究及既有 Main 结论的普通消费；不需要据本次结果调整公共接口。
