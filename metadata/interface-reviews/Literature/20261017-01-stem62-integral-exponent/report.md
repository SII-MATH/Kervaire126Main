---
issue_id: "20261017-01-stem62-integral-exponent"
responsibility_module: "Literature"
targets:
  - "KIP126.Literature.Standard.stem62_exponent_two"
baseline_commit: "bef90640c4594af4db32c86837f9d95340d1e171"
worktree: "/tmp/kip-literature-20261017-01"
candidate_source_commit: "a484b981fad612eabe2bc7a01b54e049e9a01ce4"
api_file_and_sha256: "metadata/literature-api.json: 7a986fdb9f9a9f889568182d05ad238e9a6543bbbaed3c47028aa0c0494dcc10"
source_file_and_sha256: "KIP126/Literature/Standard.lean: 357a5d3c66d720303eee69e51147d1b2457977539308b5995bad40ed71c2f680; KIP126/Literature/Classical.lean: e0303eecdb15323e6257d398433c247ea3712ae982ffe1c3cffa296c446173f6"
reporter_agent: "/root/report_stem62"
independent_of_discoverer_and_implementer: true
evidence_level: "文献支持的普通球谱数学反例；运输到项目对象依赖已登记但未完成的 sourceRecognition；无无待补依赖 Lean 反例"
status: approved-interface-change
human_decision: "2026-10-17，本聊天用户：同意以上提案，修改原接口。具体范围见文末本轮批准记录。"
---

# 接口调整人审报告

## 请求人类决定的具体问题

当前接口断言**普通球谱全部 π₆₂ 元素都被 2 消去**。独立核验的 IWX 计算给出普通 π₆₂ 的非零三阶分量；当前固定对象的来源识别也明确采用普通球谱。二者无法同时支持这条接口的原语义。建议暂停该声明及其实际依赖闭包作为已知真命题使用。

需要人类明确选择以下范围；本报告未实施任一方案：

1. **方案 A（本报告优先建议的局部修正）**：保持普通 `Spectrum`、普通 `SphereSpectrum` 及六模块职责，把 `stem62_exponent_two` 改成只断言 2-primary 元素的指数二，精确签名见下文。批准后由协调者安排 Literature 内的真实证明及选定 θ₅ 的独立阶二证明；Main 的两个任意 synthetic 元素调用需由 Main 责任方重新核对实际 realization 是否落在 2-primary 部分，不能直接增添调用方假设。该局部修正**不保证**这两个任意选择结论仍成立，受影响 Main 闭包在重证前继续列为阻塞。
2. **方案 B（普通积分群的正确完整指数）**：删除错误的全群指数二声明，改为 `stem62_exponent_six`，精确签名见下文。这保存原量词和对象，改正结论，但也不能自动重建 θ₅ 或 synthetic 的阶二推论。
3. **暂不授权接口变更**：保留冻结接口及待补记录，明确将本条标为人审阻塞，继续其余独立 Literature 迁移。此选项不把当前原声明当作可用于新补证的真引理。

恢复历史 HF₂-local 全局背景是另一种架构选择，但涉及 AdamsSynthetic 的固定对象和 Main，不在本 Literature session 的实施范围。本报告不请求泛化授权来重定义 `Spectrum`、把普通球谱改名为完成球谱，或添加新的 source-identification 公理。

## 原接口、背景与问题成因

基线源码 `KIP126/Literature/Standard.lean:160–162`：

```lean
public theorem stem62_exponent_two :
  ∀ a : HomotopyGroup (C := Spectrum) 62 SphereSpectrum, a+a=0 := by
  sorry
```

这里 `Spectrum` 是 `KIP126.AdamsSynthetic.Standard.Spectrum : Type 1`，所用实例为 `KIP126.AdamsSynthetic.Standard.spectrumCategory : StableHomotopyCategory.{1,0} Spectrum`。`SphereSpectrum` 是该实例的幺半单位；`Sphere 62` 是其整数悬移，`HomotopyGroup 62 SphereSpectrum` 是从同一 `Sphere 62` 到该单位的 Hom，属于 `Type 0`，加法来自同一范畴的 `Preadditive.homGroup`。没有隐含的 2-primary、检测、θ₅、有限性或完备性前提。不存在声明级 universe 参数。

API 锁、派发 `full-targets.json` 和源码一致。锁中的完整 elaborated rendering 为：

```lean
∀ (a : KIP126.StableHomotopy.HomotopyGroup.{1, 0}
    62 KIP126.StableHomotopy.SphereSpectrum.{1, 0}),
  Eq.{1} (HAdd.hAdd.{0, 0, 0} a a) 0
```

为显露 printer 隐藏的固定参数，同一类型可展开书写为：

```lean
∀ (a : @KIP126.StableHomotopy.HomotopyGroup.{1, 0}
    KIP126.AdamsSynthetic.Standard.Spectrum
    KIP126.AdamsSynthetic.Standard.spectrumCategory
    (62 : ℤ)
    (@KIP126.StableHomotopy.SphereSpectrum.{1, 0}
      KIP126.AdamsSynthetic.Standard.Spectrum
      KIP126.AdamsSynthetic.Standard.spectrumCategory)), a + a = 0
```

类型指纹 `10913749501484541634`，基线证明体指纹 `2896609237660016311`。`metadata/proof-obligations.json` 通过 row.module 及责任映射将它登记为 Literature 的 `pending-proof`。基线实际证明体只有 `sorry`；API 的 axioms 包含 `sorryAx`。本审查没有新运行 kernel capture，因此此完整类型及指纹使用既有锁，源码事实另作核对。

当前用途是推导选定经典 θ₅ 的阶二，以及 Main 中任意 synthetic 类在 `(62,64)`、`(62,70)` 的阶二。后两处取 realization 后的任意 `α : HomotopyGroup 62 SphereSpectrum` 直接代入本声明。它们没有在这次代入前证明 α 是 2-primary。

### 历史源确实不同，且没有实际证明可迁入

在只读提交 `a484b981fad612eabe2bc7a01b54e049e9a01ce4`（下称 a48）中：

- `Literature/Source.lean:62–69` 的 `ClassicalSourceResults.stem62_exponent_two` 是结果输入字段。
- `Literature/Hypotheses.lean:53–72` 的 `LiteratureTheorems.classical_stem62_exponent_two` 是结果输入字段。
- `Main/Literature/SourceComparisons/Theorems.lean:71–79` 仅复制 `input.classical_stem62_exponent_two`。
- `Main/Literature/AdamsSynthetic/Theorems.lean:90–97` 仅复制 `hS.stem62_exponent_two`。
- `Literature/Assumptions.lean:11` 用 `axiom adamsSyntheticResults : LiteratureHypotheses` 提供包；当时 `metadata/external-inputs.json` 将本字段标为 `external-result-assumption`，引用 IWX 的 classical E∞ 数据。

a48 的对象链是：`Literature/Standard/Foundation.lean` → `AdamsSynthetic.Standard.classicalContext.foundation` → `HF2AdamsContext Spectra.completionModel`。`Literature/Standard/ClassicalContext.lean:15–16` 从 `hf2AdamsContext_exists` 选出该上下文；`Literature/Background/HF2Completion.lean`、`Background/ClassicalAdams.lean` 分别假设反射与 HF₂ Adams 上下文存在。`Def/ClassicalAdams/Context/Data.lean:290–295` 的 `sourceComparison` 指向完成源；`Def/StableHomotopy/Spectra/Comparison.lean:23–34,58–60` 的范畴等价起点为 `CompletedSpectrum`，sphere 是 `Q.localization.obj Prespectrum.sphere`，同伦比较使用 `Q.replacement.obj X`。

所以历史固定版本针对 HF₂-local completion sphere；本报告**没有**把它判为普通球谱上的历史假命题。它即使数学上成立也仍是外部结果输入，没有可迁移的 Lean 证明。当前 `literature-contracts.json:3377–3385` 却将迁入字段解释为全部实际经典球谱类，省去了历史对象的局部化区别。

问题分类：对当前普通球谱的预期语义，这是**假命题及对象/局部化约定错配**；对历史 completion 背景，这是**源中仍未证的输入字段**。当前 `sorry` 是形式化证明缺口，不是产生这个数学问题的实现算法错误；单纯补上战术不能修复原语义。

## 真实前提与对象核对

| 前提或对象条件 | 是否满足 | 证据及仍依赖的待补责任 |
| --- | --- | --- |
| 固定范畴、宇宙和加法使用同一实例 | 类型已固定；实例尚待构造 | `Context.lean:78–84`；`Standard/Background.lean:24–27` 中 `Spectrum`、`spectrumCategory` 均待补。没有替代群模型。 |
| 固定 sphere 是普通稳定 sphere | 已登记的明确识别要求；尚未完成证明 | `Standard/Source.lean:32–35` 的 `sourceRecognition`；`Internal/Source/Recognition.lean:37–41` 的等价起点是普通 `SourceCategory.{0}`，`sphereIso` 接同一普通源 sphere。该项责任属于 AdamsSynthetic。 |
| 同伦 degree 62 方向正确 | 是 | `HomotopyGroup n X = Sphere n ⟶ X`；源代表满足 dimension = d + stage，取 d=62，符合稳定 π₆₂，不是负茎或 62 维非稳定群。 |
| 加法与真实稳定群相符 | 识别字段明确要求；仍依赖同一待补对象 | `Recognition.lean:61–82` 的 `homotopy`、`homotopy_zero`、`homotopy_add` 使用实际 cubical loop 拼接。不是只有类型等价。后接 `sphereIso` 的 Hom 运输由预加性保持加法。 |
| 反例元素满足原量词 | 普通球谱数学上满足 | 原目标量化所有 a；三阶元素没有被任何条件排除。 |
| 2-primary 或 2-local 条件 | **没有** | 原声明没有此假设。存在 HF₂ 系数和 mod-2 Adams 页不意味着原 sphere 已局部化。 |
| 边界/范围 | 62 位于已确定范围 | IWX 两个正式版本的 62 行无不确定标记；所列后期不确定性不影响这一行。 |
| a48 与当前对象相同 | **否，不能直接运输** | a48 使用 replacement/localization 后的 completion sphere；当前 sourceRecognition 指向未完成的普通 sphere。必须保留实际比较，不存在能保留奇素数类同时把其倍增归零的加法同构。 |

普通源的实现也单独核对过：`Internal/Source/Prespectrum.lean` 把稳定同伦定义为实际 cubical based maps 对同伦和稳定化关系的商，弱等价是所有整数度上诱导双射的映射，`SourceCategory` 是对此类映射的 localization；`Internal/Source/Sphere.lean:110–127` 的 sphere 是离散两点球逐次 reduced suspension，没有 mod-2 商或 2-completion。来源实现的完整拓扑正确性没有在本报告重新形式化。

## 独立证据与复现

### 原始文献及数学反例

报告员自行通过 web 阅读了两篇原始论文的相关表格和说明，未用发现者的摘要代替查证：

1. Isaksen–Wang–Xu，*Stable homotopy groups of spheres*，PNAS **117** (2020), 24757–24763，doi:10.1073/pnas.2012335117。[论文镜像](https://www.sas.rochester.edu/mth/sites/doug-ravenel/otherpapers/IWX-published.pdf)，纸页 24759 / PDF 第 3 页，Theorem 1.1、Table 2。该定理涵盖完整稳定群；相邻说明将表的三组列解释为直和，并定义幂号表示多个循环群的直和。62 行前三部分为 `2⁴ | 3 | ·`；最后一列平滑结构群不用于本反例。
2. 同作者，*Stable homotopy groups of spheres: from dimension 0 to 90*，Publ. Math. IHÉS **137** (2023), 107–243，doi:10.1007/s10240-023-00139-1。[正式全文](https://www.numdam.org/item/10.1007/s10240-023-00139-1.pdf)，纸页 112 的 Corollary 1.3 与三部分直和说明，纸页 114 / PDF 第 8 页 Table 1 的 62 行相互吻合。正文计算方法主要讨论 2-completed 情形，汇总表仍明确列出奇素数部分；不能把正文的 2-completed 约定覆盖表内的奇素数栏。

因此普通稳定群具有加法群分解

\[
\pi_{62}^{S}\cong (\mathbb Z/2)^4\oplus\mathbb Z/3.
\]

取三阶直和因子的一个非零元素 a。若原结论 `a+a=0` 成立，则它与 `a+a+a=0` 相减得 `a=0`，矛盾。这是普通固定球谱上的文献支持数学反例；无需知道三阶元素的 Adams 标签，也不依赖任何 KIP126 待补定理来证明上述群论矛盾。

固定对象的条件性运输可以具体说明：令 `R := Standard.sourceRecognition`，设 b 是普通源球谱 62-stem 中该三阶类，则当前 sphere 上的候选为 `(R.homotopy classicalSpherePrespectrum 62).symm b ≫ R.sphereIso.hom`。源同伦比较使用同一个 R，后接同一个 `sphereIso.hom`；`homotopy_add`、`homotopy_zero` 与同构后复合的加性会保留 `3a=0`、`2a≠0`。这里 b 的文献计算及 R 的构造尚未形式化，所以此表达式是明确的数学运输方案，不是声称已经生成的 Lean 项。

运输到当前 Lean 常量时仍须完成 `Spectrum`、`spectrumCategory`、`sourceRecognition` 及普通源与文献常规定义的识别，并把文献计算形式化。故本报告在**项目 Lean 环境层面**只主张条件性反例，不能声称已有不含项目未证依赖的 `∃ a, a+a≠0` 项。当前有 `sorryAx` 的环境能形式上证明什么不构成本报告的反例。

### 同目录最小复现和实际结果

文件：

- [reproduce.py](reproduce.py)：仅调用 `git show`/`git grep` 和 Python；不修改项目，不运行 Lake。
- [evidence.json](evidence.json)：实际运行输出，含两提交的原始代码摘录、完整文件 SHA-256、目标 API 行和直接引用。

命令：

```sh
python3 /inspire/hdd/global_user/czxs25250150/Kervaire126Main/metadata/interface-reviews/Literature/20261017-01-stem62-integral-exponent/reproduce.py /tmp/kip-literature-20261017-01
```

报告时实际结果：进程 exit 0；基线 Standard/Classical 哈希精确匹配派发值；原目标证明体为 `sorry`，直接引用集合与下文一致。附带的有限算术检查取表格分解坐标 `a=(0,0,0,0,1)`，得到 `2a=(0,0,0,0,2)≠0`、`3a=0`，断言全部通过。该算术检查只校验表格解释后的群论运算，**不是固定 Lean 对象的构造，不是独立于文献的拓扑计算，也不是抽象模型失败冒充固定对象反例**。

本次没有运行 Lean、Lake、freeze 或任何测试，不提交编译通过的反例。现有 API 的 axiom 清单仅为已有捕获记录。曾尝试直接联网取得论文 PDF 作本地复核，但环境网络访问拒绝；文献证据实际来自可用 web 工具返回的原文和表格文本，两篇的行与列说明一致。

### 循环、未证及不一致环境审计

- 数学反例未调用 `stem62_exponent_two`、`theta5_order_two`、任何由它们推导的 Main 定理，未用 `False.elim` 或把 sorry 当反证证据。
- 运输依赖只声明为条件：`Spectrum`、`spectrumCategory` 和 `sourceRecognition` 尚未完成。后者有实际 sphere、整数同伦及加法的同一见证要求，不是改名后的替代模型。其责任仍归 AdamsSynthetic。
- a48 的 `adamsSyntheticResults`、背景 existence axioms、结果包字段不是证明；其投影链没有消除任何数学待补。
- 当前私有 `ClassicalResults` 是带条件的参数记录。其 `theta5_order_two` 和 synthetic order-two helper 使用记录里的指数二字段；这些是条件推论，不能用于证明固定 Standard 目标。未构造该记录本身不产生逻辑矛盾。
- 已读到的直接及下游源码链没有反向调用本目标来完成本目标；但这不是整个项目一致性的证明，也不排除其他接口的独立争议。未审计的问题不据此扩展冻结全模块。

## 方案及精确差异

### 首先评估保留原接口的内部方案

不能在保持普通 sphere、全部 a、实际加法与 IWX 计算的同时给出原接口的正确内部证明。把 realization 后的某个特定 a 证明成 2-primary 只能修复调用处的特例，不能完成原先无条件的全群目标。把 `Spectrum` 偷换为 2-completed 背景、对加法另选实例、从既有不一致责任推出 False，都会改变对象/语义或伪造证明。

**可保留的局部声明**是当前公共 `theta5_order_two : theta5 + theta5 = 0`：该结论只涉及 Literature 选定的 θ₅，可能用真实选定对象和阶二来源直接证明。a48 中独立的 `theta5_order_two` 也只是输入字段，不能用投影代替该补证。需要构造/比较所选 θ₅ 的确是原文中的阶二代表；只知道被 h₅² 检测不能在未核对局部化和奇素数不定性时自动完成此事。

### 方案 A：限制到同一积分群的 2-primary 元素

精确原签名：

```lean
public theorem stem62_exponent_two :
  ∀ a : HomotopyGroup (C := Spectrum) 62 SphereSpectrum, a + a = 0
```

候选签名（仅提案，未应用、未执行 Lean 检查）：

```lean
public theorem stem62_exponent_two :
  ∀ a : HomotopyGroup (C := Spectrum) 62 SphereSpectrum,
    (∃ n : ℕ, (2 ^ n : ℕ) • a = 0) → a + a = 0
```

语义差异：保留 category、sphere、degree、加法和结论，增加对同一 a 的 2-primary 条件，所以是更弱的公共断言。`n=0` 只允许 a=0，不会误纳入三阶元素；没有 universe 或实例变动。Literature 应证明这一真实定理和选定 θ₅ 的具体实例，不能把二者作为新公理或新结果包留给消费者。

`Standard.theta5_order_two` 需要 Literature 内部的真实 θ₅ 2-primary 证明，或独立阶二证明。Main 的 `theta_degree_order_two`、`two_torsion_62_70` 当前对任意 synthetic 类量化，不自动获得新增前提。不能以源代码能多传一个假设作为默认修复；相应负责人需用实际 ν/realization/source 比较重证所需特例，或另行人审其结论。这一方案授权若仅限 Literature，不授权本报告员修改 Main，也不授权悄悄新增 Main 公共假设。

私有 `ClassicalResults` 可继续作为条件记录保留；若协调者希望将其作为 Standard 实现辅助，须同步改其字段为上述真实适用范围并重新证明 helper，但这不是对当前固定接口的一个现成实现。

### 方案 B：完整积分群指数六

候选替换声明（仅提案）：

```lean
public theorem stem62_exponent_six :
  ∀ a : HomotopyGroup (C := Spectrum) 62 SphereSpectrum,
    (6 : ℕ) • a = 0
```

语义差异：不改变任意 a 的量词和对象，将“2 消去”改成“6 消去”，更弱且覆盖三阶因子；同时删除/替换旧公共名称，需明确批准。不能保留 `stem62_exponent_two` 名称却把它暗改成指数六而不更新契约。选定 θ₅ 阶二及 Main synthetic 阶二仍须独立处理，不能从指数六推出。

### 其他方向及其局限

仅删除本错误接口、独立保留并证明选定 θ₅ 阶二，是比方案 B 更小的 API 裁剪，但删除同样需要人类明确授权，且仍暴露相同 Main 任意元素闭包。把所有当前对象恢复为历史 HF₂-local 完成对象会涉及新固定对象、同伦与加法比较、ν、λ 反演及现有 Main 的关联；不能在保留原冻结对象时完成，也不能只改 Literature 一处。因此这里不把该架构方向当成已指定精确签名、可直接实施的局部方案。

## 下游影响

### 已逐边核对的直接调用与源码闭包

直接固定声明调用只有三处：

| 调用声明 | 位置 | 影响 |
| --- | --- | --- |
| `Literature.Standard.theta5_order_two` | `Literature/Standard.lean:209–210` | 当前证明直接代入本目标；语句可保留，证明必须重做。 |
| `Main.Internal.Choice.theta_degree_order_two` | `Main/Internal/Choice/OrderTwo.lean:45–76`，调用在 69 | 任意 `(62,64)` synthetic 类的 realization α 直接代入。 |
| `Main.Internal.Theta.two_torsion_62_70` | `Main/Internal/Theta/OrderTwo.lean:50–80`，调用在 59 | 任意 `(62,70)` synthetic 类的 realization α 直接代入。 |

在基线源码上，已核对的向下传播是：

```text
stem62_exponent_two
├─ Literature.Standard.theta5_order_two
├─ Main.Internal.Choice.theta_degree_order_two
│  ├─ Main.lambda_eta_theta_square_independent
│  │  ├─ Main.any_choice_criterion
│  │  └─ Main.delta_h6_square_eq_lambda_eta_theta_square
│  ├─ Internal.Choice.theta5_square_nonzero_detection_invariance_of_pages
│  │  └─ Main.theta5_square_nonzero_detection_choice_invariant
│  │     ├─ Main.theta5_square_nonzero_detection_choice_equivalence
│  │     └─ Internal.Selected.selected_reverse
│  │        └─ Main.conditions_imply_d12
│  │           └─ Main.h6_square_differential_dichotomy_and_criterion
│  └─ SectionSeven.Internal.synthetic_theta_b_toda / theta_b_multiplied_shuffle
└─ Main.Internal.Theta.two_torsion_62_70
   └─ SectionSeven.Internal.synthetic_theta_b_toda / theta_b_multiplied_shuffle
      └─ SectionSeven.target_nu_divisible
         └─ SectionSeven.eta_extension_excluded_of_d6_vanishes
            ├─ Main.eta_extension_excluded_of_d6_vanishes
            ├─ Main.table1
            └─ Main.h6_sq_permanent
```

关键边可复核于 `Main/ChoiceIndependence.lean:113–114,146,165,172`、`BoundaryFormula.lean:29–31`、`Internal/Choice/Invariance.lean:29`、`Internal/Selected/Assembly.lean:80`、`DifferentialCriterion.lean:35,49`、`Internal/Theta/TodaExistence.lean:77–81`、`SectionSeven/ThetaToda.lean:35–40,77`、`SectionSeven/NuTarget.lean:42–44`、`SectionSeven/Final.lean:14–18`、`H6SquarePermanent.lean:16–28`。`Main/DifferentialReduction.lean:25,38–45` 还有 `h6_sq_permanent` 的后续推论。这是逐源码调用审计，不冒充本次重新获取的 kernel 全依赖图；需把上述节点的实际所有消费者纳入后续统一核验。

本报告没有断言这些下游结论数学上为假，只指出其当前证明通过争议目标。`Choice.realization_additive` 和 `Choice.realization_injective_of_lambda_powers` 本身不调用该目标；后者被 `Internal/High125/Detector.lean:39` 使用。应按声明依赖阻塞，不能因为同在 `OrderTwo.lean` 就冻结这些独立引理。

### 责任、记录和测试

- Literature 仍负责文献原条件、正确 62-stem 版本、选定 θ₅ 及同一对象比较。AdamsSynthetic 仍负责已登记的范畴和源识别；本报告不接手或转移责任。Main 负责自身局部推导，不应被默认要求提供新公共假设。
- 若授权改 API，协调者应精确更新 `literature-api.json` 的声明名/完整类型/指纹/导出、`literature-contracts.json` 的 `literature-classical` 和历史字段映射、`literature-sources.json` 的实际证明来源/哈希、`proof-obligations.json` 的真实责任；保留历史原始字段、原始来源和 a48 未证性质。不得盲刷六模块锁或把本问题批准扩展为其他接口批准。
- 若授权的变更确实触及 Main 公共类型或记录，需先取得对应模块和具体范围授权，交该模块负责人安排；不能本报告员直接改写。仅改证明不改变公共接口时仍需遵守 session 的单模块边界。
- `Tests/Literature/Consumers.lean:14` 普通导入消费选定 θ₅ 阶二；`Tests/Literature/Interface.lean:27–55` 锁类型/宇宙/公理及导出；`Literature/InternalAudit.lean:47–67` 容许已登记 sorry 并核对指纹。构建成功不会消除此数学问题。
- 后续实施应保留原有 LiteratureChecks、ArchitectureChecks、Integration/Trust 覆盖，并运行 source inventory 与完整 `lake build`。`Tests/Trust.lean` 保证测试自身没有新公理/sorry，不保证全部传递上游责任完成。`Tests/Architecture.lean` 的主目标类型检查不能替代本审查。

## 阻塞范围与继续项

确切应暂停的新补证用途：`Standard.stem62_exponent_two` 原语义；其上述三个直接证明体；继续使用这些证明体作为数学证据的依赖闭包。已存在源码和待补记录由协调者保留，接口冻结期间本报告不删除任何声明。Main 主目标当前证明触及该链，因此不能把其编译成功描述成已获得无争议数学证明。

可继续：不依赖本条的 realization/λ 反演及权移比较、E₂ 自由部分、有限 λ 商和 E∞ 公式、商代数、BHS lift、May/Moss/Toda 的独立公共定理、η/ν 及 tmf 等真实对象比较与证明；每项仍需各自核对来源与前提。当前 session 的非阻塞迁移由协调者继续安排。本问题不要求等待本报告才研究它们，也不使这些独立接口自动失效。

快照说明：报告读取期间协调者在独立工作树串行整合了 `Standard.lean` 的其他证明，文件 SHA 曾变为 `2e2a03e0fe64489c93f03d32ef08dfc7a110c0b2bd8c61cb3d0e4b960a4e08d5`；核对的变更仅涉及别的迁移项，未改本目标及其直接调用。`evidence.json` 使用 `git show` 固定在派发基线，故不会将并发新证明归给本报告或覆盖他人的改动。

## 已确认事实与未决部分

已确认：原接口无 2-primary 前提；当前源识别要求普通 sphere 并固定加法；两篇 IWX 原文的 62 行含三阶因子；a48 绑定 HF₂-local 背景且只通过结果包输入该字段；当前本条是直接 sorry，并有实际 Main 调用。

未决：文献计算的 Lean 实现、sourceRecognition 的完成、选定 θ₅ 的独立阶二构造、Main 任意 realization 的真实 2-primary 范围及其下游重证。未找到无待补依赖的项目 Lean 反例；没有用这一局限暗示原普通球谱全群指数二仍可能与所核对的文献计算相容。

## 人类审核记录

尚无人类对本报告及任一具体方案作出决定。`human_decision: null`。协调者、发现者、独立审计员或报告员的意见，以及等待过程，均不构成授权。未经明确批准，上述候选签名只存在于本报告。


## 本轮批准记录（2026-10-17）

用户在本聊天阅览七份报告摘要后明确回复：

> 同意以上提案，修改原接口

本报告获准范围：

- 方案 A：stem62_exponent_two 增加同一元素的 2-primary 条件；保留普通球谱。
- 不批准改用指数六方案或静默替换完成球谱；下游新增假设/待补另审。

该批准不是新增公理、额外待补责任、任意 Main 公共前提或未列明接口变更的授权。原文中的“尚未批准”保留为历史阶段记录；实现及实际验证另记，批准不表示证明已经完成。
