---
issue_id: ProofTools-20261022-finite-level-consequences
title: 公开两个已证明的有限层微分与经典延拓推论
summary: 已按 2026-10-22 用户明确“同意”的授权实施两个完整 ProofTools 公共定理、公共入口、相应接口锁和消费者测试，并绑定 Blueprint 5.53、5.56。独立核对正式类型与批准候选一致，既有声明和导出未变、待补基线未变；完整构建 3722 jobs 和 49 项 Blueprint 测试通过。两结论无 ProofTools 本地证明洞，仍继承 52 项已登记上游责任。
responsibility_module: ProofTools
targets:
  - KIP126.ProofTools.Standard.cutoffAdamsDifferentialAtLevel
  - KIP126.ProofTools.Standard.finiteLevelExtensionToClassical
  - sem:ProofTools:ss-adams-soundness
  - sem:ProofTools:ss-classical-soundness
baseline_commit: fa6c729fe2f1b251ef6ead8838a0fbbb0975f8aa
reporter_agent: /root/audit_level_targets
independent_of_discoverer_and_implementer: true
evidence_level: 独立完整源码、elaboration 后实际类型、固定对象与数学前提审查；候选及全量 Lean 构建通过；实际递归依赖无 ProofTools 本地证明洞，上游传递待补全部已登记
status: approved-interface-change
resolution: implemented-and-validated
human_decision: '2026-10-22 用户对本报告所述最小两项公开声明及绑定方案明确回复“同意”。批准新增 KIP126.ProofTools.Standard.cutoffAdamsDifferentialAtLevel 与 KIP126.ProofTools.Standard.finiteLevelExtensionToClassical，纳入 KIP126.ProofTools 公共入口，精确更新相应 ProofTools 接口锁和消费者测试，分别绑定 sem:ProofTools:ss-adams-soundness（5.53）与 sem:ProofTools:ss-classical-soundness（5.56）。其它公共声明的名称、类型、前提、语义、对象关联和导出保持不变；不新增公开谓词、数学假设、公理或待补责任，不修改上游接口或依赖锁。批准实施不等于已完成最终构建验收。'
---

# 有限层微分与经典延拓推论的公共接口

## 已批准的范围

已将获准的 [完整公共包装候选](evidence/FiniteLevelConsequences.lean) 实施于 [FiniteLevelConsequences.lean](../../../../KIP126/ProofTools/FiniteLevelConsequences.lean)，新增且仅新增两个完整公共定理：

1. `KIP126.ProofTools.Standard.cutoffAdamsDifferentialAtLevel`，绑定 Blueprint `sem:ProofTools:ss-adams-soundness`，当前编号 5.53。
2. `KIP126.ProofTools.Standard.finiteLevelExtensionToClassical`，绑定 Blueprint `sem:ProofTools:ss-classical-soundness`，当前编号 5.56。

两个声明分别调用已完成的同模块私有证明。其余辅助构造保持私有，未新增公开命题谓词，未改任何现有公共声明的名称、类型、前提、语义、对象关联或导出。新增声明已列入 ProofTools 接口锁及公共入口，并由普通导入的消费者验证。本次未修改其他模块或依赖锁，未新增公理或证明洞。

用户此前已确认这两个 Blueprint 数学陈述，并要求直接尝试证明和形式化。2026-10-22，用户对完成候选后提出的最小两项公共包装及绑定方案明确回复“同意”，上述具体范围现已获准，无需再次确认。该授权只涵盖本报告列出的两项公开声明、公共入口、相应锁和消费者测试及两项完整结论绑定，不延伸到其它接口变更。

## 背景与现有接口

本次实施前，两个 Blueprint 条目已有传统数学陈述，尚无直接绑定其完整结论的公共声明；现已分别绑定上述两项完整定理。其正文与数学证明以 [ProofTools.tex](../../../../blueprint/chapters/ProofTools.tex) 中上述两个稳定标签为准；本报告不另立相对 AimPaper 的修正版陈述，也不修改或复制 `corrections.yaml`。

候选直接复用以下现有表达与工具：

- `Standard.LevelFiniteExtension`：同一实际有限商映射上的指定源、目标无限页类、标签代表及延拓方程，包含页数和长度范围。
- `Standard.LevelFiniteNoCrossing` 与 `Standard.LevelBoundaryNoCrossing`：实际映射、固定 stem 与 weight 下的完整 crossing 三角。
- `InfiniteExtension`、`TowerExtensionEquation`、`TowerEssentialExtension`、`DifferentialAt`、`IsPermanentCycle`、`ClassicalDetects`。
- `RealizationCoordinates model`、`LambdaInversionAdamsComparison model R`：已有 Proposition 5.14 的实现背景与检测比较。
- 已证明的四边 cutoff 方块、带权边界比较、有限窗口反射、无 crossing 的共同源代表及归一化实现方块。

当前完整私有候选是：

- [CutoffDifferential.lean](../../../../KIP126/ProofTools/FiniteLifting/CutoffDifferential.lean) 中 `KIP126.ProofTools.Internal.FiniteLifting.cutoffAdamsDifferentialAtLevel`。
- [LevelClassicalLift.lean](../../../../KIP126/ProofTools/FiniteLifting/LevelClassicalLift.lean) 中 `KIP126.ProofTools.Internal.FiniteLifting.finiteLevelExtensionToClassical`。
- [LevelSourceLift.lean](../../../../KIP126/ProofTools/FiniteLifting/LevelSourceLift.lean) 中的私有正层源代表与实现比较，供第二个完整候选调用。

## 固定对象与完整类型边界

两项均固定 `KIP126.AdamsSynthetic.Standard.model`，经典对象为该模型原有的 `ClassicalObject`，映射是 `X.obj model.auxiliary ⟶ Y.obj model.auxiliary`。实际 elaborated 类型中的模型宇宙为 `{1,0,1}`，两声明无额外模型、自由宇宙或类型类参数。不泛化到任意抽象谱序列，不改成任意线性映射，也不缩小为某一个数值例子。所有有限商、归一化映射、移位、无限页类及检测使用此同一模型。完整实际类型见 [kernel 探针输出](evidence/finite-level-theorem-audit.log) 及 [结构化审计](evidence/finite-level-theorem-audit.json)。

### cutoffAdamsDifferentialAtLevel

完整候选签名以 `CutoffDifferential.lean` 最后一个私有定理为准，公开时只改变其可见性、责任命名空间及包装位置，保持所有参数和类型。其参数及前提逐项为：

- `X Y f`；`page level : ℕ`；`r m l s t κ : ℤ`。
- `x : Ambient model X (s,t)`、`y : Ambient model Y (s+m,t+m)`、`u : Ambient model X (s+r,t+r-1)`、`v : Ambient model Y (s+r+l,t+r-1+l)`。
- `2 ≤ page`、`page ≤ r`、`e(f) ≤ m ≤ page-2+e(f)`、`e(f) ≤ l`。
- `u`、`v` 的永久循环资格，允许零类和边界标签。
- 指定的 `DifferentialAt model X r ... x u`，同一 `LevelFiniteExtension X Y f page level m s t x y`，以及指定的 `InfiniteExtension model X Y f l (s+r) (t+r-1) u v`。
- `1 ≤ κ ≤ r+l-m`。
- 同一实际方块上 `LevelBoundaryNoCrossing ... r` 或 `LevelFiniteNoCrossing ... m`。
- 对移位后的底映射，在 `p=(t-s,t+e(f)-level)`，不存在源、目标滤过 `a,c` 满足 `s+r<a≤c≤s+r+l` 且 `s+m+κ≤c` 的实际本质延拓。
- 存在有限目标类 `η`，由指定目标标签 `λ^(level+m-e(f))y` 代表，并满足同一实际右边界的长度 `κ-1` 零延拓。
- 同一右边界、同一 `p` 上不存在 `s+m<a≤c≤s+m+(κ-1)` 的实际本质延拓。

结论完整保留为：

```lean
DifferentialAt model Y (r+l-m)
  (s+m,t+m) (s+r+l,t+r-1+l) y v
```

`DifferentialAt` 同时断言页数至少为 2 及实际 Adams 微分，不只是指数等式。右边的 `η` 由指定标签的无限页代表唯一性与有限顶部延拓的目标认同；它不是额外独立选取的标签，也不把所求非零微分作为前提。上述 crossing 条件包括长度零和末层。

### finiteLevelExtensionToClassical

完整候选签名以 `LevelClassicalLift.lean` 最后一个私有定理为准，参数与结论如下，公开包装不增加任何条件：

```lean
(R : RealizationCoordinates model)
(hcomp : LambdaInversionAdamsComparison model R)
(X Y : ClassicalObject)
(f : X.obj model.auxiliary ⟶ Y.obj model.auxiliary)
(page level : ℕ) (m s t : ℤ)
(x : Ambient model X (s,t))
(y : Ambient model Y (s+m,t+m))
(hx : IsPermanentCycle
  (model.classical.obj (X.obj model.auxiliary)) (s,t) x)
(he : KIP126.ProofTools.Standard.LevelFiniteExtension
  X Y f page level m s t x y)
(hnc : KIP126.ProofTools.Standard.LevelFiniteNoCrossing
  X Y f page level m s t) :
IsPermanentCycle
  (model.classical.obj (Y.obj model.auxiliary)) (s+m,t+m) y ∧
  ∃ a : HomotopyGroup (t-s) (X.obj model.auxiliary),
    ClassicalDetects (model.classicalConvergence X) (s,t) x a ∧
    ClassicalDetects (model.classicalConvergence Y) (s+m,t+m) y
      (eqToHom (congrArg (Sphere (C := Spectrum))
        (show (t+m)-(s+m)=t-s by omega)) ≫ a ≫ f)
```

其中 `he` 包含 `2≤page`、`e(f)≤m≤page-2+e(f)`，有限商长为 `page+level-1`，权重为 `t+e(f)-level`。`hnc` 精确包含 `s<a≤c≤s+m`，保留长度零及最后一层 `c=s+m`。结论要求一个共同经典代表 `a` 与其实际像 `a ≫ f`，不只分别证明两类存活。

不预设目标永久性、完整目标提升、正层 `comparison.nuE2` 校准、非零性或本质性。`e(f)∈{0,1}` 由既有 `normalizedExponent_le_one` 消去，未留作调用者的新前提。已有实现背景 `R,hcomp` 与 Blueprint 的 Proposition 5.14 背景一致。

## 独立证明审查

审查者 `/root/audit_level_targets` 未参与三个候选源码的实现。先独立检查已批准数学目标、范围和可能反例，再对完整实际候选逐项回译，未以源码名称或注释代替类型。审查发现并反馈一次公共谓词解包的包装错误，实施者已改为经现有 `levelFiniteExtension_iff_internal` 构造内部 witness；其最终版本包含在下述哈希中。

第一个候选从同一实际方块提取右边代表及它自己的边界，使用已证明的带权反向边界比较。设 `q=page+level-1`、`d=level+m-e(f)`、`D=r+l-m`，所需 `0≤d<q`、`q-d≤D-1`、`D≥2` 及 `D-q-1+d=r-page+l-e(f)` 均由原范围推出。底边只使用获准的 cutoff 区间，没有加强为全底边无 crossing。没有引用原 Proposition 5.10 的争议 crossing 等价。

第二个候选先由源永久性选取未移位底权重代表，实际移位得到零层归一化代表，再乘 `λ^level`。实际 λ/shift 相容性及商包含方块给出 intrinsic 有限源标签；零层校准与 `RealizationCoordinates.lambda` 保证它实现为由原 `x` 检测的同一经典代表。没有假定尚未建立的正层 `comparison.nuE2` 全局校准。

无 crossing 引理允许使用该指定 full source，同时保留有限延拓的指定目标。由商包含自然性，其有限目标恰为该源的实际归一化像的投影。可见指数 `level+m-e(f)<q` 给出目标永久性和同一 full image 的检测；最后归一化实现方块识别其经典实现为同一 `a` 的 `f_*a`。未假定 full target lift，未将任意较强 zero-level `InfiniteExtension` 作为隐藏中间结论。

未发现满足全部真实前提的反例、对象或权重错配、循环证明。此前弱部分标记数据的反例不适用于这两个实际数学陈述，不计作本次反例证据。

## 检查证据与传递责任

已独立读取并核对三个最终候选源码的 SHA-256：

| 源文件 | SHA-256 |
| --- | --- |
| `FiniteLifting/CutoffDifferential.lean` | `8d3dc5b12f76d58894c79f91fd13f0182d5b5c3905c89bd6a0a3d229cb23e338` |
| `FiniteLifting/LevelSourceLift.lean` | `a087d450d23b760aa726dc07d79e4dca1499c4358a474635651d33561a36fd0c` |
| `FiniteLifting/LevelClassicalLift.lean` | `9eff31c96c2d0ea4362b19beb32c15efd62daa7e1fa27d225f053fb7524bca54` |
| `evidence/FiniteLevelConsequences.lean` | `6eafd5db4ac3cfa415c906217a5bbb6bf8aa94407b845746eb620e2d4cdc7394` |

协调者执行的检查及复现命令完整记录在 [验证摘要](evidence/verification.md)。独立审查者读取实际构建日志、最终三个源码和完整公共包装候选，并核对上述哈希与其内容：

- 三个候选模块构建成功，3336 jobs；完整 `lake build` 成功，3721 jobs。
- ProofTools 内部审计包含 6064 个声明，仅保留原已登记的 1 项本地待补，无项目公理。两个完整私有定理均作为显式根加入递归本地证明洞检查并通过。
- 完整公共包装候选经 `lake env lean` 检查成功，无诊断；其正式实施及公共入口消费又通过下述实施后完整构建。
- 源码清单检查覆盖 622 个项目文件和 35 个消费者或审计文件；49 项 Blueprint 测试通过，`git diff --check` 通过。

[可复现探针](evidence/FiniteLevelTheoremAudit.lean) 导入相关五模块完整内部审计，输出实际完整类型，并遍历声明类型和实际证明体所引用的项目常量。遇到 ProofTools 本地 `sorry` 会直接报错。最终 [结构化结果](evidence/finite-level-theorem-audit.json) 与 [实际日志](evidence/finite-level-theorem-audit.log) 均已独立读取，结果为：

| 候选 | ProofTools 依赖数，均无本地洞 | 继承的上游直接待补责任 |
| --- | --- | --- |
| cutoff 微分推论 | 861 | 52：AdamsSynthetic 35、E2Computation 2、Literature 15 |
| 有限层经典实现推论 | 322 | 46：AdamsSynthetic 35、Literature 11 |

两者上游责任去重后共 52 项，独立以结构化比较逐项对照 `interface/baselines/proof-obligations.json`，未登记集合为空。完整名称及定义源模块在审计 JSON 中。两个 E2 输入是既有 `KIP126.Computation.Standard.sourceCoordinates` 和 `KIP126.Computation.Standard.comparison`，责任按实际源模块 E2Computation 计；没有调用 AdamsCalculations 或 Main 的后续计算。实际 ProofTools 依赖中不含争议的 `finiteCrossing_iff_syntheticCrossing`。

两个实际公理闭包均为 `propext`、`Classical.choice`、`Quot.sound` 及继承上游待补的 `sorryAx`。因此本次完成的是这两个命题的完整本地证明，不宣称所有上游构造或全信任链已经闭合。没有新公理、新待补责任，也没有递归接手上游接口的上游证明。

## 精确改动与下游影响

已实施范围为新增两个公共定理、从 `KIP126.ProofTools` 公共入口导出、精确增补 ProofTools 公共类型锁及公共消费测试，并将两个 Blueprint 条目绑定到各自完整结论。私有实现通过 ProofTools 内部审计覆盖。现有定理的名称、类型、前提及对象关联均保持原样，其他模块无修改需求。

独立审查者已逐字比较正式公共模块与批准附件，两个完整类型、参数顺序、私有证明调用均相同。提交前统一删除候选附件末尾的多余空白行后，两文件字节一致，SHA-256 均为 `6eafd5db4ac3cfa415c906217a5bbb6bf8aa94407b845746eb620e2d4cdc7394`；清理前附件的审查指纹为 `79ccd321cb1e2fe3a05788500081e6eaa49833256e23a5bc5e2b5f4b92ad5c62`。

对实施前精简接口快照 `/tmp/proof-tools-api-before-public-consequences.json` 的结构化比较结果：

- 手写数学声明精确新增获准的 2 个定理，删除为 0。
- Lean 为类型内证明自动生成并导出 3 个常量：`cutoffAdamsDifferentialAtLevel._proof_2`、`cutoffAdamsDifferentialAtLevel._proof_4`、`finiteLevelExtensionToClassical._proof_2`，均在 `generated_declarations` 如实记录。这是 2 个数学定理及其自动证明常量，不是新增 5 个数学接口。
- 所有既有手写声明和自动声明的整行记录均未改变，包含类型指纹、宇宙和公理依赖；既有导出删除为 0。
- `proof-obligations.json` 仍为原 204 条，其 SHA-256 与实施前完全一致：`895e790f0c0944b63f780fa38647ea332ac5b989f0718fe90726d0181f58ff38`。

正式 ProofTools 类型锁 SHA-256 为 `3f3954ebcef1eba9924f591b19124edd863bcb53a6224d44eb652aa992c91d00`。普通公共消费者验证两个新定理可见，同时验证两个内部完整证明和正层源比较仍不可见。两个 Blueprint 稳定标签均只绑定对应完整公共结论。

实施后最终 `lake build` 成功，3722 jobs；49 项 Blueprint 测试成功，耗时 238.674 秒。独立审查者已读取 `/tmp/finite-level-public-full-build.log` 与 `/tmp/finite-level-public-blueprint-tests.log` 的实际完成结果。两个条目的本地完整形式化已完成；网页颜色仍遵循原生依赖状态，不更改隐藏责任状态，也不声称上游待补因此全部闭合。

## 未完成范围与人审记录

两条完整证明、独立陈述对齐审查、实际类型及依赖核验、公共包装实施、精确接口锁更新、消费者测试和两个 Blueprint 绑定现已完成。报告保留真实人审状态 `approved-interface-change`，以 `resolution: implemented-and-validated` 记录实施验证完成。

人审依据为 2026-10-22 用户在本会话对上述具体方案回复“同意”，完整授权边界记录于 `human_decision`。最终实施后的公共声明、锁差异和完整构建已独立核对；上游 52 项既有传递待补仍按原责任保留，没有因本次公开包装而宣称已补证。
