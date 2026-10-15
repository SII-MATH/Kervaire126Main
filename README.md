# Kervaire126Main

本仓库保留 [AimPaper](AimPaper/main.tex) 中最终定理 `KIP126.Main.h6_sq_permanent` 的形式化及其实际证明依赖。数学对象和证明采用 develop 中的具体构造与比较关系，按数学定义、外部输入和主证明分层组织。

| 目录 | 内容 |
| --- | --- |
| [Def](KIP126/Def/) | 通用数学定义、对象、接口及定义良定所需的通用引理。固定外部输入、公理和第六节证明均已迁出。 |
| [Literature](KIP126/Literature/) | 文献源对象、背景存在性及固定标准对象、文献中的固定表和外部文献结论；结果由 `Literature.adamsSyntheticResults` 提供。 |
| [Computation](KIP126/Computation/) | 固定计算表、坐标代数及其数学解释；必要的计算证书单独放在 `Certificates`。实际 Adams 结果仍由相关公理 `Computation.adamsComputations` 提供。 |
| [Main](KIP126/Main/) | 最终定理所需的第六、七节证明、专用辅助论证、局部记号与相关输入组合。 |

[Tests](Tests/) 仅保留 `Architecture` 和 `Trust` 两个检查；数学模块不导入 Tests。独立背景核验、Example 2.11 表项核验及无关公共接口检查已移除。

本轮将生产 Lean 文件从 **1653 个裁剪至 1167 个**，删除 486 个；其中 Main 从 **67 个减至 51 个**，Tests 从 **23 个减至 2 个**。按源码索引，2710 项原声明不再保留，保留数学文件内删除了 791 条完整命令。最终定理的陈述与证明源码逐字未变，保留的数学声明均保持裁剪前完整原文；导入、属性及空作用域的整理另行审查。编译所需的 3 项原数学声明和 36 条局部记号均从备份原样恢复，共撤销 39 条命令的删除，没有补写数学代码。裁剪清单及验证记录见 [final-theorem-pruning.json](metadata/final-theorem-pruning.json)。

## 数学对象与外部假设

[HF2AdamsContext](KIP126/Def/ClassicalAdams/Context/Data.lean) 以指定的完备化 `Q : CompletionModel` 为参数，描述模 2 稳定同伦背景，包含 HF₂、Milnor 坐标、张量三角结构、协运算及具体谱模型的比较。底层空间、预谱及 HF₂ 完备化的定义位于 `Def/StableHomotopy/Spectra`。synthetic 背景另由 `SyntheticAdamsContext` 指定，保留与同一经典 Adams 塔的比较。通用构造不假定任何外部结果；沿用 develop 当前工作区的六个背景公理及固定选择位于 `Literature/Background`、`Literature/Standard`，所有标准对象使用同一个完备化。

[ExternalHypotheses](KIP126/Computation/Hypotheses/Joint.lean) 表示主证明采用的两组相关外部假设：

```lean
structure ExternalHypotheses where
  literature : ExternalHypotheses.LiteratureHypotheses
  computation : ExternalHypotheses.ComputationHypotheses literature
```

`LiteratureSources`、`LiteratureTheorems` 分别记录文献源对象和这些对象上的结论；`ComputationInterpretation`、`ComputationTheorems` 分别记录计算解释和解释后的数学结论。外部结果接口只陈述其数学前提和结论。Computation 的 `Certificates` 子目录另外保存固定基底、关系组合、坐标等式和解释相容性的内核验证；这些实质计算证书与构造输入所必需的最小良定证书分别逐文件登记于 [layer-boundaries.json](metadata/layer-boundaries.json)。局部坐标验证不能替代实际球面 Adams 结果的外部假设。

`KIP126.Main.externalHypotheses` 组合两个外部结果公理，本身是定义。计算证书和主证明使用同一文献见证及其相关计算假设，不重新选择源对象。`Main/AdamsSynthetic` 在同一背景上提取证明所需对象；第七节的 λ 单射、tmf 检测和滤过推导放在 `Main/SectionSeven`，其固定输入核验归 Computation。

通用定义按数学主题归入 `KIP126.SpectralSequence`、`KIP126.Algebra`、`KIP126.Comparison` 和 `KIP126.AdamsSynthetic`。主要结构包括：

| 名称 | 数学职责 |
| --- | --- |
| `AdamsComparison` | 经典 Adams 塔与 synthetic 谱序列、λ 商、收敛及检测之间的相容比较。 |
| `AlgebraRealizationComparison` | 代数结构、λ 反演实现、权移和 E₂ 的比较。 |
| `SourceComparisons`、`SourceTheorems` | 文献对象与标准对象的比较，以及文献对象上的定理。 |
| `E2Interpretation`、`AdamsComputationTheorems` | 球面和 Cν 的计算坐标解释及这些解释满足的 Adams 结论。 |
| `TodaBracketLaws`、`TodaNaturalityLaws` | Toda 括号的基本性质与自然性。 |
| `LambdaInversionEquivalence` | λ 反演与经典范畴之间的局部化／恢复等价。 |

文献假设的字段为 `sources`、`theorems`，计算假设的字段为 `interpretation`、`theorems`。计算 E₂ 坐标的解释与几何上的 λ 反演实现分别命名，避免混淆。证明目录按 `Dichotomy`、`EtaDetection`、`ThetaSquareClassification`、`FiltrationElevenRepresentative` 等具体结论组织。

此次整理复用了原 Main 的 `AdamsSynthetic`、`Standard`、`SectionSeven` 等数学组织名称。未直接覆盖为旧的总模型结构：当前定义将 Adams 页、Milnor 坐标、收敛及检测绑定到实际 Adams 塔；旧结构不能完整保留这些要求。原 Main 中仍适用的数学对象含义予以保留，不重复建立另一套定义。

## 论文证明入口

| 论文结论 | Lean 声明 | 文件 |
| --- | --- | --- |
| Theorem 7.1 | `KIP126.Main.h6_sq_permanent` | [H6SquarePermanent](KIP126/Main/H6SquarePermanent.lean) |
| Proposition 7.8 | `KIP126.Main.proposition_7_8` | [PropositionSevenEight](KIP126/Main/PropositionSevenEight.lean) |
| Proposition 7.9 | `KIP126.Main.SectionSeven.proposition_7_9` | [PropositionSevenNine](KIP126/Main/SectionSeven/PropositionSevenNine.lean) |
| Lemma 7.14 | `KIP126.Main.SectionSeven.lemma_7_14_alpha_one_exists` | [SectionSeven/AlphaOne](KIP126/Main/SectionSeven/AlphaOne.lean) |
| Lemma 7.20 | `KIP126.Main.SectionSeven.lemma_7_20_nu_extension` | [NuExtension/NinthQuotient](KIP126/Main/SectionSeven/NuExtension/NinthQuotient.lean) |

编号按本仓库论文核对；7.12 是 Remark。当前证明先由 ν-可除性和 Cν 入射微分排除证明 Proposition 7.9，再与 Proposition 7.8 推出最终结论。论文中另一些命题在该形式化中是 Proposition 7.9 的后继推论，不属于最终证明的前提，不在本轮保留范围内。

最终陈述保持 develop 的固定标准球面 Adams 谱序列中的非零永久存活：

```lean
NonzeroSurvival sphereAdamsData (2, 128) standardH6Square
```

当前源码保留 **8 个公理和 1 处 `sorry`**：六个背景公理、两个相关外部结果公理，以及广义 Mahowald 最小中间长度情形中的原有 May 边界提升缺口 MH2。声明依赖审查确认最终证明实际使用 MH2。广义 Leibniz 的两个缺口和完整广义 Mahowald 的非相邻比较缺口 MH1 不在最终证明依赖链中，已随无关声明删除；这不表示已补完它们。Def 不含公理或 `sorry`。位置见 [proof-obligations.json](metadata/proof-obligations.json)。本轮完整构建于 2026-10-15 14:18:56 UTC 通过（4288 个构建任务），包括最终定理及 `Tests.Architecture`、`Tests.Trust`。最终证明仍含 `sorryAx`，对应上述 MH2 缺口；构建通过不表示证明已完成。

## 验证与来源

工具链保持 Lean **v4.32.2**，mathlib 固定为 `905b95818eb32af7874a58b427f50c1711a5e96c`。在仓库根目录运行：

```sh
lake exe cache get  # 首次获取依赖缓存；已有缓存可跳过
python3 scripts/check-source-inventory.py
lake build
```

源代码检查覆盖目录、依赖关系及精确公理／待补清单；构建包含 `Tests.Architecture` 和 `Tests.Trust`，核验最终类型、两组假设的相关性并报告实际证明依赖。与最终证明无关的独立迁入接口测试不再作为当前构建目标。协作约定见 [AGENTS.md](AGENTS.md)。

[remote-develop-merge.json](metadata/remote-develop-merge.json) 记录远程 develop 至 `edbb648` 的逐项合并、源文件校验和及公共接口映射。该记录是历史合并清单；选择无关性及其他未被最终证明使用的内容不再全部保留。最终证明所需的 Milnor 构造和比较关系仍使用同一标准背景。远程新增但尚未证明的源识别接口不用于替换本地固定完备化背景，也不引入其占位证明。

[main-scope-migration.json](metadata/main-scope-migration.json) 记录上一轮 Main 范围调整、计算证书分类、背景核验分离和验证结果；[input-layer-migration.json](metadata/input-layer-migration.json) 保留上一轮外部输入迁移及背景参数化记录；[mathematical-naming-audit.json](metadata/mathematical-naming-audit.json) 记录全仓逐主题审查、改名映射和保留数学术语的理由；[mathematical-names.json](metadata/mathematical-names.json) 保留首轮调整记录；[develop-migration.json](metadata/develop-migration.json) 记录此前迁入时的源文件映射与哈希，保留为历史记录。[external-inputs.json](metadata/external-inputs.json) 是活动来源清单；[develop-external-inputs.json](metadata/develop-external-inputs.json) 是上游原始快照，其中历史路径不是当前接口。文献材料保存在 [Sources](Sources)。Blueprint 的迁移与检查继续延后。

重组前工作区备份为 `/inspire/hdd/global_user/baokangjie-CZXS25250151/Kervaire126Main-before-reorganization-20261015T080856Z/workspace.tar.gz`；本次命名修改前备份为 `/inspire/hdd/global_user/baokangjie-CZXS25250151/Kervaire126Main-before-mathematical-names-20261015T085206Z/workspace.tar.gz`。
