# Kervaire126Main

[AimPaper](AimPaper/main.tex) 关于 Kervaire 不变量 126 维情形的 Lean 形式化。数学对象和主证明采用 develop 中更具体的构造与比较关系；命名和组织参考原 Main，以数学对象、外部假设及论文结论为中心。

| 目录 | 内容 |
| --- | --- |
| [Def](KIP126/Def/) | 通用数学定义、对象、接口及定义良定所需的通用引理。固定外部输入、公理和第六节证明均已迁出。 |
| [Literature](KIP126/Literature/) | 文献源对象、背景存在性及固定标准对象、文献中的固定表和外部文献结论；结果由 `Literature.adamsSyntheticResults` 提供。 |
| [Computation](KIP126/Computation/) | 固定计算表、坐标代数及其数学解释、输入对象的必要良定证书；实际 Adams 结果由相关公理 `Computation.adamsComputations` 提供。 |
| [Main](KIP126/Main/) | 实际计算结果的证明、文献应用、第六节延伸定理、第七节证明及主定理。 |

## 数学对象与外部假设

[HF2AdamsContext](KIP126/Def/ClassicalAdams/Context/Data.lean) 以指定的完备化 `Q : CompletionModel` 为参数，描述模 2 稳定同伦背景，包含 HF₂、Milnor 坐标、张量三角结构、协运算及具体谱模型的比较。底层空间、预谱及 HF₂ 完备化的定义位于 `Def/StableHomotopy/Spectra`。synthetic 背景另由 `SyntheticAdamsContext` 指定，保留与同一经典 Adams 塔的比较。通用构造不假定任何外部结果；沿用 develop 当前工作区的六个背景公理及固定选择位于 `Literature/Background`、`Literature/Standard`，所有标准对象使用同一个完备化。

[ExternalHypotheses](KIP126/Main/ExternalHypotheses/Data.lean) 表示主证明采用的两组相关外部假设：

```lean
structure ExternalHypotheses where
  literature : ExternalHypotheses.LiteratureHypotheses
  computation : ExternalHypotheses.ComputationHypotheses literature
```

`LiteratureSources`、`LiteratureTheorems` 分别记录文献源对象和这些对象上的结论；`ComputationInterpretation`、`ComputationTheorems` 分别记录计算解释和解释后的数学结论。两层保存外部陈述、固定数据和输入对象，不在此证明外部结论。构造分次坐标代数所必需的齐次性等证书单独登记于 [layer-boundaries.json](metadata/layer-boundaries.json)；维数、非零性、消失及其他实质证明放在 Main。`KIP126.Main.externalHypotheses` 组合两个外部结果公理，本身是定义。`Main/AdamsSynthetic` 在同一背景上提取对象并建立应用所需结论。

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
| Lemma 7.16 | `KIP126.Main.SectionSeven.lemma_7_16_toda_bracket_detected` | [TodaDetection](KIP126/Main/SectionSeven/TodaDetection.lean) |
| Corollary 7.18 | `KIP126.Main.SectionSeven.corollary_7_18_h0_extension` | [H0Extension](KIP126/Main/SectionSeven/H0Extension.lean) |
| Lemma 7.20 | `KIP126.Main.SectionSeven.lemma_7_20_nu_extension` | [NuExtension/NinthQuotient](KIP126/Main/SectionSeven/NuExtension/NinthQuotient.lean) |

编号按本仓库论文核对；7.12 是 Remark。代码的证明依赖顺序不完全等同论文叙述顺序，具体说明见对应文件。`ChoiceIndependence` 下的两个 `Prop` 定义仍只是命题陈述，不作为已证明定理列入上表。

最终陈述保持 develop 的固定标准球面 Adams 谱序列中的非零永久存活：

```lean
NonzeroSurvival sphereAdamsData (2, 128) standardH6Square
```

`Main/ExtensionLaws` 中仍有四处原有待补证明：广义 Leibniz 两处、广义 Mahowald 两处。另有 Literature 中六个明确接受的背景公理和上述两个外部输入公理；Def 不再含公理或 `sorry`。位置见 [proof-obligations.json](metadata/proof-obligations.json)；编译通过不表示所有依赖均已证明。本次整理不增加公理或证明缺口。

## 验证与来源

工具链保持 Lean **v4.32.2**，mathlib 固定为 `905b95818eb32af7874a58b427f50c1711a5e96c`。在仓库根目录运行：

```sh
lake exe cache get  # 首次获取依赖缓存；已有缓存可跳过
python3 scripts/check-source-inventory.py
lake build
```

源代码检查覆盖目录、依赖关系及精确公理／待补清单；构建包含 `Tests.Architecture` 和 `Tests.Trust`，核验最终类型、两组假设的相关性并报告实际证明依赖。协作约定见 [AGENTS.md](AGENTS.md)。

[input-layer-migration.json](metadata/input-layer-migration.json) 记录本次内容分类、模块迁移和背景参数化；[mathematical-naming-audit.json](metadata/mathematical-naming-audit.json) 记录全仓逐主题审查、改名映射和保留数学术语的理由；[mathematical-names.json](metadata/mathematical-names.json) 保留首轮调整记录；[develop-migration.json](metadata/develop-migration.json) 记录此前迁入时的源文件映射与哈希，保留为历史记录。[external-inputs.json](metadata/external-inputs.json) 是活动来源清单；[develop-external-inputs.json](metadata/develop-external-inputs.json) 是上游原始快照，其中历史路径不是当前接口。文献材料保存在 [Sources](Sources)。Blueprint 的迁移与检查继续延后。

重组前工作区备份为 `/inspire/hdd/global_user/baokangjie-CZXS25250151/Kervaire126Main-before-reorganization-20261015T080856Z/workspace.tar.gz`；本次命名修改前备份为 `/inspire/hdd/global_user/baokangjie-CZXS25250151/Kervaire126Main-before-mathematical-names-20261015T085206Z/workspace.tar.gz`。
