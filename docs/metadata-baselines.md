# 元数据检查基线

`interface/baselines/` 保留十份构建输入，不作为数学说明或进度展示的第二份数据库。

| 文件 | 保留内容 | 消费者 |
| --- | --- | --- |
| 八份 `*-api.json` | 八个数学模块的公开与生成声明分组；每项名称、类型指纹、宇宙参数、公理依赖；完整导出集合 | 各模块 Lean 接口测试、Main 审计、Blueprint 绑定检查 |
| `proof-obligations.json` | 每个许可证明洞的名称、模块、类型与证明体指纹、类别；精确 Main 根与 ProofTools 边界名单 | 八个数学模块 Lean 审计与 Interfaces 只读展示；不改变原生数学节点状态 |
| `mathematical-naming-restoration.json` | 已审查的标识符改名对应 | 源清单检查 |

接口基线 schema 为 4，证明洞基线 schema 为 2。数组按声明逐行存储。格式精简保留原有检查值，不重新接受当前源码或放宽 Lean 检查。后续已授权的模块分层和第二线分类接口更新单独反映在基线中；E₂ 与 Adams 计算分别使用独立接口锁，原 Computation 兼容入口及其重复接口锁已删除；各模块接口仍核验完整导出与实际定义归属，源清单检查核验公开声明归属唯一。

数学说明和论文对应维护在 `blueprint/semantic/` 与 `blueprint/paper/`；接口范围说明是 hgraph 原生节点附件。出处使用 bibliography，固定代码提交见 `blueprint/source-snapshots.bib`。完整类型文本、依赖关系和完成状态由 Lean 捕获与 hgraph 导出，不在基线中重复维护。目标修正、问题成因、反例与状态集中记录在根目录 `corrections.yaml`，原始及修正陈述只引用 AimPaper 和 Blueprint 节点；维护方式见 [修正记录](corrections.md)。

## 前端展示

hgraph 的 **Interfaces → Baselines** 区域由 `scripts/blueprint_interfaces.py` 从上述十份基线直接生成，提供模块概览、声明与生成导出搜索、许可证明洞、Main／ProofTools 审计边界、改名对应和原始 JSON 下载。源码陈述与局部上下文使用 hgraph 原生 Lean 解析器读取，属于未经 elaboration 的源码展示，不替代编译后的完整类型。页签只读，不另维护接口数据库，也不新增数学章节、绑定或状态规则。公理列表表示锁中许可的依赖；包含 `sorryAx` 可能来自上游，无该项也不表示本次网页导出已通过完整构建。

同一页签的两个子页按需加载并保留页面、筛选及滚动状态，往返不重复请求基线；刷新文档时重新读取当前导出，不使用跨版本持久缓存。**Proposals** 区域提供接口提案审阅；可从声明查找相关提案，也可从提案返回责任模块的接口基线。

运行既有 `scripts/build-blueprint.py` 即可接入原生自定义页签；发布仍独立于 Lean 全量构建。

## 显式更新

`scripts/freeze-interfaces.py` 不再读取契约、来源或本地归档。先运行 `--prepare`，再按提示运行所需 `.lake/Capture<Module>.lean` 和 `scripts/CaptureTrust.lean`；确认接口修改已获授权后，显式运行 `python3 scripts/freeze-interfaces.py <module-stem>`。

更新器允许移除确已完成的证明洞。声明消失、未经登记的新证明洞、既有证明洞的模块/类型/证明体变化、自建公理或 elaboration-error 占位均被拒绝。新增或调整公共接口仍须遵守 `AGENTS.md`；运行更新器本身不构成授权。普通 `lake build` 只验证，不自动接受变化。

修改更新器后运行：

```sh
python3 -m unittest discover -s Tests -p 'test_metadata_baselines.py'
python3 scripts/check-source-inventory.py
lake build
```

## AdamsSynthetic 证明包装清理（2026-10-18）

用户授权清理没有独立用途的单字段命题包装，以及重复要求提交已有证明的结果包。本次移除 `NuExactTriangleInput`、`FactorizationFiltrationComparison`、`AdamsBoundednessInput`、`MappingFiltrationComparison`、`MappingDetectionInput` 和未使用的 `SphereTwistSign`；通用定理直接接收原有数学命题，固定系统直接调用登记定理。`ModelData.nuExactTriangle` 直接保存带完整同调短正合条件的保持性证明，Literature 的旧包装转换器同步移除。映射检测不再额外要求其证明没有使用的因子分解滤过比较。

这些是接口简化，不是完成或移除待补数学责任。90 项 AdamsSynthetic 证明／构造洞的责任、声明原文和类型保持不变。删除前置声明使 `Standard.Filtration` 中四项未改动的 `sorry` 获得新的源码位置／宏标签：`finite_map_separation`、`mappingConvergence`、`mapping_filtration_iff`、`adams_filtration_bounded`。逐项核对声明原文完全相同、编译后类型指纹相同及精确证明洞集合后，仅迁移这四项包含诊断标签的证明体指纹；其余证明洞基线不变。接口锁依据重新编译后的捕获更新，既有完整导出、前提和信任检查继续执行。

## Geometry 接入（2026-10-18）

用户已授权有限扩展 Literature 并新增 Geometry。新增 `geometry-api.json` 锁定两个几何结论；既有七个模块的接口归属保持不变。Literature 新增实际闭光滑流形、稳定切标架与带标架流形的数据定义，以及不变量和几何存在性接口。仅登记 `KIP126.Literature.Geometry.kervaireInvariant`（`pending-construction`）和 `KIP126.Literature.Geometry.browder_iff`（`pending-proof`）两个新增责任。前者保留配对、标架诱导二次细化及 Arf 不变量的构造责任；后者保留 Browder 定理及到固定模型的比较责任。Geometry 本地与私有证明均不许可证明洞，传递依赖仍完整审计。数学陈述、原始出处和责任范围由 Blueprint 维护。

## ProofTools 直接公开实际声明（2026-10-18）

用户已授权依据 Blueprint／AimPaper 对应及下游用途整理公开接口。原 `Operations` 的 23 个别名与 4 个重复包装，以及 `Standard.nuCofiberMahowaldZeroLayer` 的别名，改为在原定义处直接公开相应的 28 个实际声明；保留其 `Internal`／`Internal.Mahowald` 源名称。`Operations.lean` 只汇集普通公共导入，不再声明第二套名称。调用处、Blueprint 绑定和接口锁同步使用实际声明；没有下游调用不构成取消 Blueprint 正式数学接口的理由。

实际数学陈述和证明正文保持不变；原论文条目、局部对应范围、广义 Leibniz／Mahowald 的待补责任均保留。公开类型中的定义引用随去掉包装而更新，接口锁须从编译结果捕获并核验公理依赖。Main／ProofTools 的审计边界同步迁移到实际声明，完整导出、公共消费、私有辅助隐藏及递归信任检查继续执行；不加入 hgraph 兼容补丁或网页状态改写。

编译核对确认 28 个新旧入口的类型全部定义等价，原有公开声明的公理依赖不变，全部 309 项许可证明洞的名称、归属、类型和待补状态不变。`generalizedMahowald` 的源文件逐字未改；内部声明由私有名改为公开名后，仅迁移其编译证明体指纹。Lean 自动生成的 `homotopyRegrade.congr_simp` 现在实际定义于 ProofTools，故从 Main 的生成声明锁移至 ProofTools；Main 的精确边界另纳入它与 `lambdaMultiply.eq_1`，共 34 项，由 ProofTools 完整证明体审计继续核验。

## ProofTools 原文陈述登记（2026-10-18）

用户随后明确选择“写公开 theorem，并登记待补证明”。据此，`Paper/OriginalStatements.lean` 为 AimPaper 2.6、2.12、2.15、2.16、2.17、2.18、2.19、2.20、5.10、5.14 各登记一个公开待补定理。经典部分直接使用实际 Adams E∞ 群、其收敛比较与同伦代表元，未添加有界性或 synthetic-to-classical 比较前提；5.10 保留原文 crossing 条件，未把额外的 λ 核条件混入原命题。用于表达这些公开类型的经典延拓、crossing、永久循环和全页态射语言也直接公开；证明辅助构造保持私有。

十项均只有陈述，没有声称证明完成。原有 GL1／GL2／MH2 的三个源码证明洞位置与两个声明保留；精确源码检查与编译审计另许可这十个经授权的新声明。既有 Main 根、34 项 Main／ProofTools 边界及已完成工具的递归无本地证明洞检查继续执行，新增待补定理不得进入该证明链。新增责任以编译后的名称、类型和证明体指纹逐项登记；原 309 项责任保留。2.17 的对象及 5.14 的商群次数排印差异只在 `corrections.yaml` 维护，AimPaper 原文不改。

## ProofTools 原文定理补证（2026-10-18）

本轮保持全部 179 项公开导出、类型和宇宙参数不变，补完 AimPaper 2.6、2.12、2.15、2.16、2.17、2.18、2.19。2.15 将现有通用滤过群代表元准则接到实际经典 Adams 塔；2.12 保留原弱阈值，2.16／2.17 保留有符号长度。2.6 通过实际塔的逐阶提升证明滤过相加；2.18 通过有限归纳构造长度 r 的唯一可加扩张映射，并用同一代表元验证全部扩张关系。辅助引理均为私有，七项仅依赖 `propext`、`Classical.choice`、`Quot.sound`，不借用其他待补原文定理。

相应移除七项直接待补责任，总数从 319 减为 312；其余责任与精确 Main 边界保留。仍缺桥接的 2.20、5.10、5.14 不改陈述、不加前提、不转移待补归属。2.20 缺逐页代表元到同一个核代表元的收敛桥；5.10 不能删除现有 λ 除法所需的核 no-crossing 条件后套用；5.14 缺覆盖零与 inessential 情形的一般模型检测比较。源码精确检查、许可洞清单和递归无本地证明洞审计同步收紧；Blueprint 只按源码原生更新状态。

插入私有证明引理改变了同文件剩余三项 `sorry` 的编译诊断标签：`extensionBoundary_of_exact`、`finiteCrossing_iff_syntheticCrossing`、`infiniteExtension_to_classicalExtension`。已逐项核对其公开类型、归属、原始 `by sorry` 证明体和待补状态完全不变，仅迁移这三项编译证明体指纹；其他 309 项原有责任的指纹不变。检查仍逐声明比较精确类型和证明体，不放宽许可规则。

## Main 条件命题补证（2026-10-19）

`lemma_toda2ext` 与 `corollary_2ext125` 的完整公开类型、宇宙参数和导出不变，现调用独立的 `eta_extension_excluded_of_d6_vanishes hc3 hc5` 消去其共同假设。排除定理的实际证明闭包不使用这两个结果，Main 审计继续禁止这样的回用；两项责任从许可清单移除，全仓由 237 项减为 235 项。Main 源码与完整证明体检查现均要求零本地证明洞，ProofTools 的剩余责任不变。两项条件命题仍共同继承 116 项上游责任；直接原文 Toda 构造和任意代表误差论证的边界保留于 Blueprint 和 `corrections.yaml`。

ProofTools 同文件新增两个无洞私有引理，分别刻画逐页近似核代表和从共同核代表推出 Proposition 2.20 的正合代数步骤；未完成的收敛桥仍留在原公开责任。插入源码使三个原有 `sorry` 的位置从 716/740/755 移至 767/791/806。逐项比较新旧编译证明表达式，除这三个位置对应的自然数字面量外完全相同；完整类型亦相同。因此只迁移 `extensionBoundary_of_exact`、`finiteCrossing_iff_syntheticCrossing`、`infiniteExtension_to_classicalExtension` 的诊断位置证明体指纹，不放宽检查或改变责任。

## 撤销错误的旧 GL／MH 定理（2026-10-19）

用户在确认 Blueprint 已只绑定 AtLevel 版本后，明确授权删除 `KIP126.ProofTools.Standard.generalizedLeibniz` 和 `KIP126.ProofTools.Standard.generalizedMahowald`。本次仅从公开声明/导出与许可责任清单撤销这两个 theorem，不把撤销记为补证；全仓许可责任由 235 项减为 233 项，ProofTools 保留三项原论文比较/收敛责任。两个 law 定义、固定模型 MH 否定证书、GL 数学反例记录与两个 AtLevel 定理保留，另随旧 GL 证明消失的 `KIP126.Literature.bocksteinLabel.congr_simp` 是原本实际生成在 ProofTools 的自动简化辅助，并无独立源码声明；它从生成导出清单移除。除此以外，所有剩余公开类型、宇宙、信任依赖和导出逐行不变。

普通消费测试要求旧定理不可见，同时继续检查 law 定义与完整 AtLevel 用法；ProofTools 内部审计明确拒绝重新引入旧声明。Main 的禁用边界保留。精确锁根据重新编译后的公开导出和完整信任捕获生成；只移除已授权的两个责任，不新增或豁免其他证明洞。

## 获准补全实际收敛与比较条件（2026-10-19）

用户明确批准第一项（2.20）和第三项（5.14）的具体接口调整。2.20 只增加实际源滤过的完备性、有限非负层商与靶滤过分离性，保留原正合性、逐页永久性及结论。5.14 只增加同一模型的 realization 坐标与实际 Adams 塔比较，保留同一代表元及其 `f` 像、零和边界类。Literature 新比较接口记录实际 stage、projection、cofiber、全部 Z/B 与既有 E₂ 标定，检测运输是由这些结构推出的定理；没有目标同义字段。

两项条件定理及其辅助引理已补证。独立完整证明体核验分别遍历 249、454 项项目声明，均无证明洞、项目公理或目标循环，只依赖三项基础逻辑公理；新通用检测运输同样独立通过。许可清单移除这两项直接责任，由 233 减为 231；ProofTools 只保留 5.10 原 iff。锁迁移只针对用户批准的两个类型；5.10 的完整类型和 `by sorry` 原文不变，源码插入导致的诊断位置须由旧证明体的精确哈希重构核验后更新，不放宽检查。

Blueprint 保留 AimPaper 原文，将两项条件形式化绑定到单独明确列出前提的条目。Standard 实际塔比较的 producer 尚未构造，也未新增许可洞替代；2.20 的新自然条件亦不被宣称对任意模型自动成立。数学修正与未完成边界统一见 `corrections.yaml`。第二项 5.10 的 PDF 已按用户要求发到指定群，其声明修改尚未获准。完整检查按用户要求继续暂缓，本阶段只作相关模块、消费及精确接口核验。
