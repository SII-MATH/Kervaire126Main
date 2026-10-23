# 元数据检查基线

`interface/baselines/` 保留十份构建输入，不作为数学说明或进度展示的第二份数据库。

| 文件 | 保留内容 | 消费者 |
| --- | --- | --- |
| 八份 `*-api.json` | 八个数学模块的公开与生成声明分组；每项名称、类型指纹、宇宙参数、公理依赖；完整导出集合 | 各模块 Lean 接口测试、Main 审计、Blueprint 绑定检查 |
| `proof-obligations.json` | 每个许可证明洞的名称、模块、类型与证明体指纹、类别；精确 Main 根与 ProofTools 边界名单 | 八个数学模块 Lean 审计与 Interfaces 只读展示；不改变原生数学节点状态 |
| `mathematical-naming-restoration.json` | 已审查的标识符改名对应 | 源清单检查 |

接口基线 schema 为 4，证明洞基线 schema 为 2。数组按声明逐行存储。格式精简保留原有检查值，不重新接受当前源码或放宽 Lean 检查。后续已授权的模块分层和第二线分类接口更新单独反映在基线中；E₂ 与 Adams 计算分别使用独立接口锁，原 Computation 兼容入口及其重复接口锁已删除；各模块接口仍核验完整导出与实际定义归属，源清单检查核验公开声明归属唯一。

数学说明和论文对应按章维护在 `blueprint/chapters/<模块>.tex`；接口范围说明是 hgraph 原生节点附件。出处使用 bibliography，固定代码提交见 `blueprint/source-snapshots.bib`。完整类型文本、依赖关系和完成状态由 Lean 捕获与 hgraph 导出，不在基线中重复维护。目标修正、问题成因、反例与状态集中记录在根目录 `corrections.yaml`，原始及修正陈述只引用 AimPaper 和 Blueprint 节点；维护方式见 [修正记录](corrections.md)。

## 按模块跟踪审计输入

`proof-obligations.json` 仍是唯一人工维护的许可待补清单。默认构建通过
`scripts/project-proof-obligations.py` 校验完整清单，再按实际定义源模块生成
`.lake/audit-inputs/<模块>.json`；这些文件完全派生，不入库、不接受新的责任。
每个模块的 `Checks.Registry.<模块>` 由独立 Lake library 跟踪，只依赖本片内容。
生成器只在内容改变时原子替换文件，Lake 将输出文件的内容哈希作为下游输入，
不会把全局清单的哈希传递给所有审计。

七份使用待补清单的 InternalAudit 保留原有完整证明体、精确指纹、公理和依赖边界检查；
SpectralSequence 继续独立执行无洞审计。各片完整保留本模块所有条目，按条目的
`module` 源归属分区，不按 `KIP126.Computation.*` 等保留名称判断。
Main 片还保留根名单及 ProofTools 边界；ProofTools 片只保留其消费的边界。
修改该共同边界会合理地重跑两份审计，修改其他模块的单个待补条目只使该模块的片变化。
全局 summary 和未分配元数据由生成器严格校验，不复制到每片。

旧 `Checks.Registry` 全清单入口作为显式兼容入口保留，默认数学审计不再导入它。
源码清单检查每次验证全局数据和各审计的本模块输入接线；完整 `lake build`
继续包含全部原有审计和测试。缓存命中时只重放旧日志，不重新执行 Lean 审计。

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

## 与最新 main 整合及完整检查（2026-10-19）

用户随后授权完整检查通过后合并。整合 `origin/main` 的 E₂ 补证（PR #28）时，逐声明三方合并许可清单，保留上游十二项责任的完成及原有精确指纹；全仓许可责任从本任务的 231 项进一步减为 219 项，其中 AdamsComputation 为 21 项、ProofTools 仍只有 5.10，Main 为零。这十二项完成属于上游工作。本任务的已批准条件、未完成边界与公共声明保持不变。

同时保留 main 的 Blueprint 原生证明展示和读者引用更新。Main 的两个完成证明各放入独立的原生 proof 块，原直接方法的历史缺口继续保留，避免重复或嵌套证明。完整检查覆盖默认 `lake build`、源码清单、全部 Python 测试及原生 Blueprint 导出；Release 缓存按最终干净提交和完整构建输入指纹同步。

## 标准类结构与唯一主定理接口迁移（2026-10-21）

用户已批准 `StandardSphereClasses` 增加整族非零字段、固定实例填入证明，以及 `Main.h6_sq_permanent` 改为接收同一固定系统上的标准类结构；对外只保留这一个主定理版本。AdamsComputation 新增 `h6_exhaustive`，其余消费者传入固定实例。接口锁记录实际类型、结构生成声明及固定实例字段的编译器证明辅助项；数学说明和证明依赖见对应 Blueprint 条目，完成背景的上游范围仍见原提案及 issue #31。

以下为结构版改动提交 `1962133` 在整合最新 main 之前的历史核验，不是整合后源码的验证结果。当时源码插入改变了 Background 的 29 项和 E2 Standard 后部的 5 项既有 `sorry` 诊断标签。独立审核从与原始基点 `f17969a` 全部 670 个构建输入匹配的 Release 缓存加载旧模块，并逐项核对这两个文件共 38 项责任：旧类型和证明体指纹精确匹配原锁，新旧完整 kernel 类型、宇宙和责任集合不变；仅替换 Lean 识别的诊断标签参数后，完整证明表达式逐字相同，标签仍指向未改动的原 `sorry` 文本。因此只迁移当时的 34 项证明体指纹，不改变类型、状态、数量或审计规则。完整证据保留在忽略的 `local-history/metadata/interface-reviews/20261021-standard-classes-hole-labels/`。

### 整合最新 main（完整验证通过）

结构版改动已与 `origin/main` 的 `fa6c729` 整合。上游独立完成了 15 项责任，许可待补总数已由原来的 214 项减为 199 项；这些补证不归入本次接口迁移成果。固定 `standardClasses` 的非零字段直接复用上游 `standardHiConstruction` 的 `.property`，移除本任务重复添加的 Milnor 辅助证明。本任务相对于该 main 的公共接口变化仍限于 AdamsSynthetic、AdamsComputation 和 Main 三份锁，不新增证明洞。

整合后的诊断标签核验已通过：逐项核对 Background 剩余的 28 项与 E2 Standard 的 9 项，共 37 项责任；新旧原始完整类型、宇宙参数、实际模块归属和去除诊断标签差异后的完整 kernel 证明体均相同。只迁移 18 项诊断标签导致的证明体指纹，其中 Background 在 `standardClasses` 之后的 13 项、E2 Standard 的 5 项。`fa6c729` 的全部 199 项责任、状态和审计边界精确保留，未恢复上游已完成的 15 项。证据保留在忽略的 `local-history/metadata/interface-reviews/20261021-standard-classes-merge-fa6c729-hole-labels/`。

整合后的默认 `lake build` 已通过全部 3644 项任务；源码清单覆盖 606 个项目源文件和 35 个消费／审计文件。Main 审计检查 1922 项声明、Geometry 检查 6 项声明，均无本地证明洞；ProofTools 检查 5708 项声明，保留唯一既有待补责任，34 项 Main／ProofTools 边界均通过无本地证明洞核验，没有项目公理。独立全项目信任捕获通过，共 24,855 项项目声明；更新器的责任复核结果与现有 199 项清单完全相等，没有新增项目公理或失败占位。三份新捕获分别包含 AdamsSynthetic 1789 项、AdamsComputation 706 项、Main 34 项公开声明，其名称、完整类型、宇宙和公理依赖均与接口锁及全项目信任捕获精确一致。93 项 Python 单元测试及原生 Blueprint 导出通过；导出包含 241 个数学条目和 10,024 项 Lean 声明，1,921 条原生警告按既有规则保留，不设置致命警告门禁。这些验证只闭合本轮有界接口迁移，不消除原提案及 issue #31 保留的完成背景上游责任。

## 固定接口补证迁移（2026-10-22）

本轮在独立 worktree 中保持八份公共接口锁、全部公共类型、宇宙参数与导出不变，补完
`Literature.Standard.selected_filtration_lambda` 和
`AdamsSynthetic.Standard.cofiberHomologyShortComplex_shortExact`。前者迁入历史独立核验的有限商论证，
在 Literature 内用私有基础引理重建滤过步骤，不反向导入 ProofTools；后者由同一旋转三角的逐度同调短正合性，
经有限齐次分解及保持分次和余作用的核提升，推出固定余模范畴中的短正合性。
两项仍继承登记中的窗口、有限商分离性、余模阿贝尔结构和实际同调构造责任。

许可待补从 204 项减为 202 项，只移除这两个实际完成的证明责任。
插入 Literature 私有证明引理使后续 23 项原有证明洞的诊断位置变化。
逐项核对旧缓存与原基线一致、新旧完整 kernel 类型和宇宙相同；仅归一化固定 Lean
识别的诊断标签后，剩余完整证明表达式逐字相同，标签也仍指向原 `sorry` 文本。
据此仅迁移这 23 项证明体指纹。Ext 的三个剩余证明洞连同指纹保持不变。
没有新增公理、证明洞、公共接口或检查豁免。完整证据保存在
`local-history/proof-migration-20261022/`。

该阶段默认 `lake build` 返回成功，共 3733 项任务；八份接口锁保持不变，Main 的 30 个公开根与
34 个 ProofTools 边界全部通过既有审计。源码清单、49 项 Blueprint 测试及原生网页导出通过。
两项新增证明另经独立完整类型和编译依赖核验；分别保留 31 项和 30 项既有上游责任，
没有把本地补证记为这些上游构造的完成。


### 继续逐项迁移与固定接口核验

继续检查指定分支的末端 `71e63c47` 及裁剪前祖先 `c60fbbbb`，逐项覆盖当时剩余的
202 项许可责任。祖先仍保留的真实构造包括 cubical 良好替换、分次余模阿贝尔性及
实际塔的 Milnor 商比较；不把具有目标同义字段的结果包投影计为独立证明。

本次进一步补齐九项：`sourceReplacement`、私有 `canonicalComoduleAbelian`、
`sphereE2_milnorEquiv`、`sphereE2_milnor_classOfCycle`、`nuCofiber_triangle`、
`selected_realization_lifetime`、`selected_permanent_lift`、`bhs_finite_lift` 和
`selected_realization_boundary_lift`。后四项用原分支的滤过与检测论证及现有独立上游输入
适配到同一固定对象、同一标签和实际商映射；挠性提升通过减去同一个 lambda 修正项，
同时保留第一商标签并杀死指定幂。没有把零无穷页类直接当作零同伦类。

良好替换与余模阿贝尔性的完整证明闭包只使用三项基础逻辑公理，不再含上游证明洞。
其余完成项仍继承登记的固定模型、塔比较、坐标、窗口或有限商分离性等责任。
尤其 Milnor 比较的原始坐标和微分识别、规范谱序列同构、实际余模同调及一般 Ext 比较、
实现检测与指定实现提升均未被声称完成。新增私有构造全部纳入原有内部审计汇总。

为使用同模块独立上游，六项既有公开声明从 `Standard.Source` 原样移至
`Standard.Background`；名称、完整类型、宇宙、固定对象和数学模块归属不变。
其中三项仍待补的责任只同步实际定义源文件及编译诊断位置。公共接口锁只删除
`sourceReplacement` 与 `steenrodComoduleAbelian` 已消除的 `sorryAx` 信任依赖，
不得以修改导出清单接纳自动生成的额外声明；证明中的展开方式已调整以保留原导出归属。

复核早期成功构建日志时发现两处已有编译器异常，现将 `mappingSystem` 和 `mapping`
显式标为 `noncomputable`，保持原始类型与定义体。新 E₂ 比较也暴露了既有 H₆ 平方证明
在具体坐标下的内核展开超时。比较现通过私有等式证书封装，并证明所选择的等价等于
原商构造；H₆ 平方先对一般比较和标准类结构证明私有引理，再代入原固定对象。
未提高超时上限、更改目标或改变数学对象。私有探针不足以验证公开模块的展开行为，
因此最终以同模式的完整生产模块构建为准。

对新证明可能解锁的剩余条目作了再次检查。`classical_canonicalIso` 的正页比较已独立
重跑，但完整目标仍缺低于第 2 页的微分相容输入，详见已有
`interface/proposals/SpectralSequence/low-page-compatibility-20261021/report.md`。
其他排除理由逐项区分缺失的真实源结果、固定对象识别和比较图；此结论限于所查分支及
当前接口，不是剩余数学命题不可证明的断言。完整记录仍统一保存在
`local-history/proof-migration-20261022/donor-exhaustion/`。

实际编译捕获确认本阶段许可责任从 202 项减为 193 项，连同前阶段共补齐 11 项，
相对工作树原始基点为 204 → 193。其余 193 项的完整 kernel 类型、宇宙和去除诊断标签后的
完整证明体逐字相同，未新增责任；118 项证明体指纹变化仅来自源码诊断位置，其中包含
上述三项同模块内源文件迁移。每个新旧诊断范围均核对到实际 `sorry` 文本。
Main 与 ProofTools 的既有审计边界及其余许可字段完整保留。

全量构建中的架构检查还暴露了普通导入环境的可见性边界：新实际证明引用的私有
Milnor 引理存在于已编译模块，但普通导入不会加载其私有部分。公共入口消费和主目标
完整类型检查继续使用原普通导入环境；递归证明依赖检查另载入完整私有环境，仍对每项
依赖要求存在并检查其所属模块，不跳过缺失声明、不放宽允许依赖的模块集合。

最终默认 `lake build` 通过全部 4115 项任务，完整日志无错误或编译器 PANIC；八模块
内部信任审计、Main 的 30 个公开根和 34 项 ProofTools 边界、普通入口消费及完整架构
依赖检查全部通过。源码清单覆盖 913 个项目文件和 35 个消费／审计文件。独立审计再次
核对全部 11 项完成证明的原始完整类型、宇宙和传递依赖，以及八入口共 4876 项公开声明；
除两项已消除的 `sorryAx` 依赖外，公共接口锁精确保持，无新增公理、证明洞或依赖循环。

49 项 Blueprint 测试通过，原生导出得到 236 个数学条目、11,484 项 Lean 声明；
3053 条原生警告按既有规则保留。逐项迁移排查和完成后的再次检查覆盖续作起点的全部
202 项责任，独立复核确认没有未处理的完整迁移候选。剩余 193 项中，107 项未找到独立
来源证明体，83 项有具体前提或对象识别阻碍，3 项只能迁入局部组件；其完整目标继续
保留待补状态。详细证据和排除理由见上述历史目录及其中的 `exhaustion-audit.md`。


## 按程序来源重组计算章节（2026-10-23）

用户授权第四章和同名模块改为 `AdamsComputation`，第六章和同名模块改为
`SSComputation`，并把 `Adams` 直接计算的 d₂ 与 E₂ 数据一起放在第四章。
两个入口及独立接口锁分别为 `KIP126.AdamsComputation` /
`adams-computation-api.json` 和 `KIP126.SSComputation` /
`ss-computation-api.json`。原 `KIP126.Computation.*` 公共数学声明名称保持不变；
原模块专属的第二线声明改用新模块命名空间，消费者与正式绑定同步修改。
稳定的 Blueprint 数学标签及固定上游源码快照保留原名。

原来混合在 `Raw.claims` 的 671 条记录按保留的来源字段分区：
`S0_AdamsE2_basis/d2` 的记录 513、2855、2923、2926（共 4 条）迁至
`Raw.directD2Claims`，由第四章的 `Table.direct_d2_result` 负责实际页认证；
其余 667 条由第六章的 `Table.result` 认证，保留原有顺序和数据库定位。
这是原总表认证责任的分拆：许可待补项由 193 项变为 194 项，
没有新增数学输入记录，也没有完成其中任一认证。
两个 staircase 记录及其有限页到达责任仍在第六章。

`Standard.d2_h0Six_h6` 及其独立 E₂ 代数证明移入第四章并直接调用直接输出的认证，
不再通过 SS 表格取得同一方程。第六章中用于 P h₂、Q h₂ 边界及对应消失分量的 7 处同方程调用也改为直接消费第四章认证，边界和消失结论本身仍归 SSComputation。`Standard.d2_h6` 同时作为明确标注来源的
Literature 一线公式特例在第四章陈述，并不被描述成额外程序输出。
`d2_x125_8` 等来自 SS 记录的 d₂，以及无界第二线候选筛选，仍归第六章。
新 `KIP126.AdamsComputation.E2` 入口保持原来的独立代数导出；
ProofTools 只使用该入口及其组成模块，源清单和公共消费测试继续拒绝直接 d₂ 数据依赖。

旧提案移动到新责任模块目录，责任元数据随之更新，原始审查证据、哈希、
批准范围和历史源码定位保留。改名与责任分区的完整编译比对证据保存在
忽略的 `local-history/program-chapter-migration-20261023/`。


本次实际编译比对覆盖八份原锁的全部 4,876 个公开导出和全部 193 项许可责任。
按明确模块改名映射及共享声明搬移逐项比较完整 kernel 类型；
唯一额外的生成差异是 `Statement.match_1` 的绑定变量随定义搬移改变源码模块标记，
数字标签、变量作用域和完整类型结构均保持相同。
原 193 项证明洞的完整证明表达式在按同一改名映射并只归一化 Lean 识别的诊断标签后全部相同，
只迁移 20 项相应证明体指纹。134 项类型指纹随源码模块名变化；其中包括
ProofTools 锁中 `SourceMonomial.value.eq_def` 引用 E₂ 源模块的生成项。
全部旧公开声明的宇宙参数和公理依赖按同一改名映射保持一致。
88 个原第六章导出随共享语法、陈述谓词和两个指定 d₂ 声明上移；
新增公开导出仅为 `Raw.directD2Claims` 与 `Table.direct_d2_result`，
合计公开导出由 4,876 项变为 4,878 项。E₂ 子入口完整保留原 706 项导出。

全部数学源码编译通过 4,042 项任务；默认完整 `lake build` 通过 4,119 项任务。
源清单覆盖 916 个项目源文件和 36 个消费／审计文件。
Main 保留零本地证明洞，34 项 Main／ProofTools 边界通过原有审计；
全部数学模块仍无项目公理。此次检查是实际执行的迁移验证，不是新增数学结果、
独立数学复核或对既有待补责任的完成声明。


最终 89 项 Python 测试通过（66 项 Blueprint、14 项审计输入、7 项元数据、2 项来源分区）。
固定版本 hgraph 原生同步与导出通过，包含 238 个数学条目和 11,486 项源码声明；
3,058 条原生警告按既有非致命策略保留。
导出的第四章和第六章第一块均为原生 `prose`，与两章源码的自由文本来源说明一致。
网页输出仅为本地导出；这些原生状态仍不替代独立 Lean 构建及信任审计。
