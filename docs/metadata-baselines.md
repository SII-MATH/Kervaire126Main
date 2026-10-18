# 元数据检查基线

`metadata/` 保留十份构建输入，不作为数学说明或进度展示的第二份数据库。

| 文件 | 保留内容 | 消费者 |
| --- | --- | --- |
| 八份 `*-api.json` | 八个数学模块的公开与生成声明分组；每项名称、类型指纹、宇宙参数、公理依赖；完整导出集合 | 各模块 Lean 接口测试、Main 审计、Blueprint 绑定检查 |
| `proof-obligations.json` | 每个许可证明洞的名称、模块、类型与证明体指纹、类别；精确 Main 根与 ProofTools 边界名单 | 八个数学模块 Lean 审计；不再作为原生 hgraph 导出的输入 |
| `mathematical-naming-restoration.json` | 已审查的标识符改名对应 | 源清单检查 |

接口基线 schema 为 4，证明洞基线 schema 为 2。数组按声明逐行存储。格式精简保留原有检查值，不重新接受当前源码或放宽 Lean 检查。后续已授权的模块分层和第二线分类接口更新单独反映在基线中；E₂ 与 Adams 计算分别使用独立接口锁，原 Computation 兼容入口及其重复接口锁已删除；各模块接口仍核验完整导出与实际定义归属，源清单检查核验公开声明归属唯一。

数学说明和论文对应维护在 `blueprint/semantic/` 与 `blueprint/paper/`；接口范围说明是 hgraph 原生节点附件。出处使用 bibliography，固定代码提交见 `blueprint/source-snapshots.bib`。完整类型文本、依赖关系和完成状态由 Lean 捕获与 hgraph 导出，不在基线中重复维护。目标修正、问题成因、反例与状态集中记录在根目录 `corrections.yaml`，原始及修正陈述只引用 AimPaper 和 Blueprint 节点；维护方式见 [修正记录](corrections.md)。

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
