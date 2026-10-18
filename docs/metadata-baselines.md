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
