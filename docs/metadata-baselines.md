# 元数据检查基线

`metadata/` 保留十份构建输入，不作为数学说明或进度展示的第二份数据库。

| 文件 | 保留内容 | 消费者 |
| --- | --- | --- |
| 八份 `*-api.json` | 七个数学模块与 Computation 兼容入口的公开与生成声明分组；每项名称、类型指纹、宇宙参数、公理依赖；完整导出集合 | 各模块及兼容入口 Lean 接口测试、Main 审计、Blueprint 绑定检查 |
| `proof-obligations.json` | 每个许可证明洞的名称、模块、类型与证明体指纹、类别；精确 Main 根与 ProofTools 边界名单 | 七个数学模块 Lean 审计、hgraph 编译导入与分类 |
| `mathematical-naming-restoration.json` | 已审查的标识符改名对应 | 源清单检查 |

接口基线 schema 为 4，证明洞基线 schema 为 2。数组按声明逐行存储。格式精简保留原有检查值，不重新接受当前源码或放宽 Lean 检查。后续已授权的模块分层和第二线分类接口更新单独反映在基线中；E₂ 与 Adams 计算两份接口锁必须精确分区覆盖 Computation 兼容接口锁。

数学说明和论文对应维护在 `blueprint/semantic/` 与 `blueprint/paper/`；接口范围说明是 hgraph 原生节点附件。出处使用 bibliography，固定代码提交见 `blueprint/source-snapshots.bib`。完整类型文本、依赖关系和完成状态由 Lean 捕获与 hgraph 导出，不在基线中重复维护。重要目标修正仍记录在根目录 `MEMO.md`。

## 显式更新

`scripts/freeze-interfaces.py` 不再读取契约、来源或本地归档。先运行 `--prepare`，再按提示运行所需 `.lake/Capture<Module>.lean` 和 `scripts/CaptureTrust.lean`；确认接口修改已获授权后，显式运行 `python3 scripts/freeze-interfaces.py <module-stem>`。

更新器允许移除确已完成的证明洞。声明消失、未经登记的新证明洞、既有证明洞的模块/类型/证明体变化、自建公理或 elaboration-error 占位均被拒绝。新增或调整公共接口仍须遵守 `AGENTS.md`；运行更新器本身不构成授权。普通 `lake build` 只验证，不自动接受变化。

修改更新器后运行：

```sh
python3 -m unittest discover -s Tests -p 'test_metadata_baselines.py'
python3 scripts/check-source-inventory.py
lake build
```
