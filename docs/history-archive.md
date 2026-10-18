# 历史材料归档

历史材料集中在仓库根目录的 `local-history/`，整个目录由 `.gitignore` 忽略。归档采用原路径加 `local-history/` 前缀的方式，保留原有分组：

| 原位置 | 本地归档位置 |
| --- | --- |
| `Sources/Reviews/` | `local-history/Sources/Reviews/` |
| `Reports/` | `local-history/Reports/` |
| `metadata/interface-reviews/` | `local-history/metadata/interface-reviews/` |
| `metadata/proof-sessions/` | `local-history/metadata/proof-sessions/` |
| `metadata/paper-interface-exposure-20261017/` | `local-history/metadata/paper-interface-exposure-20261017/` |
| `metadata/module-path-migration.json` | `local-history/metadata/module-path-migration.json` |
| `metadata/upstream-update-review.json` | `local-history/metadata/upstream-update-review.json` |
| `metadata/fixed-interface-migration.json` | `local-history/metadata/fixed-interface-migration.json` |

完整的 `*-contracts.json`、`*-sources.json`（包括 AimPaper）、`migration-baseline.json` 与 `main-proof-port-review.json` 也已移至 `local-history/metadata/`。数学说明迁入 Blueprint/hgraph，出处通过 bibliography 引用。`metadata/` 只保留九份精简构建基线，见 [元数据检查基线](metadata-baselines.md)。重要的持续维护记录统一放在根目录 `corrections.yaml` 并由 Git 跟踪，格式见 [修正记录维护](corrections.md)；迁移前的完整记录备份放在 `local-history/`。

一次性的 Blueprint 论文对应复核清单 `blueprint/paper/mapping-review.md`，以及旧快照的章节迁移和书目刷新脚本 `scripts/refresh-blueprint-layout.py`、`scripts/refresh-blueprint-paper.py`，也按原路径归档。当前生成与发布使用 `build-blueprint.py`、`publish-blueprint.py`，不依赖这些历史材料。

精简前的全部 23 份 JSON 原始快照及校验值保存在 `local-history/metadata-before-hgraph-20261017/`。125 条接口范围说明迁入原生 hgraph 节点的逐项对应保存在 `local-history/metadata-scope-migration.json`，不复制旧的完成状态。

本次归档保留每个实际迁移文件的原始内容；逐文件原路径、新路径、大小与 SHA-256 记录在本地 `local-history/archive-manifest.json`。第一轮整理时，旧清单中的仓库相对证据路径已同步加上归档前缀；这些完整清单现已归档，当前构建基线不依赖历史路径。数学声明、类型、指纹、证明状态和责任归属未改。历史快照内部的旧路径和校验值保留原样；其中脚本的旧工作区路径及相对根目录可能需要在复现时调整。

第一轮归档时核对的 289 处历史清单引用中，24 处历史证据目标在迁移前就不在本地材料中，本次没有新增缺失目标。具体位置保存在本地 `local-history/reference-audit.json`，不把这些未找到的材料记为已经恢复或核验。

归档不随后续 Git 提交分发。完整 `lake build` 保持独立于本地归档；当前清单中指向归档的路径用于查阅历史依据，不作为新增证明前提。

## 持续审阅的接口提案

17 份独立接口审查报告已从 `local-history/metadata/interface-reviews/<模块>/<ID>/report.md` 迁入 Git 跟踪的 `interface-proposals/<模块>/<ID>/report.md`，用于 dashboard 持续审阅。归档原件保留为历史快照；提案文件记录原路径与原件 SHA-256，完整保留原元数据和正文。后续投递及状态更新只写提案目录，见 [接口提案指南](interface-proposals.md)。未迁入的小型证据仍留在本地归档，网页明确标记为本地证据，不冒充已公开可访问。

## 从 Git 历史恢复

对尚无 `local-history/` 的新检出仓库，可在仓库根目录运行以下命令恢复整理前已提交的历史版本：

```sh
mkdir local-history
git archive 73409ad30ab1f2a88e080fb1c7e8a9a1bb6efb2a \
  Sources/Reviews Reports metadata | tar -x -C local-history
```

已有本地归档时不要用该命令覆盖它。此操作恢复上述提交中的版本；本地新增产物和归档校验清单需从现有本地归档另行备份。
