# 协作规则

| 模块（接口清单） | 职责 |
| --- | --- |
| [SpectralSequence](metadata/spectral-sequence-api.json) | 谱页、微分、代表、存活、滤过、收敛、检测与 ESS；Algebra 为内部支撑。 |
| [AdamsSynthetic](metadata/adams-synthetic-api.json) | 固定范畴、Adams 系统、标准类、乘法、ν、λ 商与比较。 |
| [Literature](metadata/literature-api.json) | 带来源和完整条件的文献结果。 |
| [Computation](metadata/computation-api.json) | 计算数据与实际对象的对应、标准类标定、微分、乘积及存活。 |
| [ProofTools](metadata/proof-tools-api.json) | stretching、广义 Leibniz、广义 Mahowald 及公共操作定理。 |
| [Main](metadata/main-api.json) | 论文局部推导及标准 h₆² 非零永久存活目标。 |

公共入口为 `KIP126.<模块名>`，六模块在 `KIP126/` 下平级组织。接口、契约、来源和其他记录统一放在 `metadata/`：`*-api.json` 锁定类型与导出，`*-contracts.json` 说明用途，`*-sources.json` 记录来源。清单内部的本地路径以仓库根目录为基准；固定上游来源与历史快照保留其原始路径。Lake 的依赖锁 `lake-manifest.json` 保留在根目录。

- **接口冻结。** 未经用户明确允许，不增删或改变公共声明的名称、类型、前提、语义、对象关联及导出。认为接口不合理或不足时，提交具体修改方案、理由和下游影响，获准后实施；不得改锁文件绕过检查。已有授权不重复确认。
- **单模块任务。** 未经明确允许，不修改其他模块、接手其证明或移动责任归属。阅读和调用上游公共接口可以正常进行。
- **自顶向下证明。** 从当前目标递归拆分局部引理与构造，直到接到已有上游接口、mathlib 或基础定义；依赖不得成环。辅助声明保持私有。
- **上游直接调用。** 上游已登记的待构造、待证明接口可直接使用，责任不转入下游；不恢复 Challenge、结果包或额外假设，保留真正的数学前提。
- **如实记录。** 保持接口不变的补证明及状态更新无需另行批准；同步来源、测试和 [待补清单](metadata/proof-obligations.json)。未经允许不新增公理或待补责任，不能靠放宽检查掩盖缺口。
- **封装与检查。** 使用 `module`，默认私有、显式 `public`；`import all` 仅限同模块内部及测试审计汇总。遵守依赖方向，以普通导入验证公共消费。测试集中在 `Tests/`：`Tests.Architecture` 检查六模块入口与固定主目标，六模块专项测试保留接口锁、公共消费和边界检查，`Tests.Integration` 保留上游独立消费检查，`Tests.Trust` 汇总审计全部测试。修改后运行 `python3 scripts/check-source-inventory.py` 和 `lake build`，后者默认包含这些检查；复用缓存，不以精简测试为由删除已有覆盖。`Checks.Registry` 仅用于追踪待补清单的构建输入，不是数学模块。
- **工程边界。** 工具链按 [README](README.md) 固定，未经允许不升级或改依赖锁；避免无必要地清理缓存。Blueprint 迁移与检查继续延后。
- **推送与拉取时同步 Release 构建缓存。** 每次从本地向远程推送代码，都必须在同一任务中将与已推送提交对应、通过 `lake build` 的项目 `.lake/build/` 缓存上传到该远程仓库的 GitHub Release，供其他工作者复用。Release 使用 `build-cache-<commit>-<os>-<arch>` 等可追溯标签，并随缓存提供 `metadata.json` 和 SHA-256 校验和，记录源提交、构建输入指纹、仓库、操作系统/架构、Lean 工具链及 `lake-manifest.json` 哈希；不得将含有未提交源码改动的构建结果标记为已推送提交的缓存。

  每次 `git pull` 或 fetch 后 merge/rebase 更新本地源码后，即使未要求编译，也必须在同一任务中检查远程 Release，下载、校验并恢复与更新后源码和构建环境匹配的缓存；已在本地验证且匹配的缓存可直接复用。先检查元数据，再下载大文件；校验分片及合并后归档的 SHA-256。不得仅按最新 Release 选择缓存；仅 `AGENTS.md` 等不影响构建输入的文档变更可在核实后复用，否则旧缓存只能作为增量构建基线。

  恢复前确认没有构建进程写入 `.lake/build/`，将归档安全解压到临时目录并检查路径和文件类型，备份现有缓存后再安装，不得覆盖更新的本地编译进度。依赖及 Mathlib 缓存按锁定版本另行恢复；后续验证仍运行 `lake build`，利用缓存避免重复编译。上传失败须明确报告缓存尚未同步；无兼容缓存或下载失败时说明原因并继续源码更新，使用本地缓存或增量构建。普通 Git 推送、拉取不会自动同步 Release 附件，现有 GitHub Actions 缓存也不代替这项同步，必须显式执行上述步骤。
