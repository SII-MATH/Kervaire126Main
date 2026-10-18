# 协作规则

| 模块（接口清单） | 职责 |
| --- | --- |
| [SpectralSequence](metadata/spectral-sequence-api.json) | 谱页、微分、代表、存活、滤过、收敛、检测与 ESS；Algebra 为内部支撑。 |
| [AdamsSynthetic](metadata/adams-synthetic-api.json) | 固定范畴、Adams 系统、标准类、乘法、ν、λ 商与比较。 |
| [Literature](metadata/literature-api.json) | 带来源和完整条件的文献结果。 |
| [E2Computation](metadata/e2-computation-api.json) | 独立的 Ext／E₂ 基底、维数、乘法、标准类标定及到实际 E₂ 页的比较；不得依赖 ProofTools 或后续 Adams 计算。 |
| [ProofTools](metadata/proof-tools-api.json) | stretching、广义 Leibniz、广义 Mahowald 及公共操作定理。 |
| [AdamsCalculations](metadata/adams-calculations-api.json) | 后续 Adams 微分、边界、存活、永久循环及高页计算；可以使用 E₂ 输入和 ProofTools。 |
| [Main](metadata/main-api.json) | 论文局部推导及标准 h₆² 非零永久存活目标。 |

公共入口为 `KIP126.<模块名>`，七个数学模块在 `KIP126/` 下平级组织，依赖按 `E2Computation → ProofTools → AdamsCalculations → Main` 分层；ProofTools 只能调用 E₂ 层计算。原 `KIP126.Computation` 及其子路径的兼容入口已删除，计算内容直接从 `KIP126.E2Computation` 或 `KIP126.AdamsCalculations` 导入；现有公开声明的 `KIP126.Computation.*` 名称不变，责任归属以实际定义源模块为准。`metadata/` 只保留精简构建基线：`*-api.json` 锁定公开类型、宇宙参数、公理依赖及导出，`proof-obligations.json` 锁定许可证明洞与 Main/ProofTools 审计边界，命名清单保留检查所需的改名对应。数学说明与论文对应维护在 Blueprint，接口范围说明放在 hgraph 原生节点附件，出处统一使用 bibliography 引用；不再平行维护契约和来源 JSON。格式见 [元数据检查基线](docs/metadata-baselines.md)。历史计算审计、接口审查、证明会话、报告、完整元数据快照和一次性迁移记录统一放在被 Git 忽略的 `local-history/`，内部保留原目录结构；整理方式与恢复说明见 [历史材料归档](docs/history-archive.md)。`MEMO.md` 记录相对原始 AimPaper 的目标修正、问题成因及修复状态，保留在仓库根目录并继续由 Git 跟踪，不纳入本地归档；精简时须保留修正范围与未完成边界。清单内部的本地路径以仓库根目录为基准；固定上游来源与历史快照保留其原始路径。Lake 的依赖锁 `lake-manifest.json` 保留在根目录。

- **接口冻结。** 未经用户明确允许，不增删或改变公共声明的名称、类型、前提、语义、对象关联及导出。认为接口不合理或不足时，提交具体修改方案、理由和下游影响，获准后实施；不得改锁文件绕过检查。已有授权不重复确认。
- **单模块任务。** 未经明确允许，不修改其他模块、接手其证明或移动责任归属。阅读和调用上游公共接口可以正常进行。
- **自顶向下证明。** 从当前目标递归拆分局部引理与构造，直到接到已有上游接口、mathlib 或基础定义；依赖不得成环。辅助声明保持私有。
- **上游直接调用。** 上游已登记的待构造、待证明接口可直接使用，责任不转入下游；不恢复 Challenge、结果包或额外假设，保留真正的数学前提。
- **如实记录。** 保持接口不变的补证明及状态更新无需另行批准；同步来源、测试和 [待补清单](metadata/proof-obligations.json)。未经允许不新增公理或待补责任，不能靠放宽检查掩盖缺口。
- **封装与检查。** 使用 `module`，默认私有、显式 `public`；`import all` 仅限同模块内部及测试审计汇总。遵守依赖方向，以普通导入验证公共消费。测试集中在 `Tests/`：`Tests.Architecture` 检查七个数学模块与固定主目标，各模块专项测试保留接口锁、公共消费和边界检查；各模块独立接口锁须保持导出完整、归属唯一，`Tests.Integration` 保留上游独立消费检查，`Tests.Trust` 汇总审计全部测试。修改后运行 `python3 scripts/check-source-inventory.py` 和 `lake build`，后者默认包含这些检查；复用缓存，不以精简测试为由删除已有覆盖。`Checks.Registry` 仅用于追踪待补清单的构建输入，不是数学模块。
- **工程边界。** 工具链按 [README](README.md) 固定，未经允许不升级或改依赖锁；避免无必要地清理缓存。Blueprint 已获准按一个项目、八章接入原生 hgraph：SpectralSequence、AdamsSynthetic、Literature、E2Computation、ProofTools、AdamsCalculations、Main、Geometry；前七章对应七个数学模块，第八章单列尚未形式化的几何结论与桥接。章节与条目依照数学依赖组织，聚合图也须无环；主蓝图全英文、按数学内容分节，一个数学条目可绑定多个现有 Lean 声明；外部输入在陈述前标明文章引用及原始定位。完整源码另作实现索引，压缩展示须保留实际编译依赖、传递闭合及全部既有待补责任，保留现有接口锁与构建检查；历史记录按上述 `local-history/` 约定归档，数学说明与来源引用由 Blueprint/hgraph 维护，精简接口与证明洞基线继续入库。网页发布与全量构建分开；全量构建失败不阻塞对应关系发布，未核验节点须明确标记，不能冒充已证明。运行方式见 [blueprint/README.md](blueprint/README.md)。
- **推送与拉取时同步 Release 构建缓存。** 每次从本地向远程推送代码，都必须在同一任务中将与已推送提交对应、通过 `lake build` 的项目 `.lake/build/` 缓存上传到该远程仓库的 GitHub Release，供其他工作者复用。Release 使用 `build-cache-<commit>-<os>-<arch>` 等可追溯标签，并随缓存提供 `metadata.json` 和 SHA-256 校验和，记录源提交、构建输入指纹、仓库、操作系统/架构、Lean 工具链及 `lake-manifest.json` 哈希；不得将含有未提交源码改动的构建结果标记为已推送提交的缓存。

  每次 `git pull` 或 fetch 后 merge/rebase 更新本地源码后，即使未要求编译，也必须在同一任务中检查远程 Release，下载、校验并恢复与更新后源码和构建环境匹配的缓存；已在本地验证且匹配的缓存可直接复用。先检查元数据，再下载大文件；校验分片及合并后归档的 SHA-256。不得仅按最新 Release 选择缓存；仅 `AGENTS.md` 等不影响构建输入的文档变更可在核实后复用，否则旧缓存只能作为增量构建基线。

  恢复前确认没有构建进程写入 `.lake/build/`，将归档安全解压到临时目录并检查路径和文件类型，备份现有缓存后再安装，不得覆盖更新的本地编译进度。依赖及 Mathlib 缓存按锁定版本另行恢复；后续验证仍运行 `lake build`，利用缓存避免重复编译。上传失败须明确报告缓存尚未同步；无兼容缓存或下载失败时说明原因并继续源码更新，使用本地缓存或增量构建。普通 Git 推送、拉取不会自动同步 Release 附件，现有 GitHub Actions 缓存也不代替这项同步，必须显式执行上述步骤。
