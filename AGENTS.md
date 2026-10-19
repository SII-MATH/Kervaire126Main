# 协作规则

| 模块（接口清单） | 职责 |
| --- | --- |
| [SpectralSequence](interface/baselines/spectral-sequence-api.json) | 谱页、微分、代表、存活、滤过、收敛、检测与 ESS；Algebra 为内部支撑。 |
| [AdamsSynthetic](interface/baselines/adams-synthetic-api.json) | 固定范畴、Adams 系统、标准类、乘法、ν、λ 商与比较。 |
| [Literature](interface/baselines/literature-api.json) | 带来源和完整条件的文献结果，包括几何对象、Kervaire 不变量构造与 Browder 桥接。 |
| [E2Computation](interface/baselines/e2-computation-api.json) | 独立的 Ext／E₂ 基底、维数、乘法、标准类标定及到实际 E₂ 页的比较；不得依赖 ProofTools 或后续 Adams 计算。 |
| [ProofTools](interface/baselines/proof-tools-api.json) | stretching、广义 Leibniz、广义 Mahowald 及公共操作定理。 |
| [AdamsCalculations](interface/baselines/adams-calculations-api.json) | 后续 Adams 微分、边界、存活、永久循环及高页计算；可以使用 E₂ 输入和 ProofTools。 |
| [Main](interface/baselines/main-api.json) | 论文局部推导及标准 h₆² 非零永久存活目标。 |
| [Geometry](interface/baselines/geometry-api.json) | AimPaper 的 126 维几何存在性与完整维数分类；调用 Literature 的几何对象、不变量和 Browder 输入以及 Main。 |

公共入口为 `KIP126.<模块名>`，八个数学模块在 `KIP126/` 下平级组织，依赖按 `E2Computation → ProofTools → AdamsCalculations → Main → Geometry` 分层；ProofTools 只能调用 E₂ 层计算。原 `KIP126.Computation` 及其子路径的兼容入口已删除，计算内容直接从 `KIP126.E2Computation` 或 `KIP126.AdamsCalculations` 导入；现有公开声明的 `KIP126.Computation.*` 名称不变，责任归属以实际定义源模块为准。`interface/baselines/` 只保留精简构建基线：`*-api.json` 锁定公开类型、宇宙参数、公理依赖及导出，`proof-obligations.json` 锁定许可证明洞与 Main/ProofTools 审计边界，命名清单保留检查所需的改名对应。数学说明与论文对应维护在 Blueprint，接口范围说明放在 hgraph 原生节点附件，出处统一使用 bibliography 引用；不再平行维护契约和来源 JSON。格式见 [元数据检查基线](docs/metadata-baselines.md)。历史计算审计、接口审查、证明会话、报告、完整元数据快照和一次性迁移记录统一放在被 Git 忽略的 `local-history/`，内部保留原目录结构；整理方式与恢复说明见 [历史材料归档](docs/history-archive.md)。根目录 `corrections.yaml` 是相对原始 AimPaper 的修正记录唯一维护源，由 Git 跟踪；agent 按结构化条目记录问题、反例、修复状态与 Blueprint 节点引用，格式见 [修正记录维护](docs/corrections.md)。原文与修正版陈述分别引用 AimPaper 和 Blueprint，不另写一份。不另建平行记录文件。精简时须保留修正范围与未完成边界。清单内部的本地路径以仓库根目录为基准；固定上游来源与历史快照保留其原始路径。Lake 的依赖锁 `lake-manifest.json` 保留在根目录。

- **接口冻结。** 未经用户明确允许，不增删或改变公共声明的名称、类型、前提、语义、对象关联及导出。认为接口不合理或不足时，提交具体修改方案、理由和下游影响，获准后实施；不得改锁文件绕过检查。已有授权不重复确认。
- **接口提案投递。** 独立接口审查报告统一维护在 `interface/proposals/<责任模块>/<唯一ID>/report.md`，由 Git 跟踪并在 dashboard 的 **Interfaces → Proposals** 区域展示；投递模板、校验与人审回写见 [接口提案指南](docs/interface-proposals.md)。从 `local-history/metadata/interface-reviews/` 迁入的原件仅作历史快照，后续更新只写提案目录。报告必须保留完整前提、固定对象、证据等级、候选差异、下游影响和明确授权范围；未获人审批准不等于当前必须暂停工作。相对 AimPaper 的修正仍唯一维护于 `corrections.yaml`，不在提案中平行维护修正版陈述。
- **单模块任务。** 未经明确允许，不修改其他模块、接手其证明或移动责任归属。阅读和调用上游公共接口可以正常进行。
- **自顶向下证明。** 从当前目标递归拆分局部引理与构造，直到接到已有上游接口、mathlib 或基础定义；依赖不得成环。辅助声明保持私有。
- **上游直接调用。** 上游已登记的待构造、待证明接口可直接使用，责任不转入下游；不恢复 Challenge、结果包或额外假设，保留真正的数学前提。
- **Blueprint 绑定。** 每章的 Lean 绑定只能指向实际定义在同名数学模块、且列入该模块公开接口锁的 public 声明，归属以源文件为准，不按命名空间或使用者判断。绑定必须对应条目正文实际定义的对象或陈述的结论；背景对象、前提、用于表达结论的既有谓词及证明中调用的辅助步骤不得作为该结论的额外绑定，同模块内也适用。正文确实分别陈述多个对象或结论时可绑定多个声明。跨模块内容通过原生数学条目引用连接，不混入 `\lean`／`\uses{decl:…}` 形式化绑定；仅有局部辅助步骤时如实保留未完成范围，不冒充完整陈述的直接形式化对应。私有构造与证明责任保留在 Lean 源码、内部依赖审计和待补清单中，不生成私有声明的数学条目绑定；网页状态遵循 hgraph 原生的源码局部状态与手写依赖闭合；不额外改写隐藏责任状态，完整 Lean 信任审计仍由独立构建负责。
- **如实记录。** 保持接口不变的补证明及状态更新无需另行批准；同步来源、测试和 [待补清单](interface/baselines/proof-obligations.json)。未经允许不新增公理或待补责任，不能靠放宽检查掩盖缺口。
- **封装与检查。** 使用 `module`，默认私有、显式 `public`；`import all` 仅限同模块内部及测试审计汇总。遵守依赖方向，以普通导入验证公共消费。测试集中在 `Tests/`：`Tests.Architecture` 检查八个数学模块与固定主目标，各模块专项测试保留接口锁、公共消费和边界检查；各模块独立接口锁须保持导出完整、归属唯一，`Tests.Integration` 保留上游独立消费检查，`Tests.Trust` 汇总审计全部测试。修改后运行 `python3 scripts/check-source-inventory.py` 和 `lake build`，后者默认包含这些检查；复用缓存，不以精简测试为由删除已有覆盖。`Checks.Registry` 仅用于追踪待补清单的构建输入，不是数学模块。
- **工程边界。** 工具链按 [README](README.md) 固定，未经允许不升级或改依赖锁；避免无必要地清理缓存。Blueprint 已获准按一个项目、八章接入原生 hgraph：SpectralSequence、AdamsSynthetic、Literature、E2Computation、ProofTools、AdamsCalculations、Main、Geometry；八章对应八个数学模块；几何对象、Kervaire 不变量与 Browder 输入归属 Literature，Geometry 的两个推论保持无本地证明洞，继承上游待补状态。跨章节的原生 statement/proof 依赖必须指向更早章节；同章内部依赖遵循 hgraph 原生处理，不另设网页级循环检查；主蓝图全英文、按数学内容分节，一个数学条目可绑定多个现有 Lean 声明；外部输入在陈述前标明文章引用及原始定位。不再生成 implementation 实现索引或 verification 核验网页；Lean 源码、全部既有待补责任、接口锁与独立构建信任审计继续保留；Blueprint 只使用 hgraph 原生同步和导出，不再附加自动分组、源码依赖投影、双图合并、重复对应登记、隐藏责任状态改写、编译证据种子、快照一致性门禁或警告致命策略；网页仅保留本模块公开绑定与章节依赖顺序两项额外约束；历史记录按上述 `local-history/` 约定归档，数学说明与来源引用由 Blueprint/hgraph 维护，精简接口与证明洞基线继续入库。网页发布与全量构建分开；网页发布不依赖编译快照或全量构建，原生网页状态不代表 Lean 编译或编译依赖闭包已核验。运行方式见 [blueprint/README.md](blueprint/README.md)。
- **提交推送流程与耗时控制。** 优先复用合适的现有检出；需要隔离其他未提交工作时，优先在项目及缓存所在的同一文件系统建立临时检出，复用固定版本的依赖和已有构建缓存。缓存需要独立写入时优先使用写时复制或 reflink，避免无必要地跨盘复制整个缓存，也不得让并发构建共写同一缓存或覆盖他人的构建进度。

  检出等轻量工具持续无进展或超时时，及时检查操作是否已在后台完成；已有结果直接复用，否则切换可靠的本地 Git 流程。不得长时间反复轮询同一路径，或因工具未返回而重复创建检出。

  推送／合并、必需检查和缓存同步完成后及时交付结果。临时检出的归档与清理可排队或后续处理，不得阻塞交付；未完成时如实注明位置和状态。不得借清理删除其他工作、未提交改动或未推送提交。
- **推送与拉取时同步 Release 构建缓存。** 每次从本地向远程推送代码，都必须在同一任务中确保该远程仓库的 GitHub Release 有与已推送提交的构建输入和环境匹配、通过 `lake build` 且已校验的项目 `.lake/build/` 缓存，供其他工作者复用。先核对已有 Release，已有匹配缓存就直接复用；仅在没有匹配缓存时重新打包上传。新 Release 使用 `build-cache-<实际构建源提交>-<os>-<arch>` 等可追溯标签，并随缓存提供 `metadata.json` 和 SHA-256 校验和，记录实际源提交、构建输入指纹、仓库、操作系统/架构、Lean 工具链及 `lake-manifest.json` 哈希；不得将含有未提交源码改动的构建结果标记为已推送提交的缓存。

  是否复用按完整构建输入指纹、工具链、依赖锁及操作系统／架构判断，不仅按提交哈希判断。PR 提交与服务端合并提交等只要这些输入相同，就复用已发布 Release 及归档，避免重复打包、上传和发布。保持原缓存的实际源提交记录，在任务结果中说明当前提交与所复用 Release 的关联；不得将旧缓存元数据中的源提交改写成未经对应构建验证的新提交。缓存复用不免除必要的完整构建、信任审计和校验要求。

  每次 `git pull` 或 fetch 后 merge/rebase 更新本地源码后，即使未要求编译，也必须在同一任务中检查远程 Release，下载、校验并恢复与更新后源码和构建环境匹配的缓存；已在本地验证且匹配的缓存可直接复用。先检查元数据，再下载大文件；校验分片及合并后归档的 SHA-256。不得仅按最新 Release 选择缓存；仅 `AGENTS.md` 等不影响构建输入的文档变更可在核实后复用，否则旧缓存只能作为增量构建基线。

  恢复前确认没有构建进程写入 `.lake/build/`，将归档安全解压到临时目录并检查路径和文件类型，备份现有缓存后再安装，不得覆盖更新的本地编译进度。依赖及 Mathlib 缓存按锁定版本另行恢复；后续验证仍运行 `lake build`，利用缓存避免重复编译。上传失败须明确报告缓存尚未同步；无兼容缓存或下载失败时说明原因并继续源码更新，使用本地缓存或增量构建。普通 Git 推送、拉取不会自动同步 Release 附件，现有 GitHub Actions 缓存也不代替这项同步，必须显式执行上述步骤。
