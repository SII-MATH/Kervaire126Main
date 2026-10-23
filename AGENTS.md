# 协作规则

| 模块（接口清单） | 职责 |
| --- | --- |
| [SpectralSequence](interface/baselines/spectral-sequence-api.json) | 谱页、微分、代表、存活、滤过、收敛、检测与 ESS；Algebra 为内部支撑。 |
| [AdamsSynthetic](interface/baselines/adams-synthetic-api.json) | 固定范畴、Adams 系统、标准类、乘法、ν、λ 商与比较。 |
| [Literature](interface/baselines/literature-api.json) | 带来源和完整条件的文献结果，包括几何对象、Kervaire 不变量构造与 Browder 桥接。 |
| [AdamsComputation](interface/baselines/adams-computation-api.json) | 对应上游 `Adams`：独立的 Ext／E₂ 基底、维数、乘法、标准类标定、实际 E₂ 比较及直接计算的 d₂；不得依赖 ProofTools 或 SSComputation。 |
| [ProofTools](interface/baselines/proof-tools-api.json) | stretching、广义 Leibniz、广义 Mahowald 及公共操作定理。 |
| [SSComputation](interface/baselines/ss-computation-api.json) | 对应上游 `ss`：传播或推导的 Adams 微分（包括 d₂）、边界、存活、永久循环及高页计算；可以使用 AdamsComputation 输入和 ProofTools。 |
| [Main](interface/baselines/main-api.json) | 论文局部推导及标准 h₆² 非零永久存活目标。 |
| [Geometry](interface/baselines/geometry-api.json) | AimPaper 的 126 维几何存在性与完整维数分类；调用 Literature 的几何对象、不变量和 Browder 输入以及 Main。 |

公共入口为 `KIP126.<模块名>`，八个数学模块在 `KIP126/` 下平级组织，依赖按 `AdamsComputation → ProofTools → SSComputation → Main → Geometry` 分层；ProofTools 只能调用 AdamsComputation 的 E₂ 子层（`KIP126.AdamsComputation.E2` 及其组成模块），不得导入该模块的直接 d₂ 数据。原 `KIP126.Computation` 及其子路径的兼容入口已删除，计算内容直接从 `KIP126.AdamsComputation` 或 `KIP126.SSComputation` 导入；现有公开声明的 `KIP126.Computation.*` 名称不变，责任归属以实际定义源模块为准。`interface/baselines/` 只保留精简构建基线：`*-api.json` 锁定公开类型、宇宙参数、公理依赖及导出，`proof-obligations.json` 锁定许可证明洞与 Main/ProofTools 审计边界，命名清单保留检查所需的改名对应。数学说明与论文对应维护在 Blueprint，接口范围说明放在 hgraph 原生节点附件，出处统一使用 bibliography 引用；不再平行维护契约和来源 JSON。格式见 [元数据检查基线](docs/metadata-baselines.md)。历史计算审计、接口审查、证明会话、报告、完整元数据快照和一次性迁移记录统一放在被 Git 忽略的 `local-history/`，内部保留原目录结构；整理方式与恢复说明见 [历史材料归档](docs/history-archive.md)。根目录 `corrections.yaml` 是相对原始 AimPaper 的修正记录唯一维护源，由 Git 跟踪；agent 按结构化条目记录问题、反例、修复状态与 Blueprint 节点引用，格式见 [修正记录维护](docs/corrections.md)。原文与修正版陈述分别引用 AimPaper 和 Blueprint，不另写一份。不另建平行记录文件。精简时须保留修正范围与未完成边界。清单内部的本地路径以仓库根目录为基准；固定上游来源与历史快照保留其原始路径。Lake 的依赖锁 `lake-manifest.json` 保留在根目录。

- **接口冻结。** 未经用户明确允许，不增删或改变公共声明的名称、类型、前提、语义、对象关联及导出。认为接口不合理或不足时，提交具体修改方案、理由和下游影响，获准后实施；不得改锁文件绕过检查。已有授权不重复确认。
- **接口提案投递。** 独立接口审查报告统一维护在 `interface/proposals/<责任模块>/<唯一ID>/report.md`，由 Git 跟踪并在 dashboard 的 **Interfaces → Proposals** 区域展示；投递模板、校验与人审回写见 [接口提案指南](docs/interface-proposals.md)。从 `local-history/metadata/interface-reviews/` 迁入的原件仅作历史快照，后续更新只写提案目录。报告必须保留完整前提、固定对象、证据等级、候选差异、下游影响和明确授权范围；未获人审批准不等于当前必须暂停工作。相对 AimPaper 的修正仍唯一维护于 `corrections.yaml`，不在提案中平行维护修正版陈述。
- **研究结果投递。** 供持续审阅的研究结果维护在 `research/results/<唯一ID>/report.md`，随小型证据由 Git 保存并在 dashboard 的 **Research** 入口展示，格式见 [研究结果指南](docs/research-results.md)。文件头与正文为唯一维护源；迁入的本地原件只保留作历史快照。完整记录数学对象、量词、输入、证明、独立复核、形式化状态、新颖性核查与未完成边界，不把局部引理写成已解决开放问题，不将研究复核等同于人类批准或 Lean 认证。此入口不改变数学模块责任、正式 Blueprint 绑定、接口或证明洞；正式论文修正仍唯一维护于 `corrections.yaml`。
- **单模块任务。** 未经明确允许，不修改其他模块、接手其证明或移动责任归属。阅读和调用上游公共接口可以正常进行。
- **自顶向下证明。** 从当前目标递归拆分局部引理与构造，直到接到已有上游接口、mathlib 或基础定义；依赖不得成环。辅助声明保持私有。
- **上游直接调用。** 上游已登记的待构造、待证明接口可直接使用，责任不转入下游；不恢复 Challenge、结果包或额外假设，保留真正的数学前提。
- **Blueprint 绑定。** 每章的 Lean 绑定只能指向实际定义在同名数学模块、且列入该模块公开接口锁的 public 声明，归属以源文件为准，不按命名空间或使用者判断。绑定必须对应条目正文实际定义的对象或陈述的结论；背景对象、前提、用于表达结论的既有谓词及证明中调用的辅助步骤不得作为该结论的额外绑定，同模块内也适用。正文确实分别陈述多个对象或结论时可绑定多个声明。跨模块内容通过原生数学条目引用连接，不混入 `\lean`／`\uses{decl:…}` 形式化绑定；仅有局部辅助步骤时如实保留未完成范围，不冒充完整陈述的直接形式化对应。私有构造与证明责任保留在 Lean 源码、内部依赖审计和待补清单中，不生成私有声明的数学条目绑定；网页状态遵循 hgraph 原生的源码局部状态与手写依赖闭合；不额外改写隐藏责任状态，完整 Lean 信任审计仍由独立构建负责。
- **如实记录。** 保持接口不变的补证明及状态更新无需另行批准；同步来源、测试和 [待补清单](interface/baselines/proof-obligations.json)。未经允许不新增公理或待补责任，不能靠放宽检查掩盖缺口。
- **封装与检查。** 使用 `module`，默认私有、显式 `public`；`import all` 仅限同模块内部及测试审计汇总。遵守依赖方向，以普通导入验证公共消费。测试集中在 `Tests/`：`Tests.Architecture` 检查八个数学模块与固定主目标，各模块专项测试保留接口锁、公共消费和边界检查；各模块独立接口锁须保持导出完整、归属唯一，`Tests.Integration` 保留上游独立消费检查，`Tests.Trust` 汇总审计全部测试。修改后运行 `python3 scripts/check-source-inventory.py` 和 `lake build`，后者默认包含这些检查；复用缓存，不以精简测试为由删除已有覆盖。`Checks.Registry` 仅用于追踪待补清单的构建输入，不是数学模块。
- **工程边界。** 工具链按 [README](README.md) 固定，未经允许不升级或改依赖锁；避免无必要地清理缓存。Blueprint 已获准按一个项目、八章接入原生 hgraph：SpectralSequence、AdamsSynthetic、Literature、AdamsComputation、ProofTools、SSComputation、Main、Geometry；八章对应八个数学模块；几何对象、Kervaire 不变量与 Browder 输入归属 Literature，Geometry 的两个推论保持无本地证明洞，继承上游待补状态。跨章节的原生 statement/proof 依赖必须指向更早章节；同章内部依赖遵循 hgraph 原生处理，不另设网页级循环检查；主蓝图全英文、按数学内容分节，一个数学条目可绑定多个现有 Lean 声明；外部输入在陈述前标明文章引用及原始定位。不再生成 implementation 实现索引或 verification 核验网页；Lean 源码、全部既有待补责任、接口锁与独立构建信任审计继续保留；Blueprint 只使用 hgraph 原生同步和导出，不再附加自动分组、源码依赖投影、双图合并、重复对应登记、隐藏责任状态改写、编译证据种子、快照一致性门禁或警告致命策略；网页仅保留本模块公开绑定与章节依赖顺序两项额外约束；历史记录按上述 `local-history/` 约定归档，数学说明与来源引用由 Blueprint/hgraph 维护，精简接口与证明洞基线继续入库。网页发布与全量构建分开；网页发布不依赖编译快照或全量构建，原生网页状态不代表 Lean 编译或编译依赖闭包已核验。运行方式见 [blueprint/README.md](blueprint/README.md)。
- **main 合并流程。** 合并到 `origin/main` 必须通过以 `main` 为目标的 GitHub PR，并等待必需的 `Lean checks` 及其他分支保护检查通过；启用合并队列时，使用该队列完成合并。不得直接推送到 `main`，不得使用管理员绕过、强制推送或关闭必需检查来完成合并。用户要求“合并到 origin/main”即授权执行这一完整 PR 流程；必须确认 PR 已实际合并，不能只开启自动合并便报告完成。
- **合并后同步当前工作目录。** 在临时或其他 worktree 中处理 PR 时，记录任务开始时用户当前工作目录的路径、分支和 HEAD。确认 PR 已实际合并后，在同一任务交付前检查该目录的分支、跟踪远端、暂存／未暂存／未跟踪改动、进行中的 Git 操作，以及使用该目录或其构建缓存的构建进程。仅当该目录位于 `main`、工作区干净、无进行中的 Git 操作或构建／缓存写入，且可快进到 `origin/main` 时，获取远端更新并以 `git merge --ff-only origin/main` 同步；实际更新前再次核对这些条件，保留原有开发缓存。同步后确认本地 HEAD 与远端一致，并核对 `AGENTS.md`、README 等规则已是合并后的版本，不能只更新临时 worktree 或远端便宣称当前目录已同步。有未提交改动、正在构建、处于其他分支或存在分叉等情况时保留现场，不强行切换分支、合并、重置、自动 stash、终止构建或覆盖缓存；交付时明确待同步目录、本地与远端提交及未同步原因，待安全时补做。此同步检查不得被临时 worktree 清理省略，也不要求等待后台 Release 缓存发布。
- **提交推送流程与耗时控制。** 优先复用合适的现有检出；需要隔离其他未提交工作时，优先在项目及缓存所在的同一文件系统建立临时检出，复用固定版本的依赖和已有构建缓存。缓存需要独立写入时优先使用写时复制或 reflink，避免无必要地跨盘复制整个缓存，也不得让并发构建共写同一缓存或覆盖他人的构建进度。

  本机单槽 CI 使用独立于日常开发的专用账户和持久化缓存；同一 Lean 工具链与依赖锁下，连续检出、PR 和合并队列任务直接复用同一构建目录，由完整 `lake build` 判断并执行增量编译。不按提交或构建输入指纹拆分、复制整份工作缓存，也不因源码指纹变化主动恢复整份 Release 缓存。工具链或依赖锁变化时使用另一环境目录，保留原缓存。单槽串行执行是此复用方式的前提；并发构建仍须独立写入，不得共写开发缓存。旧布局迁移使用同盘重命名，保留已有构建进度，不做整份复制。

  检出等轻量工具持续无进展或超时时，及时检查操作是否已在后台完成；已有结果直接复用，否则切换可靠的本地 Git 流程。不得长时间反复轮询同一路径，或因工具未返回而重复创建检出。

  推送／合并和必需检查完成后及时交付结果，不等待后台 Release 缓存发布；报告其已发布、待处理或重试状态。临时检出的归档与清理可排队或后续处理，不得阻塞交付；未完成时如实注明位置和状态。不得借清理删除其他工作、未提交改动或未推送提交。
- **合并后的异步 Release 构建缓存。** Release 缓存只由合并后 `main` 的成功 CI 构建生成，不再要求每次本地推送、PR 或合并队列提交都有精确 Release 缓存。后台发布服务独立于必需检查和 Lean CI 槽；默认等待 60 秒合并连续 `main` 更新，待处理请求只保留最新提交。已有发布开始后可能完成原提交，再处理最新请求。日常推送、合并和任务交付不等待打包或上传；如实报告后台状态，不把待发布或失败说成已同步。

  发布前核对 GitHub 的仓库、`main` push、工作流、实际源提交、run attempt、成功的源码清单与完整 `lake build`，只读取 CI 专用工作缓存；CI 开始新任务或检出变化时让步，丢弃未完成归档并重试，不锁住 CI、不复制或覆盖开发缓存。归档完成后独立上传其不可变文件。缓存发布失败不影响已通过的检查或合并，保留持久队列和正确分片，自动退避重试（最长间隔 15 分钟），并支持手动重试和重启恢复。发布器只运行已审核、安装在 job 可写目录之外的可信代码；凭据不传给 CI 作业。

  先检查已有 Release，按完整构建输入指纹、工具链、依赖锁、仓库及操作系统／架构匹配；匹配且校验通过时直接复用，避免重复打包、上传。新 Release 使用 `build-cache-<实际构建源提交>-<os>-<arch>` 等可追溯标签，提供 `metadata.json`、完整输入清单、成功构建日志和 SHA-256 校验和，记录实际源提交、环境和 `lake-manifest.json` 哈希。逐文件检查归档路径、文件类型与 SHA-256，并验证每个上传分片的服务端摘要，全部通过后才将草稿正式发布；中断后只补传缺失或损坏的预期分片，不修改已发布缓存。相同输入的后续 `main` 提交可复用原 Release，保留原缓存实际源提交，不改写成未经对应构建验证的新提交。

  拉取或 merge/rebase 更新源码时，优先保留已在本地验证且匹配的缓存；需要恢复时先读取远程元数据，再下载和校验匹配缓存。异步缓存尚未发布、下载失败或没有兼容缓存时，不等待发布、不阻塞源码更新或交付，使用本地工作缓存或已校验的同环境旧缓存作为增量基线，由完整 `lake build` 验证当前输入，不把旧基线声称为当前输入已通过。恢复前确认没有写入 `.lake/build/` 的构建进程，安全解压到临时目录并检查路径和文件类型，备份现有缓存后安装，不得覆盖更新的编译进度；校验分片及合并归档的 SHA-256。依赖及 Mathlib 缓存按锁定版本另行恢复。本机单槽 CI 连续检出仍直接复用自身环境缓存，只有缓存缺失、损坏需重建或用户明确要求时恢复 Release；完整构建、信任审计和其他必需检查始终保留。
