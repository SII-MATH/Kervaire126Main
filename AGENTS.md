# 协作规则

本仓库按用户 2026-10-15 的明确要求，以 `Kervaire126-develop` 当前工作树为准合并形式化代码，并将原 Interface 拆分为 Literature 和 Computation。用户随后要求对照原 Main 的数学命名重新整理，取代迁入时保留旧声明名称的规则。采用数学对象、假设职责及经核对的论文编号命名；保留数学陈述、前提、对象关联和来源。用户随后要求将 Def 中的外部计算及文献输入迁出，并明确允许 Def 保留构造数学对象、保证定义良定所需的通用引理。

| 目录 | 职责 |
| --- | --- |
| `KIP126/Def/` | 通用数学对象、定义、接口及定义良定所需的通用引理；不含固定外部表、外部公理或待补证明。 |
| `KIP126/Literature/` | 外部文献结果、文献中的固定表、六个背景公理与标准背景选择，以及 `KIP126.Literature.adamsSyntheticResults` 公理。 |
| `KIP126/Computation/` | 固定计算数据、坐标对象及其解释、外部计算结果，以及依赖同一文献见证的 `KIP126.Computation.adamsComputations` 公理。 |
| `KIP126/Main/` | 接收外部输入，完成计算结果验证、文献应用、第六节与第七节证明及主定理推导。 |

公共入口为 `KIP126.Def`、`KIP126.Literature`、`KIP126.Computation`、`KIP126.Main` 和 `KIP126`。公共名称使用 `HF2AdamsContext`、`ExternalHypotheses`、`Main.AdamsSynthetic`、`Main.SectionSeven`、`AdamsComparison`、`E2Interpretation` 等数学术语。全仓命名审查见 `metadata/mathematical-naming-audit.json`，首轮迁移见 `metadata/mathematical-names.json`；不恢复 `Implementation`、`Challenge2`、`StageInput` 作为公共数学接口。

- **依赖方向。** Def 只依赖 Def；Literature 可依赖 Def；Computation 可依赖 Def 和 Literature；Main 可消费全部三层。不得恢复顶层 Interface、LinProgram、Checks，测试放在 `Tests/`；KIPBase 保持独立。`import all` 限于同层内部。
- **外部陈述与输入构造。** Literature、Computation 的外部结果仍用原公理给出，不把已证明或待证明结论改成新公理；结果的实际证明放 Main。输入对象定义必需的最小良定证书（例如固定关系的齐次性）按文件哈希登记于 `metadata/layer-boundaries.json`，禁止将维数、非零性、永久存活等结果证明混入这个例外。外部输入层不得有 sorry。Def 中不保留任何外部公理或固定数据表；计算表的局部证书不能替代实际球面计算结果的外部输入。
- **固定背景。** `CompletionModel` 显式参数贯穿 `SourceComparison`、`TensorComparison` 与 `HF2AdamsContext`；Literature 选择的标准对象使用同一个完备化。不得将原来固定背景上的存在性公理增强为任意背景上的存在性。最终定理类型只允许引用登记的背景选择，不允许依赖文献或计算的结果公理。
- **同一见证。** `Computation.adamsComputations` 的类型必须为 `ExternalHypotheses.ComputationHypotheses Literature.adamsSyntheticResults`。`Main.externalHypotheses` 是组合两个输入的定义，不是第三个公理；下游只能从该相关组合提取对象及事实，不得重新独立选择源对象或坐标。
- **主定理。** 保持 develop 的最终数学陈述，公共名称为 `KIP126.Main.h6_sq_permanent`：固定标准球面 Adams 谱序列中，`standardH6Square` 在 `(2, 128)` 非零永久存活。不要改为自选类、弱存活或几何 Kervaire 存在性。
- **证明状态。** 按用户最新确认保留当前六个背景公理与两个外部结果公理，现均位于 Literature/Computation。Main 第 6 节广义 Leibniz、广义 Mahowald 各有两处原有待补证明；构建通过不表示最终证明已无缺口。不得新增未登记公理、把内部目标改成假设，或调用目标占位声明完成证明。
- **记录同步。** [proof-obligations.json](metadata/proof-obligations.json) 精确登记当前公理和 sorry 位置；[external-inputs.json](metadata/external-inputs.json) 是活动来源清单。[develop-migration.json](metadata/develop-migration.json) 记录来源工作树、文件映射和原始哈希；[develop-external-inputs.json](metadata/develop-external-inputs.json) 是上游来源快照，包含历史路径，不是活动接口清单。补证后同步真实状态，不得通过修改清单掩盖缺口。
- **验证。** 保留 `module` 和显式公共导出。修改后运行 `python3 scripts/check-source-inventory.py` 及 `lake build`；构建包含 `Tests.Architecture` 和 `Tests.Trust`，检查最终类型、输入相关性及实际公理依赖。工具链和依赖锁保持固定，复用已有缓存；Lake 包名 `KIP126` 与 develop 一致。
- **推送与拉取时同步 Release 构建缓存。** 每次从本地向远程推送代码，都必须在同一任务中将与已推送提交对应、通过 `lake build` 的项目 `.lake/build/` 缓存上传到该远程仓库的 GitHub Release，供其他工作者复用。Release 使用 `build-cache-<commit>-<os>-<arch>` 等可追溯标签，并随缓存提供 `metadata.json` 和 SHA-256 校验和，记录源提交、构建输入指纹、仓库、操作系统/架构、Lean 工具链及 `lake-manifest.json` 哈希；不得将含有未提交源码改动的构建结果标记为已推送提交的缓存。

  每次 `git pull` 或 fetch 后 merge/rebase 更新本地源码后，即使未要求编译，也必须在同一任务中检查远程 Release，下载、校验并恢复与更新后源码和构建环境匹配的缓存；已在本地验证且匹配的缓存可直接复用。先检查元数据，再下载大文件；校验分片及合并后归档的 SHA-256。不得仅按最新 Release 选择缓存；仅 `AGENTS.md` 等不影响构建输入的文档变更可在核实后复用，否则旧缓存只能作为增量构建基线。

  恢复前确认没有构建进程写入 `.lake/build/`，将归档安全解压到临时目录并检查路径和文件类型，备份现有缓存后再安装，不得覆盖更新的本地编译进度。依赖及 Mathlib 缓存按锁定版本另行恢复；后续验证仍运行 `lake build`，利用缓存避免重复编译。上传失败须明确报告缓存尚未同步；无兼容缓存或下载失败时说明原因并继续源码更新，使用本地缓存或增量构建。普通 Git 推送、拉取不会自动同步 Release 附件，必须显式执行上述步骤。

重组前目标仓库完整工作区保存在 `/inspire/hdd/global_user/baokangjie-CZXS25250151/Kervaire126Main-before-reorganization-20261015T080856Z/workspace.tar.gz`。Blueprint 的迁移与检查继续延后；不可据此宣称 Blueprint 已同步。
