# Kervaire126Main

证明管理前端采用原生 hgraph：一个项目，八章依次为 SpectralSequence、AdamsSynthetic、Literature、E2Computation、ProofTools、AdamsCalculations、Main、Geometry；第八章单列尚未形式化的几何终点。主蓝图用英文按数学内容组织，一个条目可绑定多个现有 Lean 声明；完整源码另作实现索引，真实编译依赖与既有待补责任继续核验。生成、发布与预览方式见 [Blueprint 使用说明](blueprint/README.md)；现有接口锁和默认构建检查继续保留。

[AimPaper](AimPaper/main.tex) 关于 Kervaire 不变量 126 维情形的 Lean 形式化。

- Lean：**v4.32.2**，由 [lean-toolchain](lean-toolchain) 固定。
- mathlib：`905b95818eb32af7874a58b427f50c1711a5e96c`，由 [lakefile.lean](lakefile.lean) 和 [lake-manifest.json](lake-manifest.json) 固定。

需要 elan 和 Python 3；在仓库根目录运行：

```sh
lake exe cache get  # 获取锁定版本的 Mathlib 依赖缓存；已有缓存可跳过
lake build
```

模块职责、接口与任务边界见 [AGENTS.md](AGENTS.md)。[metadata/](metadata/) 只保留接口、许可证明洞、审计边界与命名检查所需的精简基线，格式见 [元数据检查基线](docs/metadata-baselines.md)。数学说明与论文对应在 Blueprint 中维护，接口范围说明保存在 hgraph 原生节点附件；文献及固定代码版本通过 bibliography 引用，代码版本条目见 [source-snapshots.bib](blueprint/source-snapshots.bib)。待补工作由 Lean 编译证据和 hgraph 依赖状态展示；[proof-obligations.json](metadata/proof-obligations.json) 保留证明洞许可基线，构建通过不代表全部证明完成。Lake 的依赖锁 `lake-manifest.json` 保留在根目录。

SpectralSequence、AdamsSynthetic、Literature、E2Computation、ProofTools、AdamsCalculations、Main 七个数学模块在 `KIP126/` 下平级组织，公共入口为 `KIP126.<模块名>`。计算层按 `E2Computation → ProofTools → AdamsCalculations → Main` 单向组织：E₂ 层提供独立的基底、乘法、维数和实际对象比较；后续 Adams 层负责微分、边界与存活。原 `KIP126.Computation` 及其子路径保留为只含导入的兼容入口，所有既有 `KIP126.Computation.*` 公开声明名称与接口锁保持不变；新的数学导入使用实际分层入口。移除原 `Def/` 目录层级的路径映射和验证记录已归档到 `local-history/metadata/module-path-migration.json`；历史来源仍使用其原始提交中的路径。

历史计算审计、接口审查、证明会话、报告及完整契约和来源 JSON 统一放在被 Git 忽略的 `local-history/`，本地文件保留，整理与恢复方式见 [历史材料归档](docs/history-archive.md)。[MEMO.md](MEMO.md) 保留在仓库根目录并继续入库，其中历史证据链接指向本地归档。构建、hgraph 导出与精简基线更新均不要求归档目录存在。

测试集中在 `Tests/`。`Tests.Architecture` 通过普通根导入检查七个数学模块、兼容入口和固定主目标；各模块子目录保留精确接口、公共消费及边界测试，`Tests.Integration` 另外验证上游消费无需导入 Main。`Tests.Trust` 汇总全部测试，检查测试自身没有引入公理或未完成证明。E₂ 与后续 Adams 的独立入口检查同时验证旧 Computation 接口锁的精确分区。上述检查及各数学模块内部审计都纳入默认 `lake build`；单独检查总入口可运行 `lake build ArchitectureChecks`。修改后还应运行 `python3 scripts/check-source-inventory.py`，核对源文件覆盖与模块依赖边界。

推送代码时，须在同一任务中把对应提交通过 `lake build` 的项目 `.lake/build/` 缓存上传到该仓库的 GitHub Release。标签应包含提交、操作系统和架构，例如 `build-cache-<commit>-<os>-<arch>`；附件包含缓存归档、`metadata.json` 和 SHA-256 校验和。元数据记录源提交、构建输入指纹、仓库、系统/架构、Lean 工具链和依赖锁哈希，不能把未提交源码的构建结果标记为已推送提交的缓存。

拉取并合并或变基更新源码后，即使没有要求编译，也须在同一任务中检查 Release：先核对元数据，选择与源码及环境匹配的缓存，再下载并校验归档（含分片校验）。已有本地匹配缓存可直接复用；只有不影响构建输入的文档变化可在核实后跨提交复用，其他旧缓存仅作为增量构建基线。安装前确认没有构建进程写入缓存，临时安全解压并检查路径和文件类型，备份后安装，保留更新的本地编译进度。后续仍运行 `lake build` 验证。没有兼容缓存或下载失败时说明情况并继续源码更新和增量构建；上传失败则明确报告缓存未同步。完整要求见 [AGENTS.md](AGENTS.md)。

项目 Release 缓存与 Mathlib 依赖缓存分别恢复；`lake exe cache get` 获取后者。[CI](.github/workflows/ci.yml) 的 GitHub Actions 缓存保存 `.lake` 以加速 CI，不能代替面向其他工作者的 Release 附件；普通 Git 推送、拉取也不会自动同步这些附件。
