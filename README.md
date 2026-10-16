# Kervaire126Main

[AimPaper](AimPaper/main.tex) 关于 Kervaire 不变量 126 维情形的 Lean 形式化。

- Lean：**v4.32.2**，由 [lean-toolchain](lean-toolchain) 固定。
- mathlib：`905b95818eb32af7874a58b427f50c1711a5e96c`，由 [lakefile.lean](lakefile.lean) 和 [lake-manifest.json](lake-manifest.json) 固定。

需要 elan 和 Python 3；在仓库根目录运行：

```sh
lake exe cache get  # 获取锁定版本的 Mathlib 依赖缓存；已有缓存可跳过
lake build
```

模块职责、接口与任务边界见 [AGENTS.md](AGENTS.md)。接口、契约、来源和其他记录集中在 [metadata/](metadata/)，本地路径均以仓库根目录为基准，固定上游来源与历史快照中的路径除外。待补责任见 [proof-obligations.json](metadata/proof-obligations.json)；构建通过不代表全部证明完成。来源见 [migration-baseline.json](metadata/migration-baseline.json) 和 [Sources](Sources)。Lake 的依赖锁 `lake-manifest.json` 保留在根目录。

SpectralSequence、AdamsSynthetic、Literature、Computation、ProofTools、Main 六模块在 `KIP126/` 下平级组织，公共入口为 `KIP126.<模块名>`。移除原 `Def/` 目录层级的路径映射和验证记录见 [module-path-migration.json](metadata/module-path-migration.json)；历史来源仍使用其原始提交中的路径。

测试集中在 `Tests/`。`Tests.Architecture` 通过普通根导入检查六模块入口和固定主目标；各模块子目录保留精确接口、公共消费及边界测试，`Tests.Integration` 另外验证上游消费无需导入 Main。`Tests.Trust` 汇总全部测试，检查测试自身没有引入公理或未完成证明。上述检查及六模块内部审计都纳入默认 `lake build`；单独检查总入口可运行 `lake build ArchitectureChecks`。修改后还应运行 `python3 scripts/check-source-inventory.py`，核对源文件覆盖与模块依赖边界。

推送代码时，须在同一任务中把对应提交通过 `lake build` 的项目 `.lake/build/` 缓存上传到该仓库的 GitHub Release。标签应包含提交、操作系统和架构，例如 `build-cache-<commit>-<os>-<arch>`；附件包含缓存归档、`metadata.json` 和 SHA-256 校验和。元数据记录源提交、构建输入指纹、仓库、系统/架构、Lean 工具链和依赖锁哈希，不能把未提交源码的构建结果标记为已推送提交的缓存。

拉取并合并或变基更新源码后，即使没有要求编译，也须在同一任务中检查 Release：先核对元数据，选择与源码及环境匹配的缓存，再下载并校验归档（含分片校验）。已有本地匹配缓存可直接复用；只有不影响构建输入的文档变化可在核实后跨提交复用，其他旧缓存仅作为增量构建基线。安装前确认没有构建进程写入缓存，临时安全解压并检查路径和文件类型，备份后安装，保留更新的本地编译进度。后续仍运行 `lake build` 验证。没有兼容缓存或下载失败时说明情况并继续源码更新和增量构建；上传失败则明确报告缓存未同步。完整要求见 [AGENTS.md](AGENTS.md)。

项目 Release 缓存与 Mathlib 依赖缓存分别恢复；`lake exe cache get` 获取后者。[CI](.github/workflows/ci.yml) 的 GitHub Actions 缓存保存 `.lake` 以加速 CI，不能代替面向其他工作者的 Release 附件；普通 Git 推送、拉取也不会自动同步这些附件。
