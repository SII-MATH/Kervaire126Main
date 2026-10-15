# Kervaire126Main

Kervaire 不变量问题中 126 维情形的 Lean 形式化仓库，围绕 AimPaper 组织谱序列基础、Adams／synthetic 系统、文献与计算接口、证明工具及论文主证明。

各模块通过固定对象和可直接调用的定理连接。上游尚未完成的构造或证明逐项登记，下游可以直接使用接口；这不表示整个形式化已经消除所有 `sorry`。

## 固定工具链

| 依赖 | 固定版本 |
| --- | --- |
| Lean | `leanprover/lean4:v4.32.2`，见 [lean-toolchain](lean-toolchain) |
| mathlib | `905b95818eb32af7874a58b427f50c1711a5e96c`，见 [lakefile.lean](lakefile.lean) |
| 传递依赖 | 由 [lake-manifest.json](lake-manifest.json) 锁定 |

构建环境需要 elan 和 Python 3。在仓库根目录使用 elan／Lake 选择上述工具链。首次准备依赖缓存及构建：

```sh
lake exe cache get
lake build
```

已有缓存时直接运行 `lake build`。不要为日常构建执行 `lake update` 或清空 `.lake`；工具链及依赖升级须得到明确批准。

## 模块导航

| 模块 | 职责 | 公共入口 |
| --- | --- | --- |
| SpectralSequence | 通用谱序列、滤过、收敛、检测及 ESS；包含内部 Algebra 支撑 | [KIP126.Def.SpectralSequence](KIP126/Def/SpectralSequence.lean) |
| AdamsSynthetic | 固定的 Adams／synthetic 背景、标准类、ν、λ 商及比较 | [KIP126.Def.AdamsSynthetic](KIP126/Def/AdamsSynthetic.lean) |
| Literature | 保留来源与完整条件的文献结果 | [KIP126.Def.Literature](KIP126/Def/Literature.lean) |
| Computation | 实际对象上的计算结果、坐标与标准类标定 | [KIP126.Def.Computation](KIP126/Def/Computation.lean) |
| ProofTools | stretching、广义 Leibniz、广义 Mahowald 及公共操作定理 | [KIP126.Def.ProofTools](KIP126/Def/ProofTools.lean) |
| Main | 论文局部推导与最终非零永久存活目标 | [KIP126.Main](KIP126/Main.lean) |

公共接口、模块证明职责及变更规则见 [AGENTS.md](AGENTS.md)。每个模块分别维护 `*-api.json`（完整类型及导出）、`*-contracts.json`（数学用途及消费者）和 `*-sources.json`（来源记录）。

## 检查与证明状态

默认 `lake build` 包含接口类型与导出、可见性、公共消费样例、源码覆盖、依赖边界及公理／待补责任检查。模块检查目标为 `SpectralSequenceChecks`、`AdamsSyntheticChecks`、`LiteratureChecks`、`ComputationChecks`、`ProofToolsChecks`、`MainChecks`；总体验证为 `IntegrationChecks`。

待补声明及归属以 [proof-obligations.json](proof-obligations.json) 为准。构建成功表示代码和约定检查通过，不表示所有上游构造与证明已完成。接口变更及跨模块任务须经用户明确允许；证明任务从当前目标递归展开，接到已有上游接口为止。

[AimPaper/main.tex](AimPaper/main.tex) 是迁入的论文源文件；Blueprint 迁移与检查暂缓。原仓库固定迁移基线、来源和 attribution 见 [migration-baseline.json](migration-baseline.json) 及各模块来源清单，原始来源与许可证保留在 [Sources](Sources)。
