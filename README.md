# Kervaire126Main

[AimPaper](AimPaper/main.tex) 关于 Kervaire 不变量 126 维情形的 Lean 形式化。

- Lean：**v4.32.2**，由 [lean-toolchain](lean-toolchain) 固定。
- mathlib：`905b95818eb32af7874a58b427f50c1711a5e96c`，由 [lakefile.lean](lakefile.lean) 和 [lake-manifest.json](lake-manifest.json) 固定。

需要 elan 和 Python 3；在仓库根目录运行：

```sh
lake exe cache get  # 首次获取缓存；已有缓存可跳过
lake build
```

模块职责、接口与任务边界见 [AGENTS.md](AGENTS.md)。待补责任见 [proof-obligations.json](proof-obligations.json)；构建通过不代表全部证明完成。来源见 [migration-baseline.json](migration-baseline.json) 和 [Sources](Sources)。
