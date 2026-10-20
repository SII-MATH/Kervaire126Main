# 来源与适配

本目录为修改后的 Kervaire126Main 项目版本，2026-10-20 适配；不是 Horizon 运行时安装。

- 上游：[FrenzyMath/Archon-Horizon](https://github.com/frenzymath/Archon-Horizon/tree/50989563c6577356cd6fd5c916270d8a031fc2fb)，固定提交 `50989563c6577356cd6fd5c916270d8a031fc2fb`。
- 改编文件：`src/archon_horizon/pipeline/skills/review/definition-quality/SKILL.md` 及同目录 `references/representation-experiments.md`。
- 本地输入为 my-lean-skill 仓库保存的上述完整快照，没有跟随远程 main 更新。
- 上游版权及 Apache-2.0 条款保留于 [NOTICE](../NOTICE)、[LICENSE](../LICENSE) 与 [第三方声明](../THIRD_PARTY_NOTICES.md)。
- 传递来源：Horizon 的 `skills/_sources/lean4-skills/PROVENANCE.md` 将该 skill 的实例及 API 审查指导追溯到 [cameronfreer/lean4-skills](https://github.com/cameronfreer/lean4-skills/tree/4400419ba345fd0dc07f278359b372505780ef71) 的 `instance-pollution.md` 与 `mathlib-review-taxonomy.md`，固定提交 `4400419ba345fd0dc07f278359b372505780ef71`。Copyright (c) 2025 Lean 4 Theorem Proving Skill Contributors；条款见 [LICENSE-MIT.md](../LICENSE-MIT.md)。

保留真实消费者、规范 API、实例核对与最小表示实验。删除未安装的 lean-search / lean-refactor skill 依赖及 Horizon 后处理强制修复规则；按本项目冻结接口、模块所有权、普通公共导入及既有提案规则处理建议。与 statement-alignment 共享语义检查范围，只有表示或工程问题才展开额外审查。具体使用与审查结论见仓库 [适配说明](../../../../docs/review-skills.md)。
