# 来源与适配

本目录为修改后的 Kervaire126Main 项目版本，2026-10-20 适配；不是 Horizon 运行时安装。

- 上游：[FrenzyMath/Archon-Horizon](https://github.com/frenzymath/Archon-Horizon/tree/50989563c6577356cd6fd5c916270d8a031fc2fb)，固定提交 `50989563c6577356cd6fd5c916270d8a031fc2fb`。
- 改编文件：`src/archon_horizon/pipeline/skills/review/statement-alignment/SKILL.md` 及同目录 `references/semantic-probes.md`。
- 本地输入为 my-lean-skill 仓库保存的上述完整快照，没有跟随远程 main 更新。
- 上游版权及 Apache-2.0 条款保留于 [NOTICE](../NOTICE)、[LICENSE](../LICENSE) 与 [第三方声明](../THIRD_PARTY_NOTICES.md)。

保留完整类型回译、关键定义展开、量词与表示桥接、区分实例及证据复用。改用本项目的 AimPaper / Blueprint / corrections / interface proposals；去掉 Horizon mission、roadmap、PR 身份及 proof-review skill 依赖。增加固定 Standard 对象、模块实际归属、登记上游待补责任和原生网页状态的边界；不自动启动额外 agent 或逐声明验收。具体使用与审查结论见仓库 [适配说明](../../../../docs/review-skills.md)。
