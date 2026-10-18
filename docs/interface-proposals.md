# 接口提案投递与审阅

Dashboard 的“接口提案”页签集中展示 agent 对形式化接口的独立审查报告。可搜索完整报告，按责任模块与人审状态筛选，展开全文，下载原始报告，并复制或下载审阅反馈交给 agent 回写。反馈窗口不会直接保存数据或改变状态。

## 唯一维护源

每份提案只维护 `interface-proposals/<模块>/<唯一ID>/report.md`，由 Git 跟踪。YAML 文件头保存索引和人审信息，Markdown 正文保留完整证据、候选差异及下游影响。页面按文件自动收集，无需另登记索引。不得在另一个 YAML/JSON 中平行维护同一提案。

已迁入的 17 份报告来自本地历史归档；`archived_from` 和 `archived_sha256` 记录迁入时的来源与完整原件校验值。原件作为历史快照保留；迁入后的更新只写本目录。历史 `Computation` 归属原样标明，不据此移动当前模块责任。原始状态保留，包括部分批准和未获人审批准但可继续研究的情形。

相对 AimPaper 的数学修正仍只维护 `corrections.yaml`，原文与修正版仍引用 AimPaper 和 Blueprint。接口提案记录审查及授权边界，不复制维护另一份论文修正记录；需要时在正文引用原记录和 Blueprint。

## Agent 投递

在仓库根目录创建草稿：

```sh
.lake/blueprint-env/bin/python scripts/interface-proposals.py new \
  --module ProofTools --id 20261018-example \
  --title '具体接口问题' --reporter '/root/independent_reporter'
```

也可复制 `interface-proposals/TEMPLATE.md`。填写真实 targets、完整上下文、证据、实际检查、候选的精确差异、下游影响及阻塞范围。文件头的 `independent_of_discoverer_and_implementer` 必须如实填写；模板由独立报告员使用，非独立发现笔记不应冒充独立报告。

必填文件头字段为 `issue_id`、`title`、`summary`、`responsibility_module`、`targets`、`baseline_commit`、`reporter_agent`、`independent_of_discoverer_and_implementer`、`evidence_level`、`status`、`human_decision`。额外来源元数据完整显示于“来源与原始状态”，不会被丢弃。重复 YAML 键或 ID、缺失字段及没有人审依据的批准状态会使提案校验失败。

草稿使用 `draft`；独立报告完成后设为 `pending-human-review`，没有授权时 `human_decision: null`。`summary` 应明确当前需要的行动，不把研究记录一律写成等待用户决定。可选的 `blocking`、`resolution` 等细节应同时在正文说明。

小型复现源码或日志可放在报告同目录的 `evidence/`，用相对 Markdown 链接引用。导出支持每份不超过 1 MB 的 `.lean`、`.txt`、`.json`、`.md`、`.log` 文件；不跟随符号链接，也不从本地归档隐式导出材料。未随仓库提供的历史证据会显示“本地证据”，不生成失效网页链接。完整报告下载保留原始引用路径。

## 人类审阅与状态回写

“填写审阅反馈”支持复制和下载文本；将其交给 agent 后，由 agent 把明确决定、日期、方案与授权范围回写同一报告的 `human_decision` 和正文。未明确批准的部分必须保留。页面没有自动批准或执行接口修改的动作。

支持的状态为 `draft`、`pending-human-review`、`partially-approved`、`first-clause-approved-second-clause-under-review`、`approved-interface-change`、`approved-implemented-and-validated-before-publication`、`rejected`、`withdrawn`。批准、部分批准和不采纳均要求非空的人审依据。批准不等于已完成实现或数学证明；实施验证应在正文给出实际范围。

## 校验与刷新

```sh
.lake/blueprint-env/bin/python scripts/interface-proposals.py validate
.lake/blueprint-env/bin/python -m unittest discover -s Tests -p 'test_blueprint*.py'
.lake/blueprint-env/bin/python scripts/build-blueprint.py
```

原生 hgraph 导出同时生成页签与报告页面；不依赖 `local-history/`，不修改数学依赖、公共接口或证明状态。重新导出后刷新 dashboard 可见；远程站点仍随已有 Pages 流程发布。
