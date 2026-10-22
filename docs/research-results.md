# 研究结果投递与阅读

Dashboard 的 **Research** 入口集中展示可持续审阅的数学研究结果。
每份报告提供完整陈述、证明、来源、计算证据和未决问题，支持全文搜索、
方向与状态筛选、公式阅读、固定链接和原始报告下载。

## 唯一维护源

每份结果维护在 `research/results/<唯一ID>/report.md`。YAML 文件头和
Markdown 正文一起进入版本控制；页面自动发现报告，无需另登记索引。
可从 `research/TEMPLATE.md` 创建新报告。后续修订只更新该报告，迁入前的
`local-history/` 原件保留为历史快照。

正文应包含固定数学对象、完整量词与结论、全部实质输入、证明、来源、
独立复核范围和未完成部分。跨版本数据差异必须明确；没有验证过的
计算输入不能因报告被复核而升级成独立证明。

## 元数据与状态

必填字段为 `result_id`、`title`、`summary`、`topic`、`status`、
`evidence_level`、`formalization_status`、`novelty_status`、`baseline_commit`、
`updated`、`authors` 和 `reviewers`。`result_id` 与目录名一致，`updated`
使用带引号的 ISO 日期。`authors` 和 `reviewers` 是姓名或 agent 标识列表。
可用 `archived_sources` 记录迁入原件的路径及 SHA-256。

三个维度分别维护：

| 维度 | 取值与含义 |
| --- | --- |
| `status` | `draft`：研究草稿；`conditional`：条件性结果；`reviewed-informal`：已完成独立非形式化复核 |
| `formalization_status` | `not-formalized`：尚未形式化；`partially-formalized`：部分形式化；`formalized`：已形式化，正文须列出实际声明和验证范围 |
| `novelty_status` | `not-assessed`：新颖性尚未核查；`not-established`：已按列明范围核查，原创性未确认；`known`：文献已有；`new`：主张新结果，正文须给出核查依据与范围 |

`reviewed-informal` 必须列出真实独立审查者。报告有多个结论时，应逐项说明
其成立条件，不能用整篇报告的复核状态掩盖某一结论仍依赖未验证输入。
独立 agent 复核不是人类批准；网页也不会检查或替代 Lean 编译认证。
不得仅凭本次会话首次得到某个结论就填写 `novelty_status: new`。
核查后须逐项区分文献已有陈述、已有理论的直接推论与未找到直接先例的候选增量；
列明实际读过的版本、定位、检索日期及无法取得的原文。没有检索命中不能证明原创性。

## 随报告提供证据

小型证据放在报告目录内，例如 `evidence/`，并用相对 Markdown 链接引用。
支持每个不超过 1 MB 的 `.md`、`.txt`、`.json`、`.lean`、`.log`、`.py`
文件。导出不跟随符号链接，不复制目录外文件，也不读取本地归档。
原始数据库、大型日志、论文 PDF 和机器上的绝对路径不隐式发布。

历史原报告可以作为附件保留，但正文须说明其历史状态，并以当前报告的
版本边界为准。原件校验和用于追溯，不另维护一份结果状态索引。
如果复现程序还依赖外部数据库，应给出版本、校验值和取得方式，不能
声称仅下载网页附件就可以完成全部复现。

## 检查与导出

```sh
.lake/blueprint-env/bin/python -m unittest discover -s Tests -p 'test_blueprint*.py'
.lake/blueprint-env/bin/python scripts/build-blueprint.py
python3 scripts/serve-blueprint.py --port 18726
```

原生 dashboard 中选择 **Research**；独立入口为
`http://127.0.0.1:18726/research/`，单份报告链接形如
`research/index.html#20261022-theta5-products`。浏览器检查见
`Tests/check_blueprint_research.py`。

网页导出与 Lean 构建分开。Research 不新增数学图节点、不改变接口或
证明状态；正式数学条目和 Lean 绑定仍按 Blueprint 规则维护。
相对 AimPaper 的修正只维护于 `corrections.yaml`，接口修改提案仍投递到
`interface/proposals/`。远程网页随既有 Pages 流程发布。
