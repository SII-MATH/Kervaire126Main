# 修正记录维护

根目录 `corrections.yaml` 是 **AimPaper corrections** 页面的唯一记录源，由 Git 跟踪。Agent 直接编辑其中的条目，页面自动生成。不再维护其他平行记录文件。

文件使用 `version: 1`，`scope` 保留全局修正范围及未完成边界，`corrections` 是按展示顺序排列的条目列表。

| 字段 | 维护内容 |
| --- | --- |
| `id` | 稳定且唯一的小写标识；更新条目时保持不变。 |
| `title` / `reference` | 问题标题和原论文定位，例如 Proposition 6.20 的第一段。 |
| `status.kind` / `status.label` | 展示分类 `proposed`、`revised`、`partial`，以及如实限定范围的进展文字。它们不改变 Lean 完成状态。 |
| `original.statements` / `original.source_line` | 原文编号列表和 `AimPaper/main.tex` 行号；页面按 Blueprint 出处读取完整原文，不手抄陈述。编号写为字符串。 |
| `original.include_proof_claim` | 可选布尔值；Corollary 1.5 另展示原证明中的第三页候选清单时使用。 |
| `revision.nodes` | 修正版 Blueprint 节点标签列表；页面直接读取这些节点的完整英文正文。 |
| `revision.definitions` | 可选的前置定义节点，放在修正版中的 Definitions 折叠项内。 |
| `revision.note` | 无修正版节点时必须明确写出的缺口；不能另写一个陈述冒充 Blueprint 节点。 |
| `problem` / `counterexample` | 问题及原因、可选反例；保留完整前提、对象、结论和适用边界。 |
| `progress` / `history` | 当前进展及未完成边界、可选论证与修订过程。 |
| `links` | 每项用 `node` 和 `title` 指向相关 Blueprint 条目。 |

说明文本使用 YAML 的 `|` 多行块，支持原生 Markdown 行内格式、链接及 LaTeX 公式；无需另建 `.md` 记录。所有文本字段都会显示，拼错或重复的键、重复的条目标识、不正确的类型会使生成失败，避免静默丢失内容。引用不存在的 Blueprint 节点也会使导出失败。

新增或更新记录时，以现有条目为模板，核对原文定位、问题或反例的完整条件、修正范围及当前未完成责任。修正版自然语言写在其所属 Blueprint 数学节点中，并按模块规则绑定已有公共 Lean 声明；记录只维护节点标签。不得把局部证明完成写成上游责任已全部完成，也不要省略已有历史、证据或边界。

运行格式及展示检查：

```sh
.lake/blueprint-env/bin/python -m unittest discover -s Tests -p 'test_blueprint*.py'
```

仅改记录或展示时，复用已核验数学导出刷新本地预览：

```sh
.lake/blueprint-env/bin/python scripts/preview-memo.py
python3 scripts/serve-blueprint.py --port 18728 --directory .lake/blueprint/memo-statements-preview
```

新增或修改 Blueprint 节点、绑定或数学依赖时，先用 `scripts/build-blueprint.py` 重新生成并核验数学数据，再刷新预览。预览的 `validation.json` 区分已核验的数学快照与当前展示输入；本地预览不等于远程发布。
