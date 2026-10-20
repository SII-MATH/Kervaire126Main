---
name: blueprint-authoring
description: 撰写和维护 Kervaire126Main 的 hgraph Blueprint 数学条目、非形式化证明与来源说明；按现有风格区分 From 与 A … revision of，同步标签、数学依赖和 Lean 绑定。用于 Blueprint 写作、重组和来源整理；单纯语义对齐审查使用 statement-alignment。
metadata:
  category: authoring
---

# Blueprint 撰写与维护

先读仓库根目录 [AGENTS.md](../../../AGENTS.md) 和 [Blueprint 写作规范](../../../blueprint/README.md#authoring-and-provenance)，再读目标条目、相邻定义与证明、相关来源和已有修正。它们是当前项目规则的维护源；本 skill 提供写作方法，不另设一套 Blueprint 规范。下文路径均以仓库根目录为基准。

## 明确来源关系

查本地已有论文、原始 TeX、BibTeX 和固定来源版本，再按需补查。核对具体编号、周围定义和全局假设；涉及符号、量词、次数或公式时，不能仅凭检索摘要或 OCR 文本认定原文。区分作者的结论、我们的推论和 Lean 表示。

按数学内容而非文字改动量选择陈述前的普通来源段落：

| 关系 | 写法 |
| --- | --- |
| 抄录或数学等价转述，包括记号替换 | `From \cite{key}, Theorem 6.1.` |
| 改变前提、定义域、结论或指定的比较关系 | `A level-indexed revision of \cite{key}, Theorem 6.1.` 等，准确命名修改性质 |
| 项目自行推导的结果 | 说明使用了哪些既有数学条目及推导，不把相近的文献结果冒充直接来源 |

写全 `Theorem`、`Proposition`、`Corollary` 等定位。`From` 不要求逐字相同；`revision` 也不能仅表示重新排版或改写英文。revision 必须让读者看清改变了哪些条件、对象或结论以及适用边界；不能把改写本身当作修正版的正确性或批准依据。

声明出处与证明方法出处分别表达。引用某个证明思路不表示原文证明了当前修正版，形式化了代理表示也不表示已证明到原对象的对应。具体写法与真实项目例子见 [examples.md](references/examples.md)。

## 写成可独立阅读的数学条目

按八章组织英文正文，数学条目直接写入 `blueprint/chapters/<模块>.tex`，按数学内容分节。给读者必要的背景、固定对象、符号、全部假设和精确结论；定义在使用前解释或引用，证明给出关键推导和所用结果。粒度以数学内容为准，不按 Lean 文件、声明数量、消费者分组或 agent 任务机械拆分。

定理类环境后紧接独立的 `\begin{proof} ... \end{proof}`。证明可以是完整论证、引用后的特化推导或明确限定的证明草图；没有补完的桥接和步骤必须如实说明，不以“标准”“类似可得”跳过实际缺口。定义无需强行添加证明。

保留原文抄录块和已有别名标签；需要修正版时按现有条目与 corrections 组织方式处理，不静默修改标成原文的内容。现有标题、标签与条目归属不因完成状态改变。不要把会话记录、任务调度、迁移历史或大段 Lean 名称清单写进数学正文；必要的对应范围与未完成边界可沿用 `% Blueprint note:` / `% Correspondence:`，它们会作为原生节点评论发布。

## 维护 hgraph 对应与依赖

- 使用稳定 `\label` 和原生引用连接数学条目；重命名或拆分时检查实际引用、别名及修正记录，不仅修改标题。
- 声明里的 `\uses` 记录表述所需的数学前提，proof 里的 `\uses` 记录论证实际使用的结果；两者都进入原生依赖。普通阅读引用与 bibliography 引用不自动构成依赖。不要把全部 Lean import 或实现依赖复制进图，也不要求消费目标节点绑定的每个声明。
- `\lean` 只绑定正文实际定义的对象或陈述的结论。核对全限定名、实际定义模块和公开接口锁；一个条目确实陈述多个对象或结论时可多绑定。背景对象、前提谓词和证明中的辅助步骤不能冒充结论绑定。
- 遵守项目同模块公开绑定和跨章依赖顺序两项边界；跨模块通过数学条目引用，不用跨模块 `\lean` 或 `\uses{decl:…}` 绕过。私有辅助声明不生成正式数学绑定；同章内部依赖沿用原生机制。
- 用原生同步与导出维护生成节点和状态，保留已有人工评论。不把 `\leanok`、`\mathlibok`、`\sketch` 等标记当作作者可自行设置的完成证据；按当前原生含义和实际对应使用，不为了网页变绿改写状态。网页局部状态及手写依赖闭合不代表 Lean 编译或传递证明依赖已核验。

只有局部形式化对应时，限定已覆盖范围，不能补上辅助绑定来假装完整。发现来源与 Lean 的数学含义存在疑点时，使用已安装的 [statement-alignment](../statement-alignment/SKILL.md)；普通文字整理不重复执行完整语义或定义工程审查。

## 同步、检查与交付

修改陈述时同时核对来源措辞、证明、数学依赖和 Lean 定位，保留未完成责任。相对 AimPaper 的修正仍唯一维护在 `corrections.yaml`，原文与修正版引用 AimPaper 和 Blueprint；按 [修正记录指南](../../../docs/corrections.md) 更新已有记录，不另建来源 JSON、契约表或平行修正正文。

本 skill 不授权改变冻结 Lean 接口、移交模块责任或新增公理/证明洞。数学调整涉及这些边界时，遵守已有授权，并按 [接口提案指南](../../../docs/interface-proposals.md) 给出精确差异和下游影响；不因发现一个疑点暂停无关工作。

按实际改动使用项目现有检查：Blueprint 内容、绑定或依赖变动时，运行 `.lake/blueprint-env/bin/python -m unittest discover -s Tests -p 'test_blueprint*.py'`，并用 `.lake/blueprint-env/bin/python scripts/build-blueprint.py` 检查原生同步与导出。工具不可用、失败或未运行分别报告，不把未检查写成成功渲染。核对所改条目的公式、来源、Proof 面板和导航；有可用浏览器时检查实际显示，否则限定验证范围。

Lean 验证按 `AGENTS.md` 独立执行，包括 `python3 scripts/check-source-inventory.py` 与 `lake build`；这不把全量 Lean 构建变成网页发布前置条件。沿用固定依赖和缓存，不升级 hgraph 或改解析器来迁就条目。临时探针和渲染输出放在许可的临时区域；不为常规写作引入额外 agent、Horizon 服务或审查门禁。

交付修改位置、来源关系和数学范围、对应/依赖的变化、实际检查及剩余边界。写作完成不等于证明完成，也不自动发布网站或提交远程。

来源与适配说明见 [sources.md](references/sources.md)。
