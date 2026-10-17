# 王老师要求的反例 PDF 与 Adams 图

2026-10-17 14:20 UTC，王老师在 `project-math-assistant` 回复反例消息：
“这个输出pdf，画相应的adams chart”。
原消息：<https://applink.feishu.cn/client/chat/open?openChatId=oc_0757f47818759dc02c05b8dd370aa649&position=1484>。

已按此意见制作 `Proposition-6.20-counterexample.pdf`（A4，4 页），14:31 UTC 作为该消息的回复发送并回读核验文件名与回复关联：
<https://applink.feishu.cn/client/chat/open?openChatId=oc_0757f47818759dc02c05b8dd370aa649&position=1486>。
另发说明并询问非提升源条件的精确改法：
<https://applink.feishu.cn/client/chat/open?openChatId=oc_0757f47818759dc02c05b8dd370aa649&position=1487>。
发送回执与最终时段消息保存在上级 `evidence/group-pdf-*.json` 和 `group-after-pdf-messages.json`。

截至该次回读，王老师尚未给出数学条件的进一步修改；不将 PDF 请求当成对候选修正的批准。完整第二段等价式继续保持未完成，生产公共接口未改。

## 内容与验证

- `classical-adams.pdf/png`：经典 mod-2 Adams 图，含 H(Z/16) 的 d4 及悬挂 HZ 的永久塔。
- `finite-ess.pdf/png`：固定 stem 1、weight 1 的有限商条带，按直和分量排横轴。彩色实线为非零 ESS 微分，灰虚线仅为早页 inessential 方程。
- `draw_charts.py` 与 `chart-checks.json`：逐项核验图中的源代表、目标和全部高源不定性。独立数学审查见 `../evidence/pdf-adams-chart-audit.md`。
- 最终 PDF 的四页均渲染为 `preview-1.png` 至 `preview-4.png` 并逐页目检；无截断、缺字或图例遮挡。XeLaTeX 日志无 missing character、overfull、undefined 或字体警告。
- PDF 明确区分纸面谱例子、有限算术 Lean 核验与当前固定 Lean 对象库尚未完成的完整谱形式化。
- 本轮 `python3 scripts/check-source-inventory.py` 通过（480 个项目文件、28 个消费/审计文件）；`lake build` 通过（3087 jobs）。构建仍回放已登记的上游 `sorry` 警告，本轮没有新增数学声明、待补责任或公理。

## 复现

从本目录运行 `python3 draw_charts.py`，再运行
`latexmk -xelatex -halt-on-error -interaction=nonstopmode Proposition-6.20-counterexample.tex`。
使用 make-pdf skill 的 XeLaTeX、中文字体与检查流程；为正确排版数学公式，直接维护 TeX 而未使用会转义公式的 Markdown 转换器。所需字体为 Latin Modern、Noto CJK 与 skill 自带的 JuliaMono。
