# 来源与本地适配

2026-10-20 为 Kervaire126Main 编写的项目级 Blueprint 写作 skill。

## 维护源

- 项目 [AGENTS.md](../../../../AGENTS.md) 与 [blueprint/README.md](../../../../blueprint/README.md)：模块边界、英文数学写作、来源措辞、原生 proof 面板和发布/验证分离。
- [Geometry](../../../../blueprint/chapters/Geometry.tex)及 [ProofTools](../../../../blueprint/chapters/ProofTools.tex)：本项目 `From`、`A … revision of`、证明与对应范围的实际用法。示例仅说明写法，数学内容以这些原文件为准。
- hgraph 使用项目 `requirements-blueprint.txt` 的固定版本；当前安装基线为 SII-MATH/hgraph 的 `c33cf070fb664360e8822fd2834b39d15ebd8d8e`。将来版本变动时核对实际项目规范，不依此文件升级工具链。

## 吸收的上游指导

[FrenzyMath/Archon-Horizon](https://github.com/frenzymath/Archon-Horizon/tree/50989563c6577356cd6fd5c916270d8a031fc2fb)，固定提交 `50989563c6577356cd6fd5c916270d8a031fc2fb`：

- `src/archon_horizon/pipeline/skills/operations/source-research/SKILL.md`：核对原始来源、具体版本及定位，区分来源结论、推论与 Lean 编码。
- 同目录 `references/catalog.md` 的 “Blueprint and source notes”：先遵守目标项目约定，让 Blueprint 解释数学及证明依赖；修改陈述时同步链接并保留缺口，实际检查构建结果。

这是上述指导的项目化改编，保留其 [Apache-2.0 LICENSE](../LICENSE)、[NOTICE](../NOTICE) 和 [第三方声明](../THIRD_PARTY_NOTICES.md)。不包含 Horizon 的 reference catalog API、上传下载服务、mission/roadmap、PR 验收或调度流程。

本地增加了 From / revision 的数学语义判别、原生 hgraph 写作方法及示例；详细项目约束引用维护源，不另建规范数据库。来源或语义不明确时联用项目已安装的 statement-alignment，普通写作不自动启动独立审查或定义重构。
