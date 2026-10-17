# AimPaper 内部结果公共接口补证记录

用户先要求公开先前审计中 11 项“有相关内部实现”的条目，随后明确要求同时补齐论文完整陈述的证明。复核发现，原分类只表示有相关内部步骤，并不表示已存在 11 条完整定理；本轮按实际成果分别记录，未把局部版本改名作为完整覆盖。

全部 57 项在本轮补证后的逐条核对现状见 [full-audit.md](full-audit.md) 和机器可读的 [full-audit.json](full-audit.json)。

基线提交：`93fbf1215b16c9630198370c6ce3cbcff9eb4912`。数学来源保持仓库固定的 `AimPaper/main.tex`，包括其中 2 完备、连通、有限型谱的全局约定。未改论文、既有公共声明、工具链或依赖锁。

## 已完成的公共结果

| 论文条目 | 公共实现 | 保留的数学内容 |
| --- | --- | --- |
| Proposition 2.10 | `KIP126.ProofTools.Paper.filtered_extension_noCrossingRange_iff` 等 | 主代表等价式及三个分款；任意滤过阿贝尔群版本适用于经典同伦群，另有同一 synthetic convergent map 的 E∞ 标签版本。crossing 保留所有非零目标，未偷换为仅 essential crossing。 |
| Proposition 4.2 | `lambda_rho_extension_collapse_finite`、`lambda_rho_extension_collapse_infinite` | 同一实际 λ、ρ 的正长度 essential 扩张排除、实际 E∞ 映射给出的 d₀ 方程、d₀ 无 crossing。 |
| Proposition 4.6 | `syntheticDeltaExtension_prop46_above_absolute` 等四个分支 | 两种经典微分长度范围，有限与绝对连接映射，固定源靶标签及实际扩张方程。 |
| Corollary 4.10 | `syntheticDeltaExtension_absolute`、`syntheticDeltaExtension_finite` 等 | 全部有效 λ 权重、a=n 零端点、源或有限靶超出 strip 的消失情形。 |
| Proposition 4.16 | `classical_crossing_iff_delta_crossing` | `2 ≤ page ≤ r` 全范围内，经典 crossing 与同一实际 δ 的 ESS crossing 的双向比较。 |
| Lemma 7.14 | `KIP126.Main.Paper.lemma_x1239` | 同一个 Q11 类及其 Q9 像、每个未截断 U 代表的两个修正关系、精确 h₀ 消灭关系。 |
| Lemma 7.20 | `KIP126.Main.Paper.lemma_nuext125` | 同一实际 Q9 中两个规定类的非零检测与规范化 ν 的精确作用方程；量词为存在代表。 |

公共入口为 `KIP126.ProofTools`、`KIP126.Main`。新增语言仅用于表述实际对象、标签、代表和 crossing；中间构造与辅助证明保持私有。条目状态与源码定位同时见 [coverage.json](coverage.json)。

## 未完成与暂缓项

- **Proposition 5.10**：一般长度需要同时除 λ 的源与映像比较。现有短长度转换不足以完成全范围。抽象滤过群方块说明某个中间推理条件不足，但没有识别为固定 synthetic 对象的反例。具体缺口见 [PROPOSITION-5-10-GAP.md](evidence/PROPOSITION-5-10-GAP.md)。没有新增局部公共版本代替全文。
- **Lemma 7.16**：已有每个 Toda 成员非零的论证；仍缺构造一个保持原 Toda 关系的 F11 成员及完整检测。剥离低滤过分量得到新代表不能自动保留原 bracket。已另证明右不定性所需的有限商 F10/F11 界，保持私有。
- **Corollary 7.18**：现有方程仅对 bracket 成员成立；推广到任意 Y 检测代表仍需证明 h₀ 消去代表差。不能取消已有方程中的额外 λ 因子，也不能把目标修正当作任意误差的吸收。完整缺口类型和证据见 [remaining-types](evidence/main-paper-section7-remaining-types.lean) 与 [remaining-evidence](evidence/main-paper-section7-remaining-evidence.txt)。
命题 6.20 的原印刷差集版本与授权修正版分别记录：前者不标已证；王老师明确要求“把差集条件先去掉”后，修正版已补齐并公开，见下节。

未使用最终 h₆² 定理或 `C3 ∧ C5` 的最终矛盾绕过上述局部证明，也未引入新的公理、`sorry` 或待补责任。尚未完成的项目继续标为未完成，不写入公共接口作为承诺。

## 6.20 授权修正版后续完成

王老师于 2026-10-17 15:06 UTC 明确要求“把差集条件先去掉”；用户要求依其意见继续补证，并将修改记入 memo。现已公开 `KIP126.ProofTools.Paper.finiteExtension_inessential_iff_shorter` 及实际源标签 `finiteExtensionCorrectionLabel`。修正版保持固定原目标 y、b=0、实际早商和经典早循环，删除源不属于晚循环的排除。前提仍包含有效早晚 witness、rEarlier≤rLater 和晚页 essential；同目标的ρ相容在证明内部导出，没有添加绑定前提。

短扩张可为 inessential，源类可为零，符合原文末式未要求短式 essential 的范围。n=e(f) 的空短源区间借晚页 essential、有效条带ρ单射及最短长度无交叉排除；正向 n>e(f) 可取 a=1。普通公共消费同时检查早循环输出、最短长度和私有封装。独立全 import-all 审查确认主定理闭包 822 个项目常量、38 项既有上游待补，无 Main 结论或 ProofTools 本地证明洞；未新增公理或责任。

11 项交付清单现为 7 项原范围完成、1 项授权修正版完成、3 项未完成；57 项原文审计仍将 6.20 记作 partial，并另列 authorized_revision complete，避免将修改后的命题冒称印刷原句已证。最终验证与依赖明细见 [本次记录](../interface-reviews/ProofTools/20261017-prop620-remove-difference/validation.json)、[独立核验](../interface-reviews/ProofTools/20261017-prop620-remove-difference/audit.md) 及 [memo](../../MEMO.md)。

## 飞书通知

用户明确要求安排 agent 向 `project math assistant` 群发送 6.20 的相关信息。实际群名为 `project-math-assistant`；数学摘要已通过群内既有机器人发送并回读验证：[群消息](https://applink.feishu.cn/client/chat/open?openChatId=oc_0757f47818759dc02c05b8dd370aa649&position=1474)。

内部报告、Lean 源码和日志附件外发被自动审批拒绝，理由为没有对具体附件的外发授权。因此没有发送附件；摘要发送成功。回执见 [feishu-message-receipt.json](evidence/feishu-message-receipt.json)。

## 验证与信任范围

以下数字是首轮七项交付时的验证快照；6.20 后续新增一条合法域下降接口的验证独立记录于 [wang-validation.json](../interface-reviews/ProofTools/20261017-paper-prop620-domain/wang-validation.json)。

实际执行普通入口消费、精确 API 捕获、完整 import-all 证明依赖捕获、源清单检查和默认 `lake build`；最终结果写入 [validation.json](validation.json)。旧接口的类型指纹、宇宙参数及公理依赖逐项比较，旧记录保留；`metadata/proof-obligations.json` 不重写。

最终检查通过：默认构建完成 3086 个任务；源清单覆盖 479 个项目文件与 28 个消费/审计文件。原有 299 项直接待补责任保持原文件字节不变。新增 33 个显式定义/定理全部核验实际传递依赖，未发现 Main/ProofTools 本地缺口或最终主定理循环；Lean 自动生成的支持声明另行列入接口锁，不算独立数学承诺。Main 公共根审计从原 17 项扩展至 21 项，保留全部原根和原 32 项 ProofTools 精确审计边界。

首轮完整构建因历史审计根清单未包含这四个已授权新增 Main 声明而失败；补充审计根后，所有原检查及新增根的相同检查均通过，没有修改待补注册或削减覆盖。完整依赖捕获也已覆盖当前全部数学源码，修复了旧临时工具遗漏模块所造成的不透明证明体漏载。

新增结果的局部证明完成，不等于固定模型、计算数据比较或文献输运的既有上游责任已完成。接口状态分别使用 `provided` 或 `provided-with-pending-dependencies`，不把成功构建当作所有数学证明无缺口的证据。


## 6.20 最新二择修正版（2026-10-18）

已形式化并公开 `FiniteExtensionNonliftableShortTo` 与 `finiteExtension_nonliftableShort_or_lateCrossing`：同一晚页扩张本质、早页扩张非本质，推出保持原 y、b=0 的差集短扩张，或同一晚页 normalized synthetic ESS 的 crossing。去差集 iff 和合法页下降继续保留。此处未将 crossing 等同定义 5.9 的经典有限页条件，也未推出推论 6.23 的升页存在性。原印刷 general-b/y′ 版本仍区别记录。验证及完整传递依赖见 [本轮记录](../interface-reviews/ProofTools/20261018-prop620-crossing-dichotomy/validation.json)。
