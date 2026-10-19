---
issue_id: ProofTools-20261018-mh-finite-level-target
title: MH 形式化目标：强有限商、双输入层数与共同代表
summary: "用户已明确授权撤销两个旧 GL/MH theorem，保留 law 定义、反例证据及已证 AtLevel；已实施源码删除与消费测试迁移，精确接口锁与两模块审计已通过；完整检查按用户后续要求暂缓。"
responsibility_module: ProofTools
targets:
  - KIP126.ProofTools.GeneralizedMahowaldLaw
  - KIP126.ProofTools.Standard.generalizedMahowald
  - KIP126.ProofTools.Standard.FiniteMahowaldAtLevelStatement
  - KIP126.ProofTools.Standard.generalizedMahowaldAtLevel
baseline_commit: 1dc13a1973bc0f69c14e39f197372c30a350d4e8
reporter_agent: /root/mh_interface_review
independent_of_discoverer_and_implementer: true
evidence_level: "原完成快照的独立证明审查保留；合并远程 75 项补证后，完整 lake build（3573 jobs）、72 项 Python 测试、源码与接口检查、原生 Blueprint 导出和三个核心根的实际 kernel 依赖复核均通过。当前全仓 237 项既有待补，row／cone 47 项上游、完整 MH 55 项上游，未新增公理或证明洞。"
status: approved-interface-change
human_decision: "2026-10-18 用户明确要求：“就按这个方案推进，先把完整的 Lean 陈述和实际 no-crossing 条件定下来，写出完整的陈述，替换掉现在 blueprint prooftools 章节里里无法证明的版本，再完成形式化证明。”授权范围为本提案的 ProofTools MH 方案、完整类型与实际 no-crossing、相应 Blueprint 替换及补证；不推定为可新增公理、改变其他数学模块公共接口或增加上游待补责任。
2026-10-19 本对话用户明确授权：“那就删掉这两个旧定理，保留 law 定义、反例证据和已证的 AtLevel 版本，同步接口锁、待补清单和测试，再跑完整检查。”授权仅撤销 Standard.generalizedLeibniz 与 Standard.generalizedMahowald 两个旧 theorem；保留 law 定义、反例证据、AtLevel 版本及三项其他论文责任。"
---

# 建议采用的目标

## 合并远程 main 的验证（2026-10-19）

本次合并保留远程 `2e856875` 的接口工作区迁移、废弃错误 GL／MH 蓝图节点清理，以及 75 项既有责任的补证。当前接口清单位于 `interface/baselines/`，提案位于 `interface/proposals/`；当前全仓许可待补为 **237** 项，逐项采用该远程基线，未恢复已完成的责任，也未增加许可。新的完整带层 MH 条目保留；旧一般 law 的冻结责任与反例记录仍保留。

本任务的 MH 数学源码与已验证提交 `20dcf765` 完全一致；新增的商行、同一余纤维同构的两箭头和无 `hRows` 的完整 MH 均未改型或减弱。下文的 312 项总数、50／54 项根闭包及 3570 jobs／64 tests 是合并前独立完成快照，不作为合并后待补计数。合并结果的完整 `lake build` 通过 **3573 jobs**，**72 项 Python 测试**、549 项目文件／35 消费者和审计文件的源码清单、20 份提案校验及 Blueprint 原生导出均通过。

协调者另以所有上游及 ProofTools 实际源码的 `import all` 捕获三个根的完整 kernel 证明依赖，共核对 2014 个实际项目节点。合并后 row 根及 same-esusp cone 根各继承 **47** 项当前登记上游责任，完整 MH 根继承 **55** 项；增加的传递边来自远程补证后的真实证明体，未增加任何许可。三根均无新增公理、直接或 synthetic 证明洞、循环、缺失、下游依赖及旧 MH／GL／争议 unshifted 输入，所有实际待补的类型和证明体指纹与当前 237 项清单一致，且没有 ProofTools 待补依赖。

## MH 独立完成快照与验证边界（2026-10-19，合并远程补证之前）

2026-10-18 用户已在本提案交付后明确批准按方案推进，要求定下完整 Lean 陈述、实际 no-crossing，替换 ProofTools Blueprint 的旧版本并完成证明。下文中“尚未批准”描述的是研究交付时的历史边界，当前以本段及文件头的人审记录为准；不再为同一 ProofTools 方案重复请求确认。完整证明、接口实际差异、检查和任何新增上游接口疑点按实施结果续写，不能把方向批准写成已经完成证明。

完整 public theorem **现已实现**：`KIP126.ProofTools.Standard.generalizedMahowaldAtLevel`，实际定义于 `KIP126/ProofTools/GeneralizedMahowald/FiniteLevelAssembly.lean:163`。其完整入口为：

```lean
public theorem generalizedMahowaldAtLevel
    (T : TriangleData model.auxiliary)
    (he : (normalizedExponent model.classicalTower T.f : ℤ) +
      normalizedExponent model.classicalTower T.g +
      normalizedExponent model.classicalTower T.h = 1) :
    FiniteMahowaldAtLevelStatement T he
```

这里的固定 `model`、完整 `FiniteMahowaldAtLevelStatement`、实际 no-crossing 以及全部原指定标签保持原类型；不是只新增一个 `Prop` 定义。证明主体直接展开原目标，同步三个实际 ESS 输入为同一 `a,b`，调用实际有限商行产生**同一个 c**，保留两条 signed 像方程、全部输入与输出检测、原 x 的更高 cycle 及原 y 的强商 `LevelFiniteExtension`。**公开定理和内部完整装配均不再有 hRows 前提**，没有把实际商行或 MH 输出作为新字段转交给调用者。

这一步使用已获跨模块授权并已证的 `KIP126.Literature.Standard.normalized_finite_quotient_horizontal_row`，实际定义于 `KIP126/Literature/Standard/FiniteQuotientNormalized.lean:334`。该 theorem 保同一个实际 quotient inclusion 的 `esusp`，并证明全部选定 quotient maps 与字面负号构成 distinguished 行；同文件私有 cone 同构对**相同 esusp** 同时证明 inclusion 和 projection 两条结构箭头。当前已跨过早期“任意 good filling 尚未识别为指定地图”的阶段。详细接口及授权范围继续维护在 [Literature 提案](../../Literature/20261018-mh-finite-quotient-horizontal-row/report.md)。

本段由 `/root/mh_api_audit` 回写执行状态，依据当前源码和协调者交付的证明/独审结果；该回写者曾实现三八面体基础的两条私有引理，不以本段冒充自己对该实现的独立完整证明审查。原独立提案、人审原话与授权范围均保留。当前源码 SHA-256：

| 当前实现源 | SHA-256 |
| --- | --- |
| `KIP126/ProofTools/GeneralizedMahowald/FiniteLevelAssembly.lean` | `12fd9525b85a39171839b2666da5b6680fbb6aa1733051f370dc4cfc13c3e2b5` |
| `KIP126/Literature/Standard/FiniteQuotientNormalized.lean` | `3b58d08ea75a73abc5137d6ccb84b22091bf5cfdaa9d6a803642e153daec5eef` |

最终统一检查已完成：`lake build` 通过 **3570 jobs**，包括八模块接口锁、普通公共消费、架构及全部内部信任检查；源码清单覆盖 **549** 个项目文件和 **35** 个消费者／审计文件；全部 **64** 项 Python 测试及 **20** 份接口提案校验通过，Blueprint 原生同步和导出通过（406 个数学条目）。当前数学正文与绑定分别指向 Literature 的实际公开 row 和 ProofTools 的完整公开 MH，不以命题定义或私有辅助步骤冒充定理。

最终全仓 kernel 捕获覆盖 **14077** 项声明。全体 **312** 项原登记待补的名称、归属、类型及证明体指纹逐项保持原样，无新增公理、直接证明洞或 synthetic sorry。实际 row 及 same-esusp cone 根各继承 **50** 项原登记上游责任，完整 MH 根继承 **54** 项，均无 ProofTools 待补、旧 MH／GL、争议 normalized 结果或下游依赖；独立审查与协调者完整捕获相符。原完整 `FiniteMahowaldAtLevelStatement` 源文件逐字未改，全部既有公开类型、宇宙参数和公理依赖保持原样；工具链和依赖锁未变。

Blueprint 的完整 MH 条目现实际绑定 public `generalizedMahowaldAtLevel`，不以 `Prop` 定义或私有局部步骤充当完整 theorem。导出、接口锁、既有洞清单和 Blueprint 的最终一致同步由协调者统一检查。旧 `GeneralizedMahowaldLaw`、`Standard.generalizedMahowald` 与其历史待补及反例记录没有被本次新 theorem 改成已补完；本轮也不把整个项目、全部历史 SS 计算、一般普通 Adams 方框或无条件经典恢复标记为无洞或已认证。

获批的完整目标、实际 no-crossing、Literature 固定行及无 hRows 的完整公共 MH 已实现并完成上述全量验证，状态据此记为 `approved-implemented-and-validated-before-publication`；原批准范围和未完成上游边界保持不变。

最终实施状态由协调者 `/root` 据实际构建、捕获、独审及导出回写；原独立报告和全部人审原文保持原样。三个伴生导出是 Lean 原生生成项：`CategoryTheory.Pretriangulated.invRotCompRot.eq_1` 实际归属 Literature 的 `FiniteQuotientNormalized`，`KIP126.Literature.normalizedTriangle.eq_1` 及 `KIP126.AdamsSynthetic.Standard.shift_page.congr_simp` 实际归属 ProofTools 的 `FiniteLevelAssembly`。没有为它们手写额外数学接口或 Blueprint 绑定。最终锁完整包含真实导出：Literature 790 项，ProofTools 212 项。


最终接口锁 SHA-256（文件头所列旧哈希仍为原提案审查基线）：

| 当前接口锁 | SHA-256 |
| --- | --- |
| `metadata/literature-api.json` | `885823085c33639c29155f9593f13db3e9f26f3af43e640f81c95cff6127a89e` |
| `metadata/proof-tools-api.json` | `872918c18d6c4615d12e8af35eb7cce8946e26da259db920c75597fc6d86c316` |

## 历史实施阶段记录（最终固定行与公共 MH 完成之前）

以下保留早期 `Prop` 定义、hRows 条件装配及对应构建快照，明确其证据只覆盖当时源码。“仍缺固定行”“无条件 MH 尚未交付”等句子均是历史进度，当前状态以上节为准。

已实施的完整目标定义为 `KIP126.ProofTools.Standard.FiniteMahowaldAtLevelStatement`，源文件 `KIP126/ProofTools/GeneralizedMahowald/FiniteLevelStatement.lean`。它保留所有双层参数、指定经典标签、三个实际 ESS 输入、full-triangle essential no-crossing、同一代表及 signed 方程和最终强商结论。四个移位源采用实际 `levelFiniteSourceLabel`，没有重新引入未校准的任意正移位 νE₂ 标签；比较的 ρ 方框由已证的逐球面有限 no-return 推出，不额外作为前提。普通导入和完整类型检查已通过。这个 `Prop` 定义没有证明其真值。

已完成的证明在 `ActualNoCrossing.lean`、`FiniteLevelLabels.lean`、`FiniteComparison.lean`、`ClassicalLift.lean`；均未添加 `sorry` 或公理，也未调用旧一般 MH/GL。实际 λ 商的第一条像与同一代表第二像的某个 λ 分解见 `FiniteMay.lean`，尚未将该分解的原像识别为指定 $b$。数学上它与原目标不同，不作为完整 May 结论交付。条件性的完整 transport 已在归档研究文件通过 Lean，但它仍需要结构数据的实际固定生产者，不能充作标准模型证明。

`FiniteLevelInputs.lean` 已将三个实际 ESS 输入同步为具有五条指定检测和严格 $\delta a=\Sigma Fg(b)$ 的同一 $a,b$，并证明完整目标的顶端消失窗口。`FiniteLambdaSurjectivity.lean` 已从既有有限 $E_\infty$ 坐标满射、实际收敛与有限商顶端消失证明实际 $\lambda^A$ 在窗口 $A\le m+u-w$ 上的严格 $F^u$ 满射及其移位版本。这一步不使用完备性；也不能单独保证调整 $b$ 后同时保持 $g(b)$，因此不算第二像方程已经完成。

`FiniteMay3x3.lean` 随后交付较小的纯三角图路线：TR3/TR4 先构造第二像严格正确、第一像差为固定 $b\circ z$ 的同一代表，再用 normalized finite no-return 消去差；`normalized_finite_may_of_horizontal_row` 得到两条严格像方程。其明确条件是固定水平行 `Triangle.mk (Q_N G) (Q_N h) kN` 为 distinguished；`kN` 可以直接取带字面负号的目标，无需假设商函子加性。这是条件定理，不是当前模型已交付该水平行正合性。上游仅需生产一个 canonical、保包含的悬挂比较及相应正合水平行，任意其他比较在球面上由 `FiniteComparison.lean` 处理；不要求所有选择全局正合，也不必补完整张量相容结构。上述独立提案已收录这一较小备选。

`FiniteLevelConclusion.lean` 已证明实际检测对的反悬挂、固有源标签反射到原类的更高 cycle，以及精确悬挂 source/image 检测对推出完整强商 `LevelFiniteExtension`，包括保留原指定 $y$ 的算术重标。`FiniteLevelSourceLabel.lean` 从同一 $c$ 的实际 ρ 像反射完整高层源检测；`FiniteLevelOutputLabels.lean` 把同一 $b$ 的 $j$ 层标签严格送到 $A+j$ 层，保留普通悬挂和实际负号，不要求 $y$ 永久。

完整 `FiniteLevelAssembly.lean` 的私有 `finite_mahowald_at_level_of_horizontal_rows` 已通过 Lean 和生产目标构建，直接证明 `hRows → Standard.FiniteMahowaldAtLevelStatement T he`，不以另一个简化或通用命题代替公开目标。它完整保留同一 $a,b,c$、五条输入检测、严格 δ 等式、两条带符号像方程、两条原标签的输出检测、原 $x$ 的完整 cycle 和原指定 $y$ 的强商扩张。私有 `NormalizedFiniteQuotientHorizontalRows` 只要求固定商行 distinguished 及存在一个保包含的悬挂比较，不包含任何 MH 输出；其固定模型真值未被定义或证明。

Blueprint 的原零层 MH theorem 和语义陈述已由完整带层目标取代；完整 theorem 保留未证状态且不绑定私有组件，原文唯一仍在 AimPaper 及 corrections 页。公开旧 law 与原有待补继续保留为历史接口，未被本次新定义冒充补完。新公开导出只有实际 no-crossing、共同源定理、完整目标定义和两个实际提升/目标永久性定理；辅助结果保持私有。

独立核验发现 May 张量图到固定 λ 商的结构识别没有由现有接口交付，较强充分方案见 `interface-proposals/AdamsSynthetic/20261018-mh-lambda-tensor-coherence/report.md`。纯三角图路线已给出更小的下一步：[Literature 水平行提案](../../Literature/20261018-mh-finite-quotient-horizontal-row/report.md) 请求一个完整内联的固定商正合行 theorem，不依赖 ProofTools 私有谓词，也不需要完整张量比较结构。其 normalized triangle 语言属于 Literature，不能反向塞入 AdamsSynthetic。用户已于 2026-10-19 明确批准该最小跨模块方案与接回 ProofTools，禁止新增公理或证明洞；决定原话及精确范围维护于 Literature 提案。新增的 Literature 私有构造已给任意实际对象的保包含悬挂比较，并从实际 λ 余纤维三角的产品比较证明固定商函子的加性、负号与有限双积保持及标准分裂三角保持；尚未把八面体的良好商行识别为全部指定地图；没有以历史实现中的额外 stable cofiber 公理绕过这一证明。无条件公共 MH、一般普通 Adams 方框解码、经典 extension 恢复和实际 SS 证书不能因此称作全部完成。

检查：最终完整 `lake build` 已通过（3549 jobs），覆盖完整条件装配及全部源/目标标签、精确商长与悬挂运输；ProofTools 独立审计核查 3887 项声明，确认仍仅有原来的五项登记待补，没有项目公理。最终全仓信任捕获覆盖 13520 项项目声明；重新冻结核验未改变任何现有基线，全仓仍为 312 项原登记责任。普通公共捕获与 209 项 ProofTools 导出逐项匹配。源清单核验覆盖 531 项目文件和 35 消费/审计文件；Blueprint 原生导出、34 项相关测试和 20 份接口提案校验通过。完整条件根另经直接 import all 全源码的独立依赖核验：42 项传递上游待补全部已登记，无本地证明洞或旧 MH/GL；这些上游责任并未因此完成。原待补清单与其他模块接口锁未修改；原生页面仍只将 `Prop` 定义绑定为定义，不把私有条件证明冒充无条件公共 MH theorem。

2026-10-19 续检：`lake build` 通过（3551 jobs），源清单覆盖 533 项目文件和 35 消费/审计文件；Literature 信任审计覆盖 1468 项声明，仍为原登记 130 项待补，ProofTools 仍为原登记五项。最终全仓信任捕获覆盖 13541 项项目声明；两份新增私有源没有本地证明洞或项目公理，30 项传递上游待补全部已登记，无下游证明依赖。Blueprint 34 项测试及 20 份提案校验通过。新增构造均私有，因此本轮所有公共接口锁和 312 项待补基线保持不变。signed row 与无条件 MH 仍未交付，构建通过不替代这两个数学结论。

下文保留获准实施前的研究记录及当时的提案措辞；其中“未定稿”“尚未 elaboration”“尚未批准”等状态以本节的当前实施结果和 Literature 提案人审记录为准。

2026-10-18。用户本次要求查阅 project-math-assistant 群和仓库研究，确定应形式化的 MH 版本。本报告由未参与本候选发现或实现的独立报告员复核；协调者研究草稿及其已核来源保留，数学与源码核验范围见末节。不把“基本确定陈述”解释为已批准增删公开声明。

建议确定数学目标为：**保留强有限商的双输入层 MH，输出同一个实际代表及其两条像方程；实际 no-crossing 到共同代表的同步定理是需要另外完成的证明部分。** 普通 Adams 输出与经典 extension 输出分别给有完整前提的推论。不要继续把有反例的旧 exact-source 零层结论作为一般证明目标。

这是可审阅的数学规格；不是已经 elaboration 通过的新 Lean 类型。新增公开名称、一般 law 的替代方式、旧接口的最终处置及相应锁文件改动仍需明确授权。现阶段不需要暂停保持接口不变的局部补证。

相对 AimPaper 的问题、反例及状态唯一维护在根目录 `corrections.yaml` 的 `mahowald` 条目；原文对应 `paper:6.12`。本报告维护候选接口及其授权边界，不另立论文修正记录。

## 请求人类决定的具体问题

本轮可决定的范围是：是否采用下述“实际 May 共同代表 → 双输入层强有限商 MH → 普通 Adams 方框推论／带障碍消除条件的经典推论”的数学目标。建议先交付 i=j=0 的强商核心，再扩展双输入层。完整公共 Lean 类型、实际 no-crossing 谓词和旧 law 的替代方式尚未定稿，不能将本次数学方向的认可视为这些冻结接口的变更授权。当前没有必须先获得批准才能继续的私有证明研究。

## 来源与版本核对

1. [王老师 4 月 24 日第六节 TeX 附件](https://applink.feishu.cn/client/chat/open?openChatId=oc_0757f47818759dc02c05b8dd370aa649&position=764)：本次通过原消息重新下载，SHA-256 为 `7742cafac208e2a183667139bdbda028963ad6c2dccf920dbe974322f35edd5d`，与仓库历史研究所用附件相同。它保留第零层 h/g 输入，输出加入 level，但目标仍留有 `mod someting` 占位；证明末尾删掉了除 λ，不能把它说成已有精确目标商的最终定理。
2. [10 月 16 日明确要求加入 extension 参数](https://applink.feishu.cn/client/chat/open?openChatId=oc_0757f47818759dc02c05b8dd370aa649&position=1457)，并在 1459—1460 明确指向上述 TeX。随后要求先证特例，再查 SS 实际使用版本（1463—1464）。这些消息不能被扩大解释为任意公共接口变更授权。
3. [10 月 16 日 level 修订复核](https://applink.feishu.cn/client/chat/open?openChatId=oc_0757f47818759dc02c05b8dd370aa649&position=1462)与[全量 SS 调研](https://applink.feishu.cn/client/chat/open?openChatId=oc_0757f47818759dc02c05b8dd370aa649&position=1467)：前者区分 4/24 核心与 4/25 共同正层字面推广，后者要求强商、递归 source coset、代表同步、cutoff 和经典提升。
4. [10 月 17 日《广义MH与论文计算认证研究报告》](https://applink.feishu.cn/client/chat/open?openChatId=oc_0757f47818759dc02c05b8dd370aa649&position=1498)：本次实际下载并读取全部 13 页正文；第 4 节给出下面的双输入层参数，第 5、6 节分别写经典提升和普通 Adams 方框，第 11 节建议“主定理加两个推论”。它是研究建议，尚无已批准或已实现完整候选的消息依据。
5. 仓库历史研究：`local-history/Sources/Reviews/SS-all-results-2026-10-16/{wang-coverage,recursive-mh2,final-review}.txt`。群 PDF 后于这些材料；不能仅按旧档案得出“只补定义域仍可能够”的结论。
6. [10 月 18 日 GL 与有限除 λ 的公开结果](https://applink.feishu.cn/client/chat/open?openChatId=oc_0757f47818759dc02c05b8dd370aa649&position=1516)已由本次源码复查确认。它提供可复用工具，但没有自动证明新的 MH 或全部机器调用正确。

[原群消息摘录](evidence/group-evidence.json)保留来源链接、发送者和原始时间字段；未猜测 CLI 时间字段的时区。原 PDF、TeX、完整读取消息及历史独立数学笔记归档到 `local-history/reports/mh-statement-20261018/sources/`。[来源指纹](evidence/source-sha256.json)记录本次实际读取版本。

## 旧接口与固定对象

旧 law 的完整签名见[原签名摘录](evidence/original-law.txt)。它具有 `u v w`、`C`、`Syn`、稳定/合成范畴与两个 functorial cofiber 实例以及同一个 `D : Model C Syn`。公开证明入口固定使用 `Standard.model` 和 `T : TriangleData model.auxiliary`；这两层的泛型范围不能混同。

旧 law 要求同一 T 的指数和为 1、`NormalizedTriangleCompatible`、n₁≥1、m₁,l₁≥0，四个指定标签的 cycle/permanence，指定 suspendedX 与 x 的实际 `DesuspendsClass`，h 有限扩张、Z 上的 d_r、h 或 d_r 的旧 no-crossing，以及 g 有限扩张；然后断言原始 x 的更高 cycle 资格和零层 f 有限扩张至某 y′，y′−y∈B_r′。全部次数及量词保留于摘录，没有将 x 或 y 改为“任选同次数类”。

新候选首先也应固定当前模型、同一个 T、同一实际 normalized maps、商塔、悬挂/weight 比较和收敛；`ClassicalObject` 的现有闭包不含任意谱、任意直和或 HZ。此规格不要求扩大该闭包，更不授权改 AdamsSynthetic 或 Literature。一般几何叙述可用于理解，但不冒称当前 Lean 模型已表达 SS 中的全部 CW 谱。

## 第一层：代表级有限 May 定理

把归一化移位吸收到对象中，固定相容实际三角 X→Y→Z→ΣX 及其有限商体系，写 Q_D W=νW/λ^D。给 A,B>0，N=A+B，使用实际三角

\[
\Sigma^{0,-A}Q_B W\xrightarrow{\lambda^A}Q_N W
\xrightarrow\rho Q_A W\xrightarrow{\delta_{A,B}}\Sigma^{1,-A}Q_B W.
\]

对任意 p,w∈ℤ，取实际 a∈π_(p+1,w)Q_A Z、b∈π_(p,w+A)Q_B Y。若 δ(a)=g_B(b)，则要求构造**同一个** c∈π_(p,w)Q_N X，使

\[
\rho(c)=h_A(a),\qquad f_N(c)=-\lambda^A b.
\]

第一式用 π_(p+1,w)(ΣQ_A X)≅π_(p,w)Q_A X；δ 将 a 送入 π_(p,w+A)Q_B Z，λ^A 将 b 送入 π_(p,w)Q_N Y。所有式子均通过同一组固定悬挂、商和张量比较解释。负号来自当前 `GeneralizedMahowald/Geometry.lean` 的 `may_tensor_common_lift`；不能因 E₂ 系数为 F₂ 就在实际同伦群等式中删号。该文件已证明张量形式的两式；向指定实际商映射的比较仍需核查和完成，不能将局部张量引理称作完整 quotient 定理。

## 第二层：双输入层标签定理

固定 n,m,l,s,t∈Z，e_f,e_g,e_h 为同一 T 的归一化指数，非负且和为 1。置

\[
n_1=n-e_f\ge1,\quad m_1=m-e_g\ge0,\quad k=l-e_h\ge0,
\quad r=n+m+l=n_1+m_1+k+1.
\]

取 i,j≥0 且 j<n₁，定义

\[
A=n_1+k+i-j,\quad B=m_1+j+1,\quad N=A+B=r+i,
\qquad K=i+k,\quad J=A+j=n_1+k+i,\quad Q=N-K=r-k.
\]

可见范围必须保留：0≤i,K<A，0≤j<B，0≤J<N。j<n₁ 是本版反射源首项的充分条件，不宣称最小；若去掉它，需要另给真实源检测证书。

给定标签

\[
\bar x\in Z_{r-1}^{s,t}(Z),\quad d_r\bar x=\bar y,
\quad\bar y\in Z_\infty^{s+r,t+r-1}(Z),
\]
\[
x\in Z_{n_1-j}^{s+l,t+l-1}(X),\qquad
y\in Z_{m_1+1}^{s+l+n,t+l+n-1}(Y).
\]

完整的代表前提是存在同一个 a∈π_(t−s,t−i)Q_A Z 和同一个 b∈π_(t−s−1,t+l+n−1−j)Q_B Y，使以下检测同时成立：

| 实际类 | 指定标签 |
| --- | --- |
| a | λ^i x̄ |
| h_A(a) | λ^K x |
| δ_(A,B)(a) | λ^(B−1) ȳ |
| b | λ^j y |
| g_B(b) | λ^(B−1) ȳ |

h 的目标标签须通过同一模型的实际悬挂比较与 x 关联；原 `suspendedX` 的证明责任不得以任意 E₂ 等价替换。上述三条关于 a 的检测不得使用三个独立选择的代表。

这里“检测”指实际过滤至少为指定级，且在该关联分次具有指定标签；零标签表示过滤至少再高一层。Q_D 第 a 层使用 Z_(D−a)/B_(a+1)，并非原始 E₂ 向量的相等。两个 ȳ 像位于 Q_B 的最高可见层，顶层唯一性给实际等式 δ(a)=g_B(b)。这里还使用实际有限商的 homotopy separation 与 E∞ 可见窗口比较，使下一过滤层为零；不能只由两个 associated-graded 类相等推出任意滤过群中的实际相等。现有 `Filtration.lean` 的 `finite_top_detection_unique` 经 `finite_high_filtration_zero` 明确调用此上游 separation。

结论要求交付 c∈π_(t−s−1,t+e_h−1−i)Q_N X 及第一层的两式，c 检测 λ^K x，f_N(c) 检测 λ^J y，并推出

\[
x\in Z_Q,\qquad d_n^{\hat f_N}(\lambda^Kx)=[\lambda^Jy].
\]

源标签按 Z_Q/B_(K+1) 解释，目标按

\[
\bigl(Z_{m_1+1}/B_{J+1}\bigr)
\big/\{\text{长度小于 }n\text{ 的实际 }\hat f_N\text{-ESS 像}\}
\]

解释。现有公开 `Standard.LevelFiniteExtension` 的实际商为 `page+level−1`，可复用来表达标签关系：

```lean
-- 数学候选的结论片段；未作为新声明 elaboration，不是完整候选签名。
Standard.LevelFiniteExtension T.X T.Y T.f
  (Q+1).toNat K.toNat n (s+l) (t+l-1) x y
```

其中 page=Q+1≥2、level=K≥0，故商长为 Q+K=N；目标层 K+n−e_f=J；长度上界 n≤Q−1+e_f 等价于 m₁≥0。无需为了这个标签结论再造一个平行公开谓词。此片段还不携带实际 c 及两式，不能替代代表输出或同步定理。

目标允许为零或 inessential；y≠0 不保证其 ESS 页类非零。y=0 不意味着 f_N(c)=0。保留 c 与其实际像检测，不能仅返回这个末端商等式。

指标核对：A−K=n₁−j>0，N−K=Q，N−J=m₁+1，J−K=n₁；δ 的目标层 i+r−A−1=B−1。normalized f 把 c 的 weight 变为 t−i−e_g，等于 b 的 weight 减 A。源 cycle 由实际 Q_N 检测及 K<A 的投影反射取得；证明不取消 λ^K。该反射须同时控制低于 K 的层：λ^A 核项由实际有限商三角及底过滤界不能改变 K<A 的首项；`eInfinity_rho_finite` 与有限标签比较负责把同一代表的检测反射回来。这是待完成固定商比较的一部分，不是单靠算术等式已交付的 Lean 证明。

### 应首先交付的零输入层推论

i=j=0 给 A=n₁+k、B=m₁+1、N=r、K=k、J=r′−1=n₁+k，Q=n+m+e_h。因此核心输出是

\[
x\in Z_{n+m+e_h},\qquad
d_n^{\hat f_r}(\lambda^kx)=[\lambda^{r'-1}y]
\quad\text{于强商 }Q_r.
\]

这比先投影到 Q_Q 更能保留目标；当 k≥m₁+1，Q_Q 中目标已经不可见。不得用弱投影关系认证指定非零 y。

### 实际 no-crossing 的独立责任

以上代表版给出精确充分前提，没有假装两个孤立 ESS 式子自动同步。要交付通常可用的 MH theorem，还应证明：同一实际 Q_A 中 h 边或 δ 边适当的 no-crossing，连同各边真实 extension witnesses，足以构造上述同一个 a。无 crossing 的量化须在该实际 map、stem、weight 和所有高过滤修正上；原 `FiniteNoCrossing` 的经典窗口不得未经证明搬用。g 边在 Q_B 提供 b。

可先研究较强但明确的充分条件：若两个候选 a_h、a_δ 同源首项，且 h_A 把全部 F^(s+1) 修正送入 h 目标的再上一层，则选 a_δ 保持 h 标签；对 δ 边同理。较弱的 essential no-crossing 形式需要实际过滤修正证明，**此次未确定其最小条件或完整 Lean 公共谓词签名**。

## 两个输出推论与实际使用范围

**普通 Adams 输出。** 两次有限求像应放进同一个 λ 商连接方框，使用同一实际 α 与 β=f_Aα，保留 δ_Yβ=f_Bδ_Xα 的低项消失和首项检测。源可换成 x+Z_b，d_b 目标可换成 z+B_(b−1)；这些 coset 允许性须由方框证明支持。普通页解码、源存活和 cutoff 都是独立 ProofTools 责任。现有 `generalizedLeibnizAtLevel` 的底边使用完整 ν 输入，不直接替代一般有限—有限方框。

**经典 extension 输出。** 固定完整到有限的 p:G→G_N、同一 normalized f 对应的 φ_N、有限代表 c₀，源首项 ξ、目标首项 η 位于过滤 s₀、T。置

\[
V=F^{s_0+1}G_N\cap\varphi_N^{-1}(F^{T+1}H_N),
\qquad\mathcal A_\eta=c_0+V.
\]

保留目标的精确提升条件为 A_η∩p(F^s₀G)≠∅；在相关源过滤反射下，等价于连接障碍 ∂c₀∈∂V。不必要求原选 c₀ 自己提升，但不能只由源标签永久推出这个仿射族里有完整 lift。目标过滤反射、固定标签比较和经典恢复也须保留。在目标可见层 J<N，若已取得完整实际像，则固定比较给出 Z∞/B_(J+1)→Z_(N−J)/B_(J+1) 的单射；若指定 y 与永久标签只差 B_(J+1)，因 B_(J+1)⊆Z∞，才可推出这个指定 y 永久。经典 λ-localization 后仍须按 Z∞/B∞ 与经典 ESS 短像商解读，有限非零标签可能消失，不能自动得 essential 非零 extension。仅短有限 ESS 商中的目标相等不足以推出指定原始 y 永久；要认证 SynCsIn，须保留其实际目标首项。上述障碍准则及足够的全修正替换条件是后续应证引理，非此次已完成结果。

**除 λ 工具。** 现有 `finiteLambdaDivision` 在额外实际 λ-kernel crossing 条件下保持源、像方程和所需滤过；其小层源标签由构造产生，没有预设为旧 law 的任意指定 x，目标最终层的 λ 核不定性仍存在。故不能直接据它恢复旧 MH 的 exact-source/exact-target 结论。

**Main 与计算责任。** Main 的现有零层 ν-cofiber 实例不需更换：其 n=3、m=l=0、e_f=1、e_g=e_h=0，m₁=k=0；当前一般私有零层证明还要求 Y=sphere，不应称作任意对象的零层定理已经交付。SS 递归代表同步、搜索对全部合法线性组合的完备性、跨商 stretching、SynCs 提升和具体历史依赖闭包仍未认证。研究报告中的历史计数和 GL2412568 的三个合法修正属历史核验结果，本次未重新运行；不能宣布全部 SS 已可靠，也未得到某条官方实际数学结论错误的证据。

## 实施差异、责任与授权边界

| 项目 | 本次结果与后续方案 |
| --- | --- |
| 数学候选 | 双层强商及代表输出已具体写出；实际 no-crossing 同步另证 |
| 原 law/证明入口 | 本次不改名称、类型、前提、语义、导出或待补登记；其既有待补保留 |
| 将来公开出口 | 可优先新增代表级有限 MH 与标签推论；准确 Lean 签名、名称和锁改动须送审，不能静默替换旧 law |
| ProofTools | 实际商比较、共同代表、标签反射、同步与两个输出桥梁；仅用允许的 E₂ 输入和上游公共接口 |
| AdamsSynthetic/Literature | 固定对象、商、悬挂、收敛、May 与比较的现有责任继续在上游；本次不修改或转移 |
| AdamsCalculations | 对具体计算输入及其证书的消费仍属该层；不由 ProofTools 接手后续 Adams 计算 |
| Main | 现有安全数值实例及其禁用旧一般 GL/MH 依赖边界保留 |
| Blueprint | 新修正版应在证明/公开接口落实后对应本模块的公开绑定；此次不把私有组件绑定成完整新定理 |

批准范围尚为空。群中对 level GL 的公开化和除 λ 条件的意见，不能视为已批准 MH 全部新出口、删除旧接口或增加证明洞。本次也不请求修改工具链、依赖、其他模块或推送发布。

## 独立证据、复现与依赖审计

独立报告员 `/root/mh_interface_review` 于 2026-10-18 阅读了本提案原草稿、指定 protocol/template、原 law、实际 `normalizedTriangle`、`Geometry.lean` 的 May 两式、`Filtration.lean`、实际反证的三个组成文件、level GL 的完整公开类型、有限到完整比较、weighted reverse boundary，以及 10 月 17 日研究全文和历史独立笔记；未参与候选发现或实现。原群消息与 TeX 下载由协调者完成，本次独立审查利用其留存原件与来源，不冒称另一次群下载。记录与数学审查可独立区分。

[独立证据与复现](evidence/independent-review.md)列出核对路径、真实前提表、一般指标推导、最小算术例、重现命令和实际结果。[有限算术脚本](evidence/check-indices.txt)仅核对指标及 weight，不能替代共同代表或固定模型证明。实际输出见[复现日志](evidence/check-indices.log)。本轮未发现满足全部代表前提却违反强商结论的反例；这一有限搜索不构成一般证明。

旧 law 的实际对象证据来自 `StatementReview.lean`：旋转 ν 三角，(e_f,e_g,e_h)=(0,0,1)，(n,m,l,s,t)=(1,0,2,1,16)，x=d₂(h₄)=h₀h₃²，x̄=y=ȳ=0，h 使用指定 suspendedX；几何条件、h/g 的真实 finite witnesses、d₃(0)=0 和 d₃-no-crossing 均由原辅助文件提供。正长度 exact-source f-extension 必须杀掉该 x 的 normalized leading image，而 `BottomNuInjection` 给出实际非零像。反证证明体未调用 `generalizedMahowald`，不是把整个环境中旧 law 的 sorry 当作真后再用矛盾证明新目标。它仍依赖已登记的实际模型、标签、E₂数据和文献责任，所以证据等级是**相对于登记上游的实际对象 Lean 反证**；本轮没有重新构建或消除其传递待补，不将之称为无项目待补的独立基础反例。

May 张量引理只调用固定 Literature 的 `may_pushpull`、shift/exactness；源码的两式确有负号。`may_leftShift`、`may_rightShift`、`may_leftExact`、`may_rightExact`、`may_pushpull` 目前均有登记的待补。顶层实际相等依赖 `AdamsSynthetic.Standard.synthetic_homotopy_separated`；有限标签和 λ/ρ 兼容依赖 Literature 的 `eInfinity_finite_labels`、`eInfinity_lambda_finite`、`eInfinity_rho_finite`；完整反射依赖 `eInfinity_rho_nu`。这些责任不得从报告中省掉，也不能作为额外新假设转交给下游来代替既有上游交付。

没有以候选结论、已使用它的 SS 终态或待证目标永久性验证本候选。允许的证明顺序为 May → 实际商比较 → 标签与同步 → 方框解码／经典提升 → 具体计算证书；若使用历史 MH 节点，必须先建立独立初始事实上的无环认证。源码 imports 涵盖含有旧 law 的环境，并不等于证明体依赖旧 law；相反，仅按 import 列表排除循环也不够，实施时仍须复用 transitive declaration audit。

## 精确差异与保留原接口方案

原完整 Lean 签名在[原声明摘录](evidence/original-law.txt)，含全部宇宙、实例和隐参背景；其标准证明入口是 `(T : TriangleData model.auxiliary) : GeneralizedMahowaldLaw model T`。本提案尚未提供可 elaboration 的完整候选 Lean 签名，这一交付明确未完成，不能直接更换锁文件。

先考虑保留原 law 的内部证明：对 n=3,m=l=0、(e_f,e_g,e_h)=(1,0,0) 的 Main 特例，已有安全的零层路线可继续；对全称原 law，不能通过重新选择一个 May lift 或一般 λ 除法消掉上述 exact-source 反证。若加强前提以排除此例，或把源换为 coset，均已改变公共语义，必须单独送审。把 x 默认为任意同商代表不是保留接口的修复。

数学候选的精确变化是：固定模型和 T 保留；新增 i,j 及 A,B,N,K,J 的显式商、层；输入从两条独立 extension 式加旧 crossing，改为上文同一 a 的三条检测和同一 b 的两条检测；x 的初始 cycle 从 Z_(n₁) 扩展为 Z_(n₁−j)，不改指定 x 的双次数；输出保留 x∈Z_Q，但 extension 改为 Q_N 中 λ^Kx 到 λ^Jy，并保留实际 c 及两式。i=j=0 时 Q 与旧结论相同，商从旧 Q_Q 保留为 Q_r，源层从 0 改为 k，固有源分母 B_(k+1)、目标分母 B_(r′)，外加短 ESS 像商。新输入是明确的充分证书；在同步定理未证前，不声称新旧前提等价或整体定理强弱可线性比较。

可选方案是先只公开实际代表版，或先公开零输入层推论；二者都应在准确 Lean 签名完成后申请所需出口。单纯把旧目标改为弱投影 Q_Q 会丢掉 k≥m₁+1 时的目标，不能覆盖所需强有限调用。把新代表证书无限期要求给 Main 等下游，亦不是本提案默认方案；同步和桥梁仍由 ProofTools 构造并证明。

## 受影响对象、记录与测试

未来如批准实施，需逐项复查 `GeneralizedMahowaldLaw`、`Standard.generalizedMahowald` 及其 `ProofTools` 公共导出；`metadata/proof-tools-api.json`、`metadata/proof-obligations.json`；`Tests/ProofTools/Consumers.lean` 的旧 law 消费、Interface 锁与 `InternalAudit` 中已有禁用待补依赖审计，以及 Integration、Architecture、Trust 汇总。Blueprint 的 `blueprint/paper/ProofTools.tex` 中 `paper:6.12` 与 semantic law 绑定必须依实际公共实现同步，不能把当前私有 May 引理绑成完整 MH。原始来源与论文修正继续引用既有 bibliography、Blueprint 和 `corrections.yaml`，不在此另立修正版维护源。

Main 的禁用旧 MH 边界和现有安全特例保持；AdamsCalculations 的具体计算认证仍归该模块，ProofTools 不接管。AdamsSynthetic 和 Literature 的固定对象/比较/文献构造责任继续原归属。本次未修改生产代码、接口锁、待补清单、corrections 或导出。

## 阻塞范围与可继续项

准确受阻的是全称旧 exact-source law 的直接数学补证，以及任何确实需要从它取得正层到零层升级的依赖闭包。受争议条目仍为既有待补，不能用 sorry 得到的新结论绕开问题。尚无证据可把某个 SS 历史局部缺口自动认定为 Main 最终目标的依赖。

可继续：保持冻结接口的私有 signed May 商比较；零输入层强商构造；写出完整双层检测 Lean 类型；实际 no-crossing 同步证明；有限—有限方框的 ordinary 解码；仿射提升条件的 ProofTools 证明；论文所需计算的独立依赖闭包和局部证书；Main 安全特例及所有无争议的既有补证。

## 实际检查与未完成边界

报告员实际完成上述独立源码与数学审查、同目录有限算术复现及来源指纹复查；未运行共享 `lake build`。协调者在同一任务另行报告 `python3 scripts/check-source-inventory.py` 通过、`lake build` 通过（3535 jobs），以及 Blueprint 34 项 unittest 通过。这些是协调者执行的仓库基线检查；它们没有 elaboration 本报告候选，也不证明新 MH 或全部 SS 调用正确。

没有新 Lean theorem、没有新公理或证明洞，没有认证全部历史运行，没有给完整公共 no-crossing 签名，也没有消除固定模型的上游待补。本次独立结论限于：数学规格及分层路线可作为当前目标；精确公开 API 和代表同步责任仍须完成。

## 人类审核记录

2026-10-18，本聊天用户明确批准：“就按这个方案推进，先把完整的 Lean 陈述和实际 no-crossing 条件定下来，写出完整的陈述，替换掉现在 blueprint prooftools 章节里里无法证明的版本，再完成形式化证明。”据此将状态改为 `approved-interface-change`，实施尚在进行；授权内容及不扩大到其他模块/新增公理和上游责任的边界见文件头。群内既有意见、历史其他提案批准及 agent 审查意见没有被写作额外授权。


## 2026-10-19 本轮固定基线独立复核与删除范围待决

本段报告员为 `/root/interface_reporter`，未参与本候选发现、反例实现或带层定理实现。复核基线为 `0e940a5108088ad73a19415721060012a8aad779`，工作区为 `/inspire/hdd/global_user/czxs25250150/ops/tmp/prooftools-main-proofs-20261019`；本次用户任务是完成 ProofTools/Main 的 sorry 及 Main 灰色 Blueprint 节点。依据当前 AGENTS.md、`docs/interface-proposals.md`、指定 protocol 和人审模板，只追加本段，不改生产源码、接口锁、修正记录、人审原话或文件头的历史状态。

本段中的**撤销旧定理出口建议仍为 `pending-human-review`，`human_decision: null`**；它不是新增的独立提案，不改变本报告既有人审事项的状态。授权实现一个正确替代定理，不自动授权删除仍冻结的旧声明。当前用户的补证请求也没有明确包含删除公共声明。

### 当前原接口及其目的（完整声明复录）

当前 generic law 仍位于 `KIP126/ProofTools/Laws.lean`，目的为从实际相容三角、两条有限扩张、Z 上微分及旧 crossing，返回**指定原始 x** 的更高 cycle 和零 λ 层 f-extension，允许目标在指定 B 层内修改。完整上下文与当前声明如下；固定入口将这些参数专门化到 `Standard.model`：

```lean
universe u v w
variable {C : Type u} [StableHomotopyCategory.{u,v} C]
  [HasFunctorialCofiber (C := C)]
  {Syn : Type w} [SyntheticCategory.{w,v} Syn]
  [HasFunctorialCofiber (C := Syn)] (D : Model C Syn)
public def GeneralizedMahowaldLaw (T : TriangleData D.auxiliary) : Prop :=
  ∀ he : (normalizedExponent D.classicalTower T.f : ℤ) + normalizedExponent D.classicalTower T.g +
      normalizedExponent D.classicalTower T.h = 1,
  KIP126.Literature.NormalizedTriangleCompatible D T he →
  ∀ (n m l s t : ℤ),
    let r := n + m + l
    let n₁ := n - normalizedExponent D.classicalTower T.f
    let m₁ := m - normalizedExponent D.classicalTower T.g
    let l₁ := l - normalizedExponent D.classicalTower T.h
    let r' := r - m₁
    ∀ (x : Ambient D (T.X) (s + l, t + l - 1))
      (y : Ambient D (T.Y) (s + l + n, t + l - 1 + n))
      (xBar : Ambient D (T.Z) (s, t))
      (yBar : Ambient D (T.Z) (s + l + n + m, t + l - 1 + n + m))
      (suspendedX : Ambient D (.shift 1 T.X) (s + l, t + l)),
      1 ≤ n₁ → 0 ≤ m₁ → 0 ≤ l₁ →
      IsCycle D (T.X) n₁ (s + l, t + l - 1) x →
      IsCycle D (T.Y) (m₁ + 1) (s + l + n, t + l - 1 + n) y →
      IsCycle D (T.Z) (r - 1) (s, t) xBar →
      IsPermanent D (T.Z) (s + l + n + m, t + l - 1 + n + m) yBar →
      (D.classicalSuspension T.X).DesuspendsClass (s + l) (t + l) suspendedX x →
      FiniteExtension D T.Z (.shift 1 T.X) T.h r'.toNat l s t xBar suspendedX →
      DifferentialAt D (T.Z) r (s, t)
        (s + l + n + m, t + l - 1 + n + m) xBar yBar →
      (FiniteNoCrossing D T.Z (.shift 1 T.X) T.h r'.toNat l s t ∨
        NoCrossingOn D (T.Z) r r' (s, t)) →
      FiniteExtension D T.Y T.Z T.g (m₁ + 2).toNat m (s + l + n) (t + l - 1 + n) y yBar →
      IsCycle D (T.X) (n + m + normalizedExponent D.classicalTower T.h) (s + l, t + l - 1) x ∧
        ∃ y' : Ambient D (T.Y) (s + l + n, t + l - 1 + n),
          FiniteExtension D T.X T.Y T.f (n + m + 1 + normalizedExponent D.classicalTower T.h).toNat
            n (s + l) (t + l - 1) x y' ∧
          Congruent D (T.Y) r' (s + l + n, t + l - 1 + n) y' y

public theorem KIP126.ProofTools.Standard.generalizedMahowald
    (T : TriangleData model.auxiliary) :
    GeneralizedMahowaldLaw model T
```

### 独立实际对象、全部前提及反证核对

本轮直接阅读 `StatementReview.lean`、`RotatedNuTriangle.lean`、`RotatedNuPremises.lean`、`SuspensionClassLabels.lean`、`SourceBoundaryReview.lean` 及 `BottomNuInjection.lean`，未用发现者摘要代替源码核验。

| 原前提/对象 | 本轮实际核验 |
| --- | --- |
| 固定对象 | X=sphere，Y=ν-cofiber，Z=`.shift 1 (.shift 3 .sphere)`；T 是固定 ν 三角的实际旋转，h 为 `-Σν`，不是任意抽象模型。 |
| 固定 normalized maps 及几何 | `rotated_nu_normalized_distinguished` 证明所选 normalized 三角的相容性，不只声称存在任选旋转；指数逐项为 `(0,0,1)`。 |
| 参数范围 | `(n,m,l,s,t)=(1,0,2,1,16)`，r=r′=3，n₁=1，m₁=0，l₁=1，符合全部下界。 |
| 指定 x | `mh2BoundaryClass=oneLineTarget model 4`，由 Literature `adamsOneLine_d2 4` 给非零 `d₂(h₄)`；在 `(3,17)` 的 B₂ 内，因此属于要求的 Z₁。 |
| 指定 y、xBar、yBar | 均为零，分别在 `(4,18)`、`(1,16)`、`(4,18)`，满足 Z₁、Z₂ 与永久条件；原 law 明确允许零。 |
| 真实 suspendedX | 由 `exists_suspendsClass_mem_boundary`、实际 tower/layer 与 raw-boundary 悬挂比较构造 sx，确实 `DesuspendsClass ... sx x`，且 sx∈B₂；没有把任意 E₂ 等价当反悬挂。 |
| h 扩张 | 商 Q₂ 中的真实零 witness，再沿允许的目标 B₂ 歧义加 sx，得到 page=3、length=2 的指定 h 扩张。 |
| Z 微分 | `candidate_zero_differential` 构造 `d₃(0)=0` 的真实页代表。 |
| crossing 析取 | 采用 Z 上微分 no-crossing 分支。唯一位置 a=1,b=0；相应源 `(2,17)` 由实际移位/第一商比较及 sphere Ext `(2,13)` 为零而消失。无需另假设 h 分支。 |
| g 扩张 | 固定 g 的 page=2、length=0 零 witness，长度界由 e(g)=0 验证。 |
| 假结论 | 原结论要求从**同一原始 x** 出发的 page=3、length=1 零层 f-extension。`nonzero_leading_image_no_positive_extension` 排除任何目标 y′，比只排除同余条件更强。 |

`BottomNuInjection` 使用固定 ν 三角上的 Hom 精确性、实际第一商与 Ext `(2,13)`、`(3,14)` 消失，证明该指定 boundary 的 normalized 底映射 E₂ 像非零。正长度零层扩张则强迫同一 E₂ 像为零。`StatementReview` 的 `rotated_nu_generalized_mahowald_law_false` 将这些事实代入原 law 得否定；它不调用 `Standard.generalizedMahowald`。因此这是**相对于已登记上游构造/比较责任的固定对象 Lean 否定**，不是自由模型反例，也不是“未找到证明”。同一个包含旧 sorry theorem 的环境不能据此拿 False 消除其他目标。

### 保留原接口的内部方案、已有正确替代和精确最小变更

先考虑保留原接口补证：重选 May lift、补第二像、λ 除法或把 x 悄悄换成同余代表，都无法同时维持本表中的全部原前提和 exact-source 结论。x∈B₂ 并不等于原始 E₂ 向量 x=0；原 h 输入在正 λ 层已把这项歧义商掉，但零层 f 输出重新要求原始 x，因此失败。问题属于原命题错误/λ 层与指定对象关联失配，不是仅缺局部几何实现。

已实现的新签名保持为：

```lean
public theorem KIP126.ProofTools.Standard.generalizedMahowaldAtLevel
    (T : TriangleData model.auxiliary)
    (he : (normalizedExponent model.classicalTower T.f : ℤ) +
      normalizedExponent model.classicalTower T.g +
      normalizedExponent model.classicalTower T.h = 1) :
    FiniteMahowaldAtLevelStatement T he
```

本轮核对 `FiniteLevelStatement.lean` 完整类型及 `FiniteLevelAssembly.lean` 装配：前提使用同一实际三角、n₁,m₁,k,i,j，j<n₁，三个实际 ESS 输入与 actual no-crossing；结论交付同一 a,b,c、两条严格 signed 方程、五项输入检测和输出检测、原 x 的 cycle 及 `LevelFiniteExtension (Q+1) K ... x y`。其中 `A=n₁+k+i-j,B=m₁+j+1,N=A+B,K=i+k,J=A+j,Q=N-K`；并无额外 hRows。它保留强商 Q_N 的 λ^K 源层，不提供原 law 的任意零层取消。新旧前提和输出均有实质变化，不能称新 theorem 已补完旧 `GeneralizedMahowaldLaw`。

待人类决定的最小方案：撤销且仅撤销旧 theorem `Standard.generalizedMahowald (T : TriangleData model.auxiliary) : GeneralizedMahowaldLaw model T` 的公共导出及其旧待补登记；候选旧名称签名为**无声明**。保留当前 `GeneralizedMahowaldLaw` Prop 定义以表达历史失败命题及固定对象否定，保留已证 `generalizedMahowaldAtLevel`、原反证文件和提案。此方案无新 theorem 责任、新公理或新前提，无须把共同代表证明转给 Main。若要求保留旧 theorem，必须如实保留其争议 sorry，不能宣称“原洞已证完”。私有化/删除 Prop 定义或新增 exact-source 修正版属于另外范围，本段未申请其实施。

### 现有人审权限、下游和可继续项

本报告既有人审原话“就按这个方案推进……替换掉现在 blueprint prooftools 章节里里无法证明的版本，再完成形式化证明”已支持当前带层方案及 Blueprint 替换；无需重复询问该已获批方案。既有实施记录同时明确旧 law 和待补保留。没有查到授权**删除旧 theorem 公共出口**的真实原话，故不能把本报告的 implemented 状态扩张成删除批准。新删除建议的决定仍为 null；不改写原批准。

直接消费者是 `Tests/ProofTools/Consumers.lean:50` 的旧 law example；生产源码中未发现 AdamsCalculations/Main 调用旧 theorem。`Main/InternalAudit.lean` 明确禁止旧 GL/MH 出现在公共 Main 根依赖中。删除获批后的同步范围为旧 theorem 源码、ProofTools API 导出/type/axiom 锁、旧洞登记、ProofTools internal audit 的精确许可洞数组和对应普通消费例；保留独立反证及 Main 无旧 law 依赖边界。Blueprint `paper:6.12` 已绑定完整带层 theorem，`Tests/test_blueprint_native.py` 已禁止旧 law/theorem 四项绑定，不需要恢复旧节点。继续运行 inventory、接口/消费者/Trust 与完整 `lake build`，不删除原有覆盖或放宽检查。

阻塞只覆盖原全称零层 exact-source law 的正确补证及其真实调用闭包。Main 既有安全数值实例、其他本地引理、灰色节点的真实命题对应、三个其他 ProofTools 责任、已完成带层 GL/MH 的使用均可继续。是否那些独立原陈述另有接口问题需各自证明，不能据本反证推定它们都错误。

### 本轮实际执行的证明体依赖复现与局限

报告员使用固定 Lean 4.32.2，以 stdin 普通元程序只读导入当前已编译的全部相关模块；`import all` 恢复项目真实证明体，递归遍历类型及证明体常量，不从 import 列表推断依赖。命令无 `-o`，没有写共享构建产物；下列完整命令可在上述工作区复现：

```sh
python3 - <<'PYPROBE'
from pathlib import Path
import subprocess
imports=[]
for part in ('SpectralSequence','AdamsSynthetic','Literature','E2Computation','ProofTools'):
 for p in sorted((Path('KIP126')/part).rglob('*.lean')):
  if p.name!='InternalAudit.lean' and (Path('.lake/build/lib/lean')/p.with_suffix('.olean')).exists():
   imports.append('import all '+'.'.join(p.with_suffix('').parts))
probe='module\n'+'\n'.join(imports)+"""
import Lean
open Lean Elab Command
set_option maxHeartbeats 0
set_option maxRecDepth 8192
run_cmd do
  let env ← getEnv
  for target in #[`KIP126.ProofTools.Internal.Mahowald.rotated_nu_generalized_mahowald_law_false,
    `KIP126.ProofTools.Standard.generalizedMahowaldAtLevel,
    `KIP126.ProofTools.Standard.generalizedLeibnizAtLevel] do
    let some (root,ri) := env.constants.toList.find? (fun (n,_) => ((privateToUserName? n).getD n)==target)
      | throwError "missing root {target}"
    logInfo m!"ROOT {target}: {ri.type}"
    let mut todo := #[root]
    let mut seen : NameSet := {}
    let mut holes : Array Name := #[]
    let mut axiomsFound : Array Name := #[]
    let mut bad : Array Name := #[]
    while let some n := todo.back? do
      todo := todo.pop
      if seen.contains n then continue
      seen := seen.insert n
      let some info := env.find? n | throwError "missing {n}"
      let some idx := env.getModuleIdxFor? n | continue
      let mod := env.header.moduleNames[idx.toNat]!
      unless (`KIP126).isPrefixOf mod do continue
      if n==`KIP126.ProofTools.Standard.generalizedLeibniz || n==`KIP126.ProofTools.Standard.generalizedMahowald ||
          (`KIP126.Main).isPrefixOf mod || (`KIP126.AdamsCalculations).isPrefixOf mod then bad := bad.push n
      let b := info.value? (allowOpaque := true)
      if info.isAxiom then axiomsFound := axiomsFound.push n
      if info.type.hasSorry || b.any (·.hasSorry) then holes := holes.push n
      if info.type.hasSyntheticSorry || b.any (·.hasSyntheticSorry) then throwError "synthetic sorry {n}"
      todo := todo ++ info.type.getUsedConstants
      if let some v := b then todo := todo ++ v.getUsedConstants
    logInfo m!"CLOSURE {target}: holes={holes.size}; project axioms={axiomsFound}; forbidden={bad}"
    for n in holes do logInfo m!"UPSTREAM {target}: {n}"
"""
r=subprocess.run(['lake','env','lean','--stdin'],input=probe,text=True,capture_output=True)
print(r.stdout); print(r.stderr); print('RETURN',r.returncode)
PYPROBE
```

实际成功输出（`RETURN 0`）为：

| 实际 kernel 根 | 传递含 sorry 声明数 | 项目公理/不可见公理体 | 禁用旧 theorem 或下游模块 |
| --- | ---: | --- | --- |
| `rotated_nu_generalized_mahowald_law_false` | 57 | `[]` | `[]` |
| `Standard.generalizedMahowaldAtLevel` | 55 | `[]` | `[]` |
| `Standard.generalizedLeibnizAtLevel` | 53 | `[]` | `[]` |

三根均未触发 synthetic sorry 检查；输出的所有待补声明位于 AdamsSynthetic、Literature 或实际 E2Computation 源模块，未见 ProofTools 本地洞。`Computation.Standard.sourceCoordinates/comparison` 的命名是兼容公开名称，责任依实际源文件为 E2Computation，不是后续 AdamsCalculations。MH 反证闭包明确包含 `adamsOneLine_d2`、`nuCofiber_triangle`、`nuCofiber_normalized_label`、固定模型/归一化/悬挂及 E∞ 比较、实际 E₂ 坐标和 `synthetic_homotopy_separated`；没有借旧 GL/MH 的未证 theorem，也没有用它们的下游结论形成循环。保留这些未完成上游意味着不能称本反证或两个替代定理为无项目待补的基础证明。

这项 probe 检查的是已有编译快照的完整可见证明体；它没有重证上游责任，也不替代协调者对当前源码及锁的全量 `lake build`。初次沙箱内 `lake env lean` 自定位失败；改用沙箱外同一固定工具链后可运行。首次全文件导入遇到尚未构建的 `Paper/OriginalStatements.olean`，第二次元程序使用了 Lean 保留字作局部变量名而失败；最终命令限定已有 olean，并改名后 exit 0。所有失败均未产生证明或被当作数学反证。两个根和反证的 olean 均已存在且可读；当前表格不掩盖这些复现限制。

有限参数检查也实际 exit 0：GL 得 crossing 三对及 `d₄(0)=v` 的次数，MH 得 r=r′=3、n₁=1、m₁=0、k=1 及被迫 page=3/length=1 输出。提案校验使用主检出的既有环境：`/inspire/hdd/global_user/czxs25250150/Kervaire126Main/.lake/blueprint-env/bin/python scripts/interface-proposals.py validate`，实际输出 `Validated 20 interface reports.`；默认 python 缺 hgraph，未安装或升级任何依赖。

本轮读到的源码/锁 SHA-256 如下。文件头中的旧路径和指纹保留为历史元数据，本表明确当前已迁移到 `interface/baselines/` 的复核基线：

| 文件 | SHA-256 |
| --- | --- |
| `interface/baselines/proof-tools-api.json` | `872918c18d6c4615d12e8af35eb7cce8946e26da259db920c75597fc6d86c316` |
| `interface/baselines/proof-obligations.json` | `a1ae6319534fa43ff6240400f4a5410000dee7bd763009d8b6a5f459dab8a9a8` |
| `KIP126/ProofTools/Laws.lean` | `8731a608b3c750b044837c927ae45a8aee71eebdff441d89dd82df6b97f0732a` |
| `KIP126/ProofTools/GeneralizedLeibniz.lean` | `5ffca10bbcfc95048225a2d17175a76374d804288d022e9ee1e64736167cd8b9` |
| `KIP126/ProofTools/GeneralizedMahowald.lean` | `35479f3f2b4af8a0ff7950410557e47cd1d36f2263c10e2426fd6510a2d10c70` |
| `KIP126/ProofTools/GeneralizedMahowald/StatementReview.lean` | `9d1e24895fafa69c994d1b512e308c99fb94d351102234a5db8ee141cc33f47c` |
| `KIP126/ProofTools/GeneralizedMahowald/FiniteLevelStatement.lean` | `cdcaac79ea9481bd2030a2bd48fd091889d49097df1df8a7119a80acd2f77182` |

本轮没有代填删除方案的人类决定，没有修改原批准范围，也没有发布或实施拟议代码。


## 2026-10-19 用户明确批准撤销旧 theorem

用户在核对 Blueprint 已只绑定两个 AtLevel 版本后，明确要求：

> 那就删掉这两个旧定理，保留 law 定义、反例证据和已证的 AtLevel 版本，同步接口锁、待补清单和测试，再跑完整检查。

本段由协调者 `/root` 记录真实授权及实施范围，不冒充独立报告员的新审查，也不改变此前证据等级。授权撤销的仅为 `KIP126.ProofTools.Standard.generalizedLeibniz`、`KIP126.ProofTools.Standard.generalizedMahowald` 两个错误 theorem；对应源码中的三处 `sorry` 和两项登记责任随之移除，不能记作证明了旧命题。`GeneralizedLeibnizLaw`、`GeneralizedMahowaldLaw`、固定模型 MH 否定证书、原 GL 数学反例和全部 AtLevel 定义/证明保留。

普通消费测试改为要求旧 theorem 不可见，并继续消费两个 law 定义及 AtLevel 定理。Main 的旧 GL/MH 禁用边界继续保留；既有 Blueprint 不绑定这两个旧 theorem，无须变更其数学节点。三项 `Paper.OriginalStatements` 责任继续逐项锁定，没有新增公理或证明洞。编译、精确接口和全量检查结果随后记录。

精确编译捕获已完成：删除两个命名 theorem，另有旧 GL 证明生成的自动辅助 `KIP126.Literature.bocksteinLabel.congr_simp` 随证明消失，其实际定义归属原为 ProofTools；没有新增导出，所有剩余接口行（类型、宇宙、axiom 依赖）逐行不变。待补总数 233，ProofTools 三项。用户随后要求暂不运行完整检查，先证明剩余三责任，因此本段只记录已完成的公共入口编译与精确捕获，不宣称本轮全量检查通过。
