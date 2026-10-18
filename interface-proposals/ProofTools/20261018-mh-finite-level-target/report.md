---
issue_id: ProofTools-20261018-mh-finite-level-target
title: MH 形式化目标：强有限商、双输入层数与共同代表
summary: 群材料与仓库研究已足以确定有限 MH 的数学候选；建议以代表级 May 方程和双输入层标签定理为目标，另证实际 no-crossing 的同步推论。普通 Adams 解码与经典提升分别处理。此次仅汇总研究，不修改公共接口或登记新证明洞；完整 Lean 签名与独立复核尚待交付。
responsibility_module: ProofTools
targets:
  - KIP126.ProofTools.GeneralizedMahowaldLaw
  - KIP126.ProofTools.Standard.generalizedMahowald
baseline_commit: 1dc13a1973bc0f69c14e39f197372c30a350d4e8
reporter_agent: /root
independent_of_discoverer_and_implementer: false
evidence_level: 原群消息、原始 TeX 与研究 PDF 的来源核对及源码复查；复用历史独立数学笔记；本次没有新增 Lean 证明或重新认证历史计算
status: draft
human_decision: null
---

# 建议采用的目标

2026-10-18。用户本次要求查阅 project-math-assistant 群和仓库研究，确定应形式化的 MH 版本。本报告是研究汇总草稿，不冒充新独立接口审查，也不把“基本确定陈述”解释为已批准增删公开声明。

建议确定数学目标为：**保留强有限商的双输入层 MH，输出同一个实际代表及其两条像方程；实际 no-crossing 到共同代表的同步定理是需要另外完成的证明部分。** 普通 Adams 输出与经典 extension 输出分别给有完整前提的推论。不要继续把有反例的旧 exact-source 零层结论作为一般证明目标。

这是可审阅的数学规格；不是已经 elaboration 通过的新 Lean 类型。新增公开名称、一般 law 的替代方式、旧接口的最终处置及相应锁文件改动仍需明确授权。现阶段不需要暂停保持接口不变的局部补证。

相对 AimPaper 的问题、反例及状态唯一维护在根目录 `corrections.yaml` 的 `mahowald` 条目；原文对应 `paper:6.12`。本报告维护候选接口及其授权边界，不另立论文修正记录。

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

对相容双次数中的实际 a∈πQ_A Z、b∈πQ_B Y，若 δ(a)=g_B(b)，则要求构造**同一个** c∈πQ_N X，使

\[
\rho(c)=h_A(a),\qquad f_N(c)=-\lambda^A b.
\]

所有式子均通过同一组固定悬挂、商和张量比较解释。负号来自当前 `GeneralizedMahowald/Geometry.lean` 的 `may_tensor_common_lift`；不能因 E₂ 系数为 F₂ 就在实际同伦群等式中删号。该文件已证明张量形式的两式；向指定实际商映射的比较仍需核查和完成，不能将局部张量引理称作完整 quotient 定理。

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

这里“检测”指实际过滤至少为指定级，且在该关联分次具有指定标签；零标签表示过滤至少再高一层。Q_D 第 a 层使用 Z_(D−a)/B_(a+1)，并非原始 E₂ 向量的相等。两个 ȳ 像位于 Q_B 的最高可见层，顶层唯一性给实际等式 δ(a)=g_B(b)。

结论要求交付 c∈π_(t−s−1,t+e_h−1−i)Q_N X 及第一层的两式，c 检测 λ^K x，f_N(c) 检测 λ^J y，并推出

\[
x\in Z_Q,\qquad d_n^{\hat f_N}(\lambda^Kx)=[\lambda^Jy].
\]

源标签按 Z_Q/B_(K+1) 解释，目标按

\[
\bigl(Z_{m_1+1}/B_{J+1}\bigr)
\big/\{\text{长度小于 }n\text{ 的实际 }\hat f_N\text{-ESS 像}\}
\]

解释。目标允许为零或 inessential；y≠0 不保证其 ESS 页类非零。y=0 不意味着 f_N(c)=0。保留 c 与其实际像检测，不能仅返回这个末端商等式。

指标核对：A−K=n₁−j>0，N−K=Q，N−J=m₁+1，J−K=n₁；δ 的目标层 i+r−A−1=B−1。normalized f 把 c 的 weight 变为 t−i−e_g，等于 b 的 weight 减 A。源 cycle 由实际 Q_N 检测及 K<A 的投影反射取得；证明不取消 λ^K。

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

保留目标的精确提升条件为 A_η∩p(F^s₀G)≠∅；在相关源过滤反射下，等价于连接障碍 ∂c₀∈∂V。不必要求原选 c₀ 自己提升，但不能只由源标签永久推出这个仿射族里有完整 lift。目标过滤反射、固定标签比较和经典恢复也须保留。仅短有限 ESS 商中的目标相等不足以推出指定原始 y 永久；要认证 SynCsIn，须保留其实际目标首项。上述障碍准则及足够的全修正替换条件是后续应证引理，非此次已完成结果。

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

## 实际检查与未完成边界

本次重新读取群历史与附件、检查原 TeX 指纹、对照 law/反证/May/零层实现及现有 level GL、λ division 的实际签名，并逐式核对参数与 weight。历史独立笔记作为来源保留；本次没有启动新的独立 agent 审计。

没有新 Lean theorem、没有新公理或证明洞，也没有宣称 double-level MH 已被内核验证。后续应先在保持接口冻结下做私有构造，完整写出 no-crossing 同步推论及候选 Lean 类型，独立复核后再决定公开出口与旧接口处置。
