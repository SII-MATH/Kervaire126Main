# 6.20 固定原 y、b=0 版本：第二轮独立核验

日期：2026-10-17。基线 `aad718722aa01dfce361f40645fc776037d1078f`。任务依据：用户授权按 guozhen 群内新回复“一般的 b，可以推 b=0”继续补证，消息 `om_x100b620395ee84a4de3f31d816bb406`，position 1481。核验者只读生产文件，遵守 `AGENTS.md` 与 `/root/.agents/skills/kip-upstream-session/references/protocol.md`，仅写本报告及 `WangBzeroAudit.lean`；未参与被核验 worker 候选实现。

## 结论和证据等级

**固定原目标 y、取 b=0、保留经典非 liftable 源差集的完整 iff，不能据本轮探索登记为已证。独立复核 worker 的 HZ/16 构造后，它给出这个新增必要方向的纸面实际谱反例。** 该结论相对于论文已引用的标准 synthetic 刚性、归一化三角和通常的 HZ Adams 计算成立；这些识别不是任意 filtered 方块的可实现性假设。

必须区分两种完成程度：

- **数学层面**：实际谱、实际映射、固定 weight 的有限 λ 商、δ/ρ 的自然性、完整 Adams 滤过与全部非 liftable 首项均可逐项计算。下面给出核验，没有剩余“它也许只是抽象方块”的识别缺项。
- **当前 Lean 层面**：库中的 `ClassicalObject` 没有 HZ、HZ/16，这些对象与上述识别没有在现有固定模型中实现。因此它不是已形式化的实际谱反例。已通过 Lean 的证据是商代表引理和相关有限算术，不能把它们标作整项谱反例已在 kernel 中核验。

这不否定首段合法域自然性，也不否定“命中原目标的较短方程 ⇒ 原扩张非本质”的方向。失败的是：**早页原扩张非本质 ⇒ 可同时选择非 liftable 首项、并仍命中原目标 y。**

## 两个旧疑点已进一步核实

### 同余代表不能掩盖真正的非 liftability

这里源的分次已固定，早晚页有同一个边界分母 `B_{1+a}`，而 `B_{1+a} ⊂ Z∞ ⊂ Z_late`。所以

\[
[x']\in\operatorname{im}(Z_{\rm late}/B\to Z_{\rm early}/B)
\quad\Longleftrightarrow\quad x'\in Z_{\rm late}.
\]

即使换一个模 B 同余的代表，结论也不变。新的独立 `WangBzeroAudit.lean` 已证明一般子模商版本，并专门应用于给定项目 `D : Model C Syn` 的实际经典 `cycles`、`boundaries`、`quotientMap`。两条定理均实际 kernel 检查通过，公理只有 `propext, Classical.choice, Quot.sound`。这补充了上轮仅凭文字分析的部分。

### 有效范围内 rho 的单射也不足以保持原目标

`StretchingRepresentatives.lean:207` 的真实证明通过标准 `E∞ = Z/B` 识别，建立有效条带内 `ρ` 的 E∞ 单射。它确实排除“晚页非零较低目标被 ρ 直接杀成零”。但早页 ESS 还会把新增较高源的像商掉：一个仍然非零的 synthetic E∞ 目标，可以在早页 ESS 中变成较短边界。下面的实际谱例子正好发生这件事。不能把 E∞ 单射误当成各个 ESS 页的单射。

## 实际谱和映射

令 `E = HZ₂∧`，`M = E/16 = H(Z/16)`，取标准实际谱三角

\[
E\xrightarrow{16}E\longrightarrow M\xrightarrow{\delta}\Sigma E.
\]

定义

\[
X=\Sigma E_x\oplus\Sigma E_u\oplus M,
\qquad Y=\Sigma E_z\oplus\Sigma E_{y_0},
\]

\[
f|_{\Sigma E_x}=8y_0,\qquad
f|_{\Sigma E_u}=2z,\qquad
f|_M=(\delta,2\delta).
\]

各项都是明确的 E-module 映射，因而是实际谱映射。这些谱 connective、2-complete，逐度 mod-2 同调有限，满足论文 `main.tex:255` 的全局条件。`δ` 在 mod-2 同调非零，故整个 `f` 有 `AF(f)=0`、`e(f)=0`。这里不把 ν 的 suspension 比较误认为普通稳定 suspension 的无移位等式。

取

\[
(s,t)=(0,1),\quad n=3,\quad r'=5,\quad r=7,
\quad x\text{ 为 }\Sigma E_x\text{ 的初始类},
\quad y=h_0^3y_0\in\operatorname{Ext}^{3,4}(Y).
\]

`x` 和 `y` 都是经典永久循环，且早页合法长度界为 `0 ≤ 3 ≤ 5−2`。原 y 自始至终是 `h₀³y₀`，从未用其他目标替代。

## 实际 Adams 和 synthetic 识别的独立复核

### 1. HF₂-Adams 输入不是任意 2-adic filtration

直接读取一手原文 [May–Milgram, *The Bockstein and the Adams Spectral Sequences*, Proc. AMS 83(1), 1981](https://math.uchicago.edu/~may/PAPERS/34.pdf)，印刷页 129 的 Lemma 3(ii)(iii) 和 Lemma 4。它们给出 HZ 的单条 h₀ spike、HZ/16 的两条 spike 及实际 `d₄`，以及楔和的直和。其结果在本例是

\[
\operatorname{Ext}(E)=\mathbf F_2[h_0],\qquad
\operatorname{Ext}(M)=\mathbf F_2[h_0]\{w,v\},
\quad |w|=(0,0),\quad |v|=(0,1),
\quad d_4(v)=h_0^4w.
\]

原文还明确说明整数乘 2 与 h₀ 检测的兼容，支持所需的 2-extension，而非仅给出一张无乘法的 E∞ 图。可另核对 [Rognes 2012 讲义](https://www.mn.uio.no/math/personer/vit/rognes/kurs/mat9580v12/notes.050612.pdf)，印刷页 43 的 Lemma 4.27，`H*(HZ)=A/A{Sq¹}`。change-of-rings 得上述单 spike，无额外 Steenrod-module Ext 类遗漏。

### 2. νE 的群、lambda 和基底

记 `N=νE`。由单条 h₀ tower 和论文刚性对应，synthetic Adams E∞ 只在 stem 0；强收敛排除其他 stem 的隐藏同伦组。`λ` 在这条 tower 上没有核，且 `λh₀=2`。在 weight 0 用实际整数单位固定基底，weight `w≥0` 的基底取 `h₀^w`，则

\[
\pi_{0,w}N=h_0^w\mathbf Z_2,
\qquad F^a\pi_{0,w}N
=2^{\max(a-w,0)}h_0^w\mathbf Z_2.
\]

也可将其由 λ 反演嵌入经典 `Z₂`，像为 `2^wZ₂`。这里 λ 在关联分次上的单射，加上强收敛/分离性，保证实际群中无 λ 核；整数单位及 h₀ 对 2 的检测确定隐藏 2-extension。并非只凭关联分次抽象地选一个群结构。

于是 `N_q=N/λ^q` 的长正合列在 weight 0、1 给出

\[
\pi_{0,0}N_q=\mathbf Z/2^q,\qquad
\pi_{0,1}N_q=h_0\mathbf Z/2^q,
\]

且 stem 1 为零：相关项只是 λ^q 在 N 的 stem 0 上的核，而该核为零。两组 filtration 基底分别在 AF0 和 AF1。

### 3. 整条归一化三角保留指定连接 delta

在实际 `16` 三角中，`e(16)=1`、`e(ι)=e(δ)=0`。后两项的非零性与指数由 mod-2 同调长正合列确定。因此论文 `main.tex:966–971` 的归一化三角适用，连同 `νΣE≃Σ^{1,1}νE` 得

\[
\Sigma^{0,1}N\xrightarrow{\widehat{16}}N
\longrightarrow\nu M\xrightarrow{\nu\delta}\Sigma^{1,1}N.
\]

这核对的是**指定的全部箭头**，不是任取一个 cofiber 同构。由于 `e(δ)=0`，末箭头就是 νδ，无额外 λ。`λ·widehat{16}=16`，并且在所需自由 N tower 中 λ 单射，所以在这些群上的 `widehat{16}=λ³h₀⁴`。在 weight 1，源 `Σ^{0,1}N` 的基底为 1，靶 N 的基底为 h₀，故实际系数为 **8**。

### 4. 模 lambda 商中的 K 坐标及 rho

商构造是 tensor/cofiber，在稳定范畴保持该三角。前一步 N_q 的 stem 1 为零，故在 stem 1、weight 1 的长正合列中

\[
\pi_{1,1}(\nu M/\lambda^q)
\xrightarrow[\text{单射}]{\nu\delta}
\pi_{1,1}(\Sigma^{1,1}N_q)=\mathbf Z/2^q
\xrightarrow{8}h_0\mathbf Z/2^q.
\]

所以其像正是

\[
K_q=\ker(8:\mathbf Z/2^q\to\mathbf Z/2^q),
\quad K_4=2\mathbf Z/16,\quad K_6=8\mathbf Z/64.
\]

这是由**实际 νδ**定义的坐标，因此 f 的第三列被同时确定。ρ 与此三角自然交换，所以 `K₆→K₄` 就是模 16 的约化，其像为 `8Z/16`；两个 ΣE 分量同样为通常约化。

### 5. K 坐标和 actual Adams filtration 严格相容

有限刚性公式给出 `λ^a h₀^a v` 在 weight 1 存活，当且仅当

\[
0\le a<q,\qquad h_0^av\in Z_{q-a},
\quad\text{即}\quad a\ge q-3.
\]

`δ` 在这些存活关联分次上把 v-tower 同阶发送到 ΣE 的 h₀ tower，非零且单射。由于有限 λ strip 只有有限个 filtration 层，可以逐层反射 filtration：某个 K 坐标实际类属于 `F^a` iff 它在 `Z/2^q` 中被 `2^a` 整除。不需要凭空假设连接映射是 strict filtered map，也不依赖争议的 6.20；strictness 已由这个有限条带中的关联分次单射导出。

以上五步提供实际谱到有限群、δ、ρ、f 及 filtration 的全部兼容。当前 Lean 对象库未实现它们，不等于纸面数学中缺失这些识别。

## 逐条验证被反驳命题的全部前提与结论

ν 保持有限双积及加法。因此在上述指定坐标中，真正的 νf/λ^q 是

\[
f_q(\alpha,\beta,c)=(2\beta+c,\ 8\alpha+2c),
\qquad \alpha,\beta\in\mathbf Z/2^q,\quad c\in K_q.
\]

ν 保持有限双积的性质亦可从其表示预层、π₀ 与加性 sheafification 构造看出，故不能在这里额外选择一个同形但无来源的矩阵。原 synthetic 目标 `λ³h₀³y₀` 正是 `(0,8)`。

| 项目 | 实际核验 |
| --- | --- |
| 同一 f、同一 x、同一 y | 所有 q 均来自上述一个谱映射；ρ 自然；y 恒为 h₀³y₀。 |
| 晚页 equation | q=6，源 `(1,0,0)` 的实际像是 `(0,8)`。 |
| 晚页 essential | 任意 F¹ 源有 α 偶数、c∈8Z/64，故其 y₀ 坐标 `8α+2c` 恒为 16 的倍数，不能在 F³/F⁴ 改变 `(0,8)` 的 y₀ 首项；已检查完整高源不定性。 |
| 早页 equation | q=4，同一源仍映到 `(0,8)`。 |
| 早页 inessential | 实际高源 `(0,−2,4)∈F¹` 映到 `(0,8)`；因此原目标是较短 ESS 像。 |
| 原文 Z 差集 | 允许 `1≤a≤3`；由 d₄，早 `Z_{4−a}` 与晚 `Z_{6−a}` 的差只可能在 a=1,2，并且源首项的 v 分量非零。a=3 全可 lift。 |
| 排除全部固定目标短式 | a=1,2 的非 liftable 首项有 c=`2^a·odd`；同层 β 是 2^a 的倍数，故 z 坐标 `2β+c` 恰在 AF a 非零。任何更高源修正不能消去这个 z 首项，因此它无法达到 AF3 的指定目标；等价地，该源已有非零 d₀，不能支持所需正长度 `d_{3−a}`。 |

源 x、u 的所有 tower 永久且可 lift；给 v 加它们的同次线性组合也不能消去上表的 z 首项，因为 f(u) 的 filtration 增加一、f(x) 增加三。M 的 stem 1 没有其他 tower、也无经典边界导致的假非 liftability。如此排除了差集中**全部** x′，不只是挑选两个代表检查。

这说明早页原扩张非本质，却不存在保留非 liftable 首项、命中同一 y 的 b=0 短方程。非 liftable v 首项首先命中较低 filtration 的 z；它消去 u 的低阶像以后，组合的首项又变回可 lift 的 u。这正是迭代保持原 y 失败的机制。ρ 的 E∞ 单射仍完全成立，z 并非被 ρ 杀掉。

## 形式化与传递依赖审计

核验读取了 worker 的完整证明报告与 `WangBzeroProof.lean`，并独立重新执行后者，而非依赖 worker 的摘要。九条纯算术 lemma 均 exit 0，`#print axioms` 至多含基础三项，无 `sorryAx`。其真实证明只使用整除、奇偶、区间和整数恒等式，不调用 6.20、标准 model、任何 Main 目标或项目待补。

独立 `WangBzeroAudit.lean` 的两条商代表定理也 exit 0，无 `sorryAx`。其中实际 `cycles` 应用使用现有 `boundaries_le_cycles`，该定理体从 SSData 的 B/Z 单调性与 `B∞≤Z∞` 构造，未调用待补的模型构造或标准刚性接口。

纸面谱识别依赖 May–Milgram 的 HZ Adams 计算、synthetic 刚性、ν 的标准 suspension/additivity 和归一化三角；不是从当前 Lean 中带 sorry 的标准模型推出 False 后进行证明。当前标准 `eInfinity_finite`、`eInfinity_finite_labels`、`eInfinity_rho_finite` 等仍有已登记上游责任：本报告既未完成它们，也没有将来源定理当作当前库内完成状态。反例不调用 6.20 本身或依赖它的 corollary，数学依赖不循环。

## 实际执行与输入固定

读取任务 protocol、仓库规则、完整 6.20/定义/crossing/归一化三角、生产 witness/标签/ρ 单射证明、worker 报告与算术源；通过 web 直接读取上述两份一手参考，其中 May–Milgram 印刷页 129 还查看了原 PDF 图像。实际只读 Lean 命令均未带 `-o`，不生成生产 `.olean` 或运行 `lake build`，使用协调者允许的 `require_escalated` 启动。

```text
lake env lean metadata/interface-reviews/ProofTools/20261017-paper-prop620-domain/evidence/WangBzeroAudit.lean
# 最终 exit 0；两条定理无 sorryAx。
lake env lean metadata/interface-reviews/ProofTools/20261017-paper-prop620-domain/evidence/WangBzeroProof.lean
# 独立复跑 exit 0；九条算术定理无 sorryAx。
```

第一份独立证据的初稿曾有 quotient API/整数 module 实例/命名解析错误，修正后实际通过；未把失败初稿记成通过。没有清缓存、改锁、改生产、发群消息、提交或推送。

| 输入 | SHA-256 |
| --- | --- |
| `AimPaper/main.tex` | `828ee5a5aa06e1f390b036a043230ed417446fa7be11a4e27eecc4a565135c4b` |
| `KIP126/ProofTools/StretchingRepresentatives.lean` | `0e1c5620076f7681ab31433a3054f97949696b2afb7d19c7bde8f6b7a4a930ba` |
| `KIP126/ProofTools/Language.lean` | `50164249c50b08c58a5357e1aec2ea6035dd8043474e71b69082b56eed9cd7ee` |
| `KIP126/Literature/Standard.lean` | `d473658cbd0d2944a5a75f2741ff24f5827c1e6e57f4d2d11c05508a0f4135c6` |
| `WangBzeroAudit.lean` | `8bdffb6ad0299056660188690f1aafec9f9fb74044b15db96c19635b2dcad1fe` |
| `WangBzeroProof.lean` | `d4fd6b3150a364442d3512492fe08b21701ceaae99151d22e162c799d00fa894` |
| `wang-bzero-proof.md` | `3d6f9111686dd5e095d7910513cfad0bd797741fcd83f0e3f6f2118838cbb0c0` |

共享生产与记录正在由协调者/其他 agent 修改，本核验未回退其变更。本报告是具体修正版的独立数学证据，不代表接口调整审批；需由协调者按协议另行安排独立接口报告员，保留历史审查和用户回复，不实施或批准修改。
