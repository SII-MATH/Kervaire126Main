# 原论文备忘

记录原论文阅读与形式化过程中发现的问题、反例及修正方向。条目注明版本、原文位置和验证状态。

## 2026-10-16：广义 Mahowald trick 的降层障碍

**对象与出处。** 沿用原文的约定：素数为 2，所有谱均为 2 完备的 connective finite-type 谱。讨论 Lin–Wang–Xu, *On the Last Kervaire Invariant Problem*, [arXiv:2412.10879v2](https://arxiv.org/html/2412.10879v2) 的 Theorem 6.12。仓库原文见 [AimPaper/main.tex](AimPaper/main.tex)，标签 `thm:158d451a`；相关定义为 Notation 2.2、Definition 5.4、Remark 5.7。

### 反例

旋转同伦元素 $\nu:S^3\to S^0$ 的余纤维三角：

$$
X=S^0\xrightarrow{f=j}Y=C\nu\xrightarrow{g=p}Z=S^4
\xrightarrow{h=-\Sigma\nu}\Sigma X=S^1.
$$

取

$$
(e(f),e(g),e(h))=(0,0,1),\qquad
(n,m,l,s,t)=(1,0,2,1,16).
$$

于是 $(n_1,m_1,l_1)=(1,0,1)$，$r=r'=3$。令

$$
x=b=d_2(h_4)=h_0h_3^2\ne0\in E_2^{3,17}(S^0),
\qquad \bar x=y=\bar y=0.
$$

其中 $\bar x\in E_2^{1,16}(S^4)$、$y\in E_2^{4,18}(C\nu)$、$\bar y\in E_2^{4,18}(S^4)$，而 $h$ 的目标为 $\Sigma b\in E_2^{3,18}(S^1)$。所有 cycle 条件成立，四项前提分别为：

1. $h$-延拓的目标 $\lambda\Sigma b$ 位于 $Z_1/B_2$，因 $b\in B_2$ 而为零，故 $d_2^{\hat h_2}(0)=\lambda\Sigma b=0$。
2. $d_3(0)=0$。
3. 采用 Adams 微分的 no-crossing 分支。按 Definition 4.14，唯一可能的 crossing 是从 $E_2^{2,17}(S^4)\cong\operatorname{Ext}_{\mathcal A}^{2,13}(\mathbb F_2,\mathbb F_2)=0$ 出发的 $d_2$，故不存在。
4. $d_0^{p,E_2}(0)=0$。

### 结论不成立

原结论要求存在 $y'\equiv0\pmod{B_3}$，使 $d_1^{j,E_3}(b)=y'$。但余纤维的 Ext 长正合序列包含

$$
\underbrace{\operatorname{Ext}_{\mathcal A}^{2,17}
(\Sigma^4\mathbb F_2,\mathbb F_2)}_{
\operatorname{Ext}_{\mathcal A}^{2,13}(\mathbb F_2,\mathbb F_2)=0}
\longrightarrow E_2^{3,17}(S^0)
\xrightarrow{j_2}E_2^{3,17}(C\nu).
$$

故 $j_2(b)\ne0$。在 $\nu(-)/\lambda^2$ 的底权上，synthetic $E_\infty$ 为 $Z_2/B_1=Z_2$，于是 $d_0^{\hat j_2}(b)=j_2(b)\ne0$。因此 $b$ 不在所需 $d_1$ 的定义域中，与目标如何修正无关。

Definition 5.4 明确取源的 $k=0$ 层，即源只模 $B_1=0$；不能将这个源改读成经典 $E_3=Z_2/B_2$ 中的零类。故此例直接适用于原文明示的定义。

### 修正方向与验证状态

建议在原四项之外增加候选条件 **（5）源已属于所需延拓微分的定义域**：令 $Q=n+m+e(h)$、$F=\hat f_Q$，要求 $x\in Z_Q(X)$，且其底层 synthetic 标签 $x_0\in{}^F Z_{n-1}$。本例 $n=1$ 时，这恰要求 $j_2(b)=0$。

条件（5）排除此反例；它是否足以恢复一般情形的完整目标同余，仍需证明。另一方向是保留 $l_1$ 层延拓，将降层单列为引理。可对照 [Wu, arXiv:2606.02779v2](https://arxiv.org/pdf/2606.02779v2) 的 Theorem 4.23 与 Remark 4.25；后者的降层另要求 $f_2(x)=0$ 及边界商条件。

形式化反证为 [StatementReview.lean](KIP126/ProofTools/GeneralizedMahowald/StatementReview.lean) 中的私有定理 `rotated_nu_generalized_mahowald_law_false`；前提与非零性分别见同目录 `RotatedNuPremises.lean`、`BottomNuInjection.lean`。反证调用既有登记的上游接口，不调用待证 MH2 或 GL。代码已收入提交 `b4b439f`；公共接口未修改，MH2 的原始 `sorry` 保留。Main 当前使用的实例为 $l_1=0$，本反例为 $l_1=1$。

### 发现思路

补写 MH2 时，证明推进到带层关系

$$
d_n^{\hat f_r}(\lambda^{l_1}x)=\lambda^{r'-1}y.
$$

原证明末尾直接消去 $\lambda^{l_1}$。检查这一步时，注意到商映射

$$
\lambda:Z_2^{3,17}/B_1^{3,17}\longrightarrow Z_2^{3,17}/B_2^{3,17}
$$

杀掉非零的 $b=d_2(h_4)$。于是取 $l_1=1$，让 $h$-前提只看见 $b\bmod B_2=0$；再选旋转的 $\nu$ 三角，使底映射在 $b$ 上单射。取其余标签为零后，前提成立，而结论的指定源被最低延拓微分阻挡。问题定位在原文证明末尾的 “by dividing $\lambda^{l_1}$” 步骤（本地 `main.tex` 第 1913 行）。

## 2026-10-17：命题 6.20 的早页下降遗漏合法域条件

**版本与出处。** 仓库固定的 [AimPaper/main.tex](AimPaper/main.tex:1981)，标签 `prop:dec738d3`；该文件 SHA-256 为 `828ee5a5aa06e1f390b036a043230ed417446fa7be11a4e27eecc4a565135c4b`。本条针对自然语言原文的第一段，不将问题归为实际谱上自然性失败。

**原文问题。** 第一段断言：给定 $d_n^{f,E_r}(x)=y$，对所有 $2\le r'<r$ 都有 $d_n^{f,E_{r'}}(x)=y$。但 [Definition 5.4](AimPaper/main.tex:1301) 只在 $e(f)\le n\le r-2+e(f)$ 时定义这种页扩张。固定长度 $n$ 下降到更早页时，原文没有保证它仍在定义域内。

例如取 $r=3$、$n=e(f)+1$、$r'=2$：晚页长度合法，早页却要求 $e(f)+1\le e(f)$。第一段不要求 essential，故可用合法晚页上的零扩张核验这一字面范围冲突。形式化证据见 [DescentRangeCounterexample.lean](metadata/interface-reviews/ProofTools/20261017-paper-prop620-domain/evidence/DescentRangeCounterexample.lean)，不应据此声称论文的拓扑结论或主定理为假。

**修正与状态。** 将第一段的量化范围改为

$$
2\le r'<r,\qquad n\le r'-2+e(f).
$$

用户转述王老师的回复为“1 增加条件”，据此已公开 [finiteExtension_descends](KIP126/ProofTools/Paper/ExtensionDescent.lean:83)，保持同一个 $f,x,y$。默认 `lake build` 通过（3087 个任务）；新增定理无本地证明洞，仍依赖已登记上游责任，详见 [验证记录](metadata/interface-reviews/ProofTools/20261017-paper-prop620-domain/wang-validation.json)。论文原文文件尚未改写。

**第二段另待确认。** 用户还转述“$y'$ 应该是 $y$ 吧？”；保留 $b>0$ 时，$d_{n-a'-b}(\lambda^{a'}x')$ 的靶分次为 $(s+n-b,t+n-b)$，而原 $y$ 在 $(s+n,t+n)$，乘 $\lambda$ 不改变这两个分次。直接替换只有在 $b=0$ 时齐次；即使限制 $b=0$，带非 liftable 源条件的完整 iff 仍未证明。此项记录为表述与证明待确认，不标为已证反例或已完成修正，见 [独立核验](metadata/interface-reviews/ProofTools/20261017-paper-prop620-domain/evidence/wang-correction-audit.md)。

### 后续：王老师回复后的固定目标补证与反例核验

已读取[群内原回复](https://applink.feishu.cn/client/chat/open?openChatId=oc_0757f47818759dc02c05b8dd370aa649&position=1481)：“一般的b，可以推b=0”。固定原 $y$ 时，分次确实迫使 $b=0$；这一观察与下述问题不同：早页非本质性，是否保证能选到一个**首项不属于晚页 cycle、且仍命中原 $y$**的短扩张。

本轮已用 Lean 证明固定目标的非本质性／高源滤过代表判据（5 条），并证明模同一边界分母时，余类可提升当且仅当代表属于晚页 cycle（2 条）。这些局部结果无 `sorryAx`，只保存在[证据目录](metadata/interface-reviews/ProofTools/20261017-paper-prop620-domain/evidence/WangBzeroExactTarget.lean)，未作为完整 6.20 接口公开。

继续提取非提升首项时，得到以下纸面谱反例构造。令 $E=H\mathbb Z_2^\wedge$、$M=H(\mathbb Z/16)$，$\delta:M\to\Sigma E$ 为标准连接，取

$$
X=\Sigma E_x\oplus\Sigma E_u\oplus M,\quad
Y=\Sigma E_z\oplus\Sigma E_{y_0},\quad
f(x)=8y_0,\quad f(u)=2z,\quad f|_M=(\delta,2\delta).
$$

参数为 $r'=5,r=7,n=3,e(f)=0,(s,t)=(0,1)$，原目标为 $y=h_0^3y_0$。归一化 $16$ 三角在有限 $\lambda^q$ 商中的连接像是 $K_q=\ker(8:\mathbb Z/2^q\to\mathbb Z/2^q)$，故 $K_4=2\mathbb Z/16$、$K_6=8\mathbb Z/64$。实际映射的坐标为

$$
(\alpha,\beta,c)\longmapsto(2\beta+c,\;8\alpha+2c),\qquad c\in K_q.
$$

晚页高源像的 $y_0$ 坐标均为 16 的倍数，原目标 $(0,8)$ 因而 essential；早页高源 $(0,-2,4)$ 恰映到 $(0,8)$，使其 inessential。但所有非提升首项只能在 $a=1,2$ 含非零 $v$ 分量，先有非零 $d_0$ 命中 $z$，不能支持所需的正长度 $d_{3-a}$ 到原 $y$；$a=3$ 全部可提升。这个机制说明：**整体修正不可提升，不推出首项不可提升**。

[独立证明审查](metadata/interface-reviews/ProofTools/20261017-paper-prop620-domain/evidence/wang-bzero-audit.md)逐项核对了实际谱、$\nu\delta$、$\rho$ 和 Adams 滤过，并将其认定为固定原目标／$b=0$／保留非提升源条件版本的纸面实际谱反例；另有[接口人审报告](metadata/interface-reviews/ProofTools/20261017-prop620-fixed-target-bzero/report.md)。HZ 的实际 Adams 输入见 [May–Milgram，Lemma 3、4](https://math.uchicago.edu/~may/PAPERS/34.pdf)。有限算术另有 9 条 Lean 核验，但当前 `ClassicalObject` 尚未表示这些 HZ 对象，故**不是固定 Lean 模型中的形式化谱反例**。

因此未将完整固定目标 iff 标为已证，未新增公理、`sorry` 或待补责任，也未擅自删除非提升条件。首段合法域下降不受影响。验证及依赖范围见 [wang-bzero-validation.json](metadata/interface-reviews/ProofTools/20261017-paper-prop620-domain/wang-bzero-validation.json)；本轮完整构建通过（3087 个任务）。

**一般 $b$ 的具体见证。** 王老师随后指出早页目标被短微分命中；这正是上面的 $d_2^{\hat f_4}(\lambda h_0u)=\lambda^3h_0^3y_0$。沿原文第二种情形迭代，本例还能取 $a'=2,b=1,x'=h_0^2v,y'=h_0^2z$，有 $x'\in Z_2^{2,3}(X)\setminus Z_4^{2,3}(X)$ 及 $d_0^{\hat f_4}(\lambda^2h_0^2v)=\lambda^2h_0^2z$。其代表 $(0,0,4)$ 映到 $(4,8)$，首项是 AF2 的 $4z$。因此本例不反驳允许较低目标的一般 $b$ 形式的必要方向；反例范围始终限于固定原 $y$ 的加强版。这一见证也不证明一般 iff，后者仍需明确 $y'$ 与原目标的关联及证明两方向。已在群里据此回应并请王老师澄清。

**固定目标疑问的进一步排除。** 针对王老师“固定 $y$，$b=0$ 究竟哪里不对”，已重新独立核对第2节记号约定：即使扩张 inessential，写 $d_m(\xi)=\eta$ 仍要求 $\xi\in Z^{\mathrm{ESS}}_{m-1}$。本例 $a'=1,2$ 的所有差集源（包括同次 $x/u$ 混合及任意高源修正）在早页都有非零 $d_0$ 命中 $z$，因此分别不能支持所需 $d_2,d_1$；$a'=3$ 的差集为空。原目标成为短边界不能免除这个源存活条件。完整逐项审查见 [fixed-y-bzero-final-audit.md](metadata/interface-reviews/ProofTools/20261017-prop620-fixed-target-bzero/evidence/fixed-y-bzero-final-audit.md)，并已在群里回复；全程未要求右边的短微分在晚页存在。

### 王老师确认的后续修改：先去掉差集条件

王老师于 2026-10-17 15:06 UTC [明确回复](https://applink.feishu.cn/client/chat/open?openChatId=oc_0757f47818759dc02c05b8dd370aa649&position=1496)：“把差集条件先去掉”。用户随后要求核对意见后继续补证，并明确要求将这一修改计入 memo。原消息另存为 [wang-remove-difference-feedback.json](metadata/interface-reviews/ProofTools/20261017-prop620-fixed-target-bzero/evidence/wang-remove-difference-feedback.json)。

本轮采用的修正版保留早页循环条件 $x'\in Z_{r'-1-a'}^{s+a',t+a'}(X)$，删除 $x'\notin Z_{r-1-a'}^{s+a',t+a'}(X)$；固定原目标 $y$，取 $b=0$。保留原有效早晚扩张及晚页 essential 的前提，结论为

$$
\text{早页原扩张 inessential}\quad\Longleftrightarrow\quad
\exists\,0<a'\le n-e(f),\quad
x'\in Z_{r'-1-a'}^{s+a',t+a'}(X),\quad
d_{n-a'}^{\hat f_{r'-1}}(\lambda^{a'}x')=\lambda^{n-e(f)}y.
$$

源仍须存活到所写的早页 ESS 微分页；不将差集删除理解为删除源的存活要求。短式无需额外要求 essential，源类也未额外要求非零。修正版已补证并经普通公共入口消费，公开为 [finiteExtension_inessential_iff_shorter](KIP126/ProofTools/Paper/ExtensionIndeterminacy.lean:300)；实际源标签另由 finiteExtensionCorrectionLabel 定义。证明内部从同一 $y$ 的代表唯一性导出 $\rho$ 相容，没有添加目标绑定前提。最短长度 $n=e(f)$ 的空候选范围已处理；$n>e(f)$ 时正向可取 $a'=1$。

独立全 import-all 审查核对主定理 822 个项目常量、38 项既有上游待补，无 Main 依赖或 ProofTools 本地证明洞；没有新增公理、sorry 或责任。普通导入视图的 602/28 仅为隐藏证明体后的下界，不当成完整依赖数。完整构建通过（3088 项），源清单覆盖 481 个项目文件、28 个消费/审计文件；原有 113 个导出记录及 299 项待补清单保持不变。验证见 [本次记录](metadata/interface-reviews/ProofTools/20261017-prop620-remove-difference/validation.json)。论文原文尚未改写，原始含差集版本与此次修正版分别记录；既有 stretching 的非提升 crossing 谓词未改。

### 最新版：保留差集，增加晚页 crossing 分支

王老师随后提出：“原先差集的版本，写，若晚diff本质，早diff不本质，且不满足差集条件，则一定存在crossing”。[原消息](https://applink.feishu.cn/client/chat/open?openChatId=oc_0757f47818759dc02c05b8dd370aa649&position=1500)发表于北京时间 2026-10-17 23:49；用户于本轮明确要求将这一最新版记入 memo 并形式化。原话快照及后续审查统一放在 [新记录目录](metadata/interface-reviews/ProofTools/20261018-prop620-crossing-dichotomy/)。

记 D_y 为存在合法位移 0<a≤n−e(f) 及经典源 x′，满足早循环与晚循环的严格差集条件，并在同一早商支持到固定原 y、b=0 的短扩张；记 C_晚 为原晚页同一 normalized-map ESS 中的 crossing。目标为：晚页原扩张 essential 且早页原扩张 inessential，推出 D_y 或 C_晚；等价地，若不存在任何 D_y 见证，则存在 C_晚。这里否定的是存在量词，不是检查某一个随选短源是否可提升。

其中完整页范围为 2≤r′≤r、e(f)≤n≤r′−2+e(f)，并假定同一 x、y 的早晚两个扩张都已存在。第一分支的短式明确为

$$
d^{\hat f_{r'-1}}_{n-a}(\lambda^a x')=\lambda^{n-e(f)}y,\qquad
x'\in Z_{r'-1-a}^{s+a,t+a}(X)\setminus Z_{r-1-a}^{s+a,t+a}(X),\quad 0<a\le n-e(f).
$$

晚页 crossing 则是在同一 stem、weight 和实际晚商映射中，存在 s<u≤v≤s+n 的扩张到非零目标；该目标允许与原 y 不同。它不是声称原 y 能从这个更高源提升。

新结论首先严格落在晚页 synthetic ESS 的 crossing 层次，不直接等同于定义 5.9 的经典有限页 crossing。证明先由固定目标的代表唯一性得到早页原靶非零，再在有限滤过范围中取最高的修正源，提取到同一原靶的 essential 短扩张。如果其经典源属于晚循环层，通过实际有限商的 ρ、商与 shift 相容性，把它提升为晚商的 E∞ 首项；晚页无 crossing 将迫使该首项的像进入比原靶更高的滤过，产生到零靶的同源短式，与短扩张 essential 矛盾。新增二择已形式化并通过普通公共入口公开为 [finiteExtension_nonliftableShort_or_lateCrossing](KIP126/ProofTools/Paper/ExtensionCrossingDichotomy.lean:450)，差集分支由 [FiniteExtensionNonliftableShortTo](KIP126/ProofTools/Paper/ExtensionCrossingDichotomy.lean:29) 精确固定；已完成的去差集 iff 保留，原含差集且没有 crossing 分支的固定目标加强版不标为已证。升页推论实际编号为 6.23（此前误称 6.21，后者是公式号），其升页存在性不能从此已假定晚页扩张存在的二择直接推出。

本次完整 import-all 审计核对二择定理 929 个项目常量、38 项既有上游待补，责任集合与上一版 iff 相同；没有 Main 依赖、ProofTools 本地证明洞或新增公理。原有 116 条公共导出记录逐条保持不变，追加 2 条数学公共声明及 4 条 Lean 自动生成证明项（其中 2 条是既有定义展开方程）；299 项待补清单的字节与全部类型、证明体指纹保持不变。公共入口及普通消费检查已通过，源清单覆盖 483 个项目文件、28 个消费/审计文件。默认完整构建通过（3090 项）；最终状态见 [validation.json](metadata/interface-reviews/ProofTools/20261018-prop620-crossing-dichotomy/validation.json)。
