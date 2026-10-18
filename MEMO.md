# 相对 AimPaper 的目标修正

本备忘记录：原始 AimPaper 的哪些表述或论证存在问题、项目因此采用什么修正目标，以及修复目前证明到哪一步。它保留在仓库根目录并由 Git 跟踪；逐轮讨论和详细审计放在 `local-history/`。

主目标仍是标准 $h_6^2$ 非零永久存活。下面的局部修正不表示原论文已整体形式化，也不消除已登记的上游待补责任。[AimPaper/main.tex](AimPaper/main.tex) 目前仍保留原文，尚未按这些修正改写。

## 1. Theorem 6.12：广义 Mahowald trick 不能直接消去 λ 层

**原文与问题。** 原文标签 `thm:158d451a`，采用 Notation 2.2、Definition 5.4、Remark 5.7 的约定：素数为 2，谱为 2 完备的 connective finite-type 谱。证明末尾从带层关系

$$
d_n^{\hat f_r}(\lambda^{l_1}x)=\lambda^{r'-1}y
$$

直接消去 $\lambda^{l_1}$；但降层可以杀掉非零边界，原指定源可能不在结论所需微分的定义域。

**反例要点。** 取旋转的 $\nu$ 余纤维三角

$$
S^0\xrightarrow{j}C\nu\xrightarrow{p}S^4\xrightarrow{-\Sigma\nu}S^1,
\quad (e(f),e(g),e(h))=(0,0,1),
\quad(n,m,l,s,t)=(1,0,2,1,16).
$$

令 $x=b=d_2(h_4)=h_0h_3^2\ne0$，其余标签为零，则 $l_1=1$、$r=r'=3$。前提只看到 $b\bmod B_2=0$；而 $\operatorname{Ext}_{\mathcal A}^{2,13}=0$ 保证 $j_2(b)\ne0$，故底层 $d_0^{\hat j_2}(b)\ne0$，阻止所需的 $d_1$。Definition 5.4 的源位于第零层，只模 $B_1=0$，不能改读成经典 $E_3$ 中的零类。

**目标调整与状态。** 不再把消去 λ 当作合法的一般推导。候选修正是额外要求源属于所需微分的定义域：令 $Q=n+m+e(h)$、$F=\hat f_Q$，要求 $x\in Z_Q$ 且底层标签 $x_0\in{}^F Z_{n-1}$；另一方向是保留 $l_1$ 层结论，另证降层引理。候选条件是否足以恢复完整目标同余，仍未证明。

形式化反证为 [StatementReview.lean](KIP126/ProofTools/GeneralizedMahowald/StatementReview.lean) 中的 `rotated_nu_generalized_mahowald_law_false`，前提与非零性见同目录 `RotatedNuPremises.lean`、`BottomNuInjection.lean`。反证依赖既有登记的上游接口，不调用待证 MH2 或 GL。一般 MH2 的公共接口尚未修改，原待补保留；Main 使用 $l_1=0$ 的特例，本反例针对 $l_1=1$。

## 2. Proposition 6.20 第一段：下降必须保留长度合法域

**原文与问题。** 原文标签 `prop:dec738d3`，断言 $d_n^{f,E_r}(x)=y$ 可下降到所有 $2\le r'<r$。但 Definition 5.4 要求 $e(f)\le n\le r'-2+e(f)$。例如 $r=3,n=e(f)+1,r'=2$，晚页合法，早页已超出定义域；这是量化范围问题。

**修正目标。** 在同一个 $f,x,y$ 上下降时补上

$$
2\le r'\le r,\qquad n\le r'-2+e(f).
$$

王老师同意增加条件。修正版已公开为 [finiteExtension_descends](KIP126/ProofTools/Paper/ExtensionDescent.lean:83)，无本地证明洞，仍依赖已登记的上游输入。[审查与验证](local-history/metadata/interface-reviews/ProofTools/20261017-paper-prop620-domain/wang-validation.json)。

## 3. Proposition 6.20 第二段：固定目标的加强版需要修正

**范围与问题。** 原文允许较低目标 $y'$ 及参数 $b$。若要求保持原目标 $y$，分次迫使 $b=0$；在这个加强版中，再要求短源属于早晚 cycle 的严格差集，并不能由早页 inessential 推出。整体修正不可提升，不保证其首项不可提升且能支持到原 $y$ 的短扩张。

反例使用 $E=H\mathbb Z_2^\wedge$、$M=H(\mathbb Z/16)$ 的标准连接 $\delta$，取

$$
X=\Sigma E_x\oplus\Sigma E_u\oplus M,\quad
Y=\Sigma E_z\oplus\Sigma E_{y_0},\quad
f(x)=8y_0,\quad f(u)=2z,\quad f|_M=(\delta,2\delta).
$$

在 $r'=5,r=7,n=3,e(f)=0,(s,t)=(0,1)$ 时，原目标 $y=h_0^3y_0$ 在晚页 essential、早页 inessential；但所有差集候选源都被非零 $d_0$ 阻挡，无法支持所需短扩张。这是经独立审查的纸面实际谱反例，另有有限算术 Lean 核验；当前固定 `ClassicalObject` 尚未表示这些 HZ 对象，故不标为固定 Lean 模型中的形式化谱反例。它也不反驳允许较低目标的一般 $b$ 形式。[反例及适用范围](local-history/metadata/interface-reviews/ProofTools/20261017-prop620-fixed-target-bzero/report.md)。

**已完成的修正一：去掉差集条件。** 王老师于 2026-10-17 明确要求先去掉差集。保留同一 $x,y$ 的合法早晚扩张及晚页 essential，固定 $y,b=0$，则早页 inessential 当且仅当存在 $0<a\le n-e(f)$ 及早循环源 $x'$，满足

$$
x'\in Z_{r'-1-a}^{s+a,t+a}(X),\qquad
d_{n-a}^{\hat f_{r'-1}}(\lambda^a x')=\lambda^{n-e(f)}y.
$$

源仍须支持所写的 ESS 微分；短扩张无需 essential，源类也允许为零。修正版已公开为 [finiteExtension_inessential_iff_shorter](KIP126/ProofTools/Paper/ExtensionIndeterminacy.lean:300)，没有额外增加目标绑定前提。[修改依据与验证](local-history/metadata/interface-reviews/ProofTools/20261017-prop620-remove-difference/report.md)。

**当前采用的修正二：保留差集，增加晚页 crossing 分支。** 王老师随后提出：若晚页 essential、早页 inessential，却不存在满足差集条件的短源，则应存在 crossing。用户已明确要求形式化此版本。

令 $D_y$ 表示上述短式另满足

$$
x'\notin Z_{r-1-a}^{s+a,t+a}(X),
$$

令 $C_{\mathrm{晚}}$ 表示原晚商同一 normalized-map synthetic ESS 中的 crossing。当前结论为

$$
\text{晚页 essential}\ \land\ \text{早页 inessential}
\quad\Longrightarrow\quad D_y\ \lor\ C_{\mathrm{晚}}.
$$

完整范围为 $2\le r'\le r$、$e(f)\le n\le r'-2+e(f)$，并假定同一 $x,y$ 的早晚扩张均已存在。否定 $D_y$ 是否定所有合法见证的存在，不是某个随选短源不满足条件。晚页 crossing 位于同一 stem、weight 和实际晚商映射，滤过范围为 $s<u\le v\le s+n$，靶非零但允许不同于原 $y$。

二择已公开为 [finiteExtension_nonliftableShort_or_lateCrossing](KIP126/ProofTools/Paper/ExtensionCrossingDichotomy.lean:450)，差集分支由同文件的 `FiniteExtensionNonliftableShortTo` 固定。去差集 iff 继续保留；含差集、固定目标且没有 crossing 分支的加强版不标为已证。新二择无 ProofTools 本地证明洞，仍依赖既有上游待补。[最新修改依据](local-history/metadata/interface-reviews/ProofTools/20261018-prop620-crossing-dichotomy/report.md)与[验证](local-history/metadata/interface-reviews/ProofTools/20261018-prop620-crossing-dichotomy/validation.json)。

**尚未跨越的边界。** 此 crossing 尚未直接识别为 Definition 5.9 的经典有限页 crossing；原文一般 $b$ 版本的完整 iff 也未由上述结果证明。升页推论实际编号为 6.23（6.21 是公式号），其升页存在性不能从已经假定晚页扩张存在的二择直接推出。

## 推论 1.5：第二线分类的接口与证明边界（2026-10-18）

用户已授权补齐其上游接口并完成 Main 的组合证明。完整分类由 `Main.adams_two_line_classification` 给出，陈述仍是实际球面第二线上任意元素非零存活当且仅当属于原文清单，没有额外调用者前提。文献存活及排除结论归 Literature，无界 E₂ 基底归 E2Computation，首次微分后的候选筛选归 AdamsCalculations；Main 不接手这些上游待补证明。

原文在第三页候选清单中提前印出平方指标 $j\le6$。形式化按逻辑阶段拆开：$d_2$ 候选保留全部 $h_j^2$，再单独用 HHR 排除 $j\ge7$，不把最终截断当成第三页计算输入。八项文献来源/对象比较、一项 E₂ 基底比较及一项 Adams 候选计算是本次新增的十项待补责任；Main 组合证明没有本地证明洞，整体仍待这些上游责任及既有责任补齐。此次后续来源核查已定位 May 1964 原始博士论文，并与原 bibliography 中实际对应 1966 代数论文的 `Maythesis` 区分。各项直接来源及仍待核验的原始定位由 Blueprint 维护，引用核查不等于上游 Lean 证明完成。

**来源核查发现的接口错误。** 原文及上一轮新增的第三页候选清单遗漏了 $h_0h_4$。Lin Theorem 1.3(1) 给出 $h_0^2h_3^2=0$，由 Adams 微分及 Leibniz 有 $d_2(h_0h_4)=0$；IWX Table 6，p. 222，首行明确给出非零 $d_3(h_0h_4)=h_0d_0$。因此上一轮 `AdamsCalculations.two_line_d2_candidates` 在所声称的经典 Adams 对象上不成立，当时依赖它的 Main 组合证明不能称为已有正确上游支持的完整证明。上一轮只去除了平方指标的提前截断，没有独立检查全部混合乘积，这是本次发现的遗漏。

用户随后明确回复“批准，按此修正”。已据此在公共候选谓词补入 $(0,4)$；Literature 新增实际双次数 $(2,17)\to(5,19)$ 的非零 $d_3$ 接口 `iwx_h0_h4_d3`；Main 增加第四条混合项排除分支。最终永久存活分类及 Main 公共定理类型不变，新增一项独立的上游待补责任（309→310），并保留此前全部责任；Main 不新增本地证明洞。修正后的筛选与实际模型比较仍是上游待补，引用核查和有限检验不能替代全指标形式证明。批准范围与独立依据见 [接口复核](local-history/reports/two-line-source-alignment-2026-10-18/interface-review.md)，来源及实施验证见 [本次记录](local-history/reports/two-line-source-alignment-2026-10-18/report.md)。
