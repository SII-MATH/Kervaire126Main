---
result_id: '20261022-theta5-products'
title: 'θ₅ 的乘法滤过与平方选择不变性'
summary: '在列明的经典 Adams 输入下，证明 a₆² 属于 F¹⁴、θ₅·F⁶π₆₂ 包含于 F¹³π₁₂₄，并得到八种 θ₅ 选择的平方模 F¹⁴ 相同；固定平方的 AF10 系数仍未确定。'
topic: 'theta5'
status: 'reviewed-informal'
evidence_level: '基于列明的经典文献、有限 Adams 数据和只读代数证书的非形式化推导，已经独立 agent 逐行复核；未重建全部源计算。'
formalization_status: 'not-formalized'
novelty_status: 'not-established'
baseline_commit: '34fb925fd3c30304832e40e1c87938ff00908b67'
updated: '2026-10-22'
authors: ['/root/memory_failure_audit', '/root']
reviewers: ['/root/strong_kervaire_audit']
---

# θ₅ 的乘法滤过与平方选择不变性

本文合并两轮研究中已通过独立审查的结果。全部同伦群均指经典
2-完备球谱的稳定同伦群；在所讨论的正维有限群中，与 2-primary 部分一致。
用 \(F^s\pi_k\) 表示递减、乘法相容的模 2 Adams 滤过，
\(E_r^{s,t}\) 的 stem 为 \(t-s\)。所有 Toda 括号均为经典稳定 Toda 括号。

这是一份供人审的非形式化数学报告。它有完整的局部证明、列明的上游输入和
独立复核，尚未成为 Lean 定理，也没有完成源数据库全部微分的链级验证。
文献新颖性已于 2026-10-22 按下列范围核查，尚未确认原创性。
没有由本轮结果算出固定 \(\theta_5^2\) 的 AF10 系数，
也没有据此确定一个原先未知的实际谱序列微分。

## 0. 文献新颖性核查

本报告不能整体称为新定理。可继续考察的增量仅是 AF6 方向的两个精确滤过界；
平方选择不变性的加强是其中一个界的推论。以下判断仍以第 2 节的全部数学输入为前提。

| 本报告结论 | 与已读文献的关系 | 本次判断 |
| --- | --- | --- |
| \(\theta_5^2\) 的 AF10 分量与选择无关 | LWX Lemma 7.10 已证明平方差属于 \(F^{12}\)；同节的滤过空档还给出 \(F^{12}=F^{13}\) | 文献已有，不能作为本报告的新结果 |
| \(a_6^2\in F^{14}\pi_{124}\) | LWX 的选择比较只需要 \(F^{12}\)，结合空档到 \(F^{13}\)；在已核对的 LWX、BX、IWX、Xu 与 Wang--Xu 原文中未找到这个更强界的直接陈述 | 候选局部加强，原创性未确认 |
| \(\theta_5a_6\in F^{13}\pi_{124}\) | BX 已使用四重括号乘积及 Moss 方法研究 \(\theta_5^2\)；本报告将左输入换为 AF6 代表并控制全部不定性。未找到这一指定混合积滤过界的直接陈述 | 候选具体应用，方法本身已有，原创性未确认 |
| \(\theta_5\cdot F^6\pi_{62}\subseteq F^{13}\pi_{124}\) | AF8 方向所需 Ext 零乘积已明写于 LWX；AF10 方向由乘法滤过及 \(F^{12}=F^{13}\) 直接推出。需要额外论证的只有 AF6 方向 | 不能把全部三个方向分别算成新结果 |
| 八种 \(\theta_5\) 的平方模 \(F^{14}\) 一致 | 比 LWX 的模 \(F^{12}\) 界强；本报告由 \(a_6^2\in F^{14}\)、其他方向的乘法滤过和指数二群结构推出 | 候选加强的推论，不是另一项独立发现 |

可复核的主要文献定位如下。源码行号只用于定位随版本固定的原件，不代替文章引用。

1. Lin--Wang--Xu, [On the Last Kervaire Invariant Problem, arXiv:2412.10879v2](https://arxiv.org/abs/2412.10879v2)，Lemma 7.10，预印本 p. 45，`main.tex:2221–2239`：平方选择的误差在 AF 至少 12。Lemma 7.16 的证明末段，p. 51，`main.tex:2560–2564` 明列 \(h_5^2(\Delta e_1+C_0+h_0^6h_5^2)=0\)；`main.tex:2254` 及附录 `Table:S124.12` 给出所用滤过空档。Question 1.7，p. 3，仍问是否存在平方为零的 \(\theta_5\)。
2. Burklund--Xu, [The Adams differentials on the classes \(h_j^3\), arXiv:2302.11869v3](https://arxiv.org/abs/2302.11869v3)，§7.2 的 Proposition 7.19、Theorem 7.20（预印本 p. 54）及证明（pp. 54–56），`kervairev2.tex:588–690`。其中明确使用 \(\theta_5\langle2,\theta_4,\theta_4,2\rangle\) 与嵌套 Toda 括号；不能把本报告使用这种方法本身称为创新。
3. Isaksen--Wang--Xu, [Stable homotopy groups of spheres: From dimension 0 to 90, arXiv:2001.04511v3](https://arxiv.org/abs/2001.04511v3)，群表、Toda 括号表及随附经典图表；Xu, [The strong Kervaire invariant problem in dimension 62, arXiv:1410.6199v1](https://arxiv.org/abs/1410.6199v1)，Theorem 1.2、Corollary 1.3；Wang--Xu, [The triviality of the 61-stem, arXiv:1601.02184v4](https://arxiv.org/abs/1601.02184v4)，Theorem 1.9、Corollary 1.10。它们提供本报告的群、低维乘积及四重括号输入，没有据此独立宣称 124-stem 的上述两个新滤过界。
4. May, [A brief note on the Hopf and Kervaire invariant one problems, arXiv:2609.18942v1](https://arxiv.org/pdf/2609.18942v1#page=2)，p. 2 仍明确写出 \(\theta_5^2=0\) 未知。这个近时说明支持主平方问题仍未由所引工作解决，不证明本报告的局部加强是首次出现。

检索日期为 2026-10-22。已核对上述本地全文与 arXiv 返回的版本，并检查
`all:Kervaire AND cat:math.AT` 的全部 69 条返回记录及 `all:"strong Kervaire"`
的 3 条记录，筛选相关近期工作后阅读原文；这不是对所有数学文献的全文穷尽检索。
BJM 1983、1984 原始论文的全文本次未能取得，只能通过 BX、Xu 等文献核对相关引用；
没有覆盖作者未公开的计算和口头已知结果。核查范围与版本记录见
[本次检索记录](evidence/novelty-search-20261022.json)。因此目前只可称为
“在已读文献中未找到直接先例的两个具体滤过加强”，不可称为已确认的文献新发现。
本节由 `/root` 汇总，θ₅ 文献对照由 `/root/memory_failure_audit` 复核，
近期相邻结果由 `/root/strong_kervaire_audit` 独立复核。

## 1. 完整数学结论

令 \(\theta_5\in\pi_{62}\) 为任意由 \(h_5^2\) 检测的类，
\(a_6\in\pi_{62}\) 为任意由 \(h_5n\) 检测的类。相对于第 2 节列明的输入，
有

\[
 a_6^2\in F^{14}\pi_{124},\qquad
 \theta_5a_6\in F^{13}\pi_{124},\qquad
 \theta_5\cdot F^6\pi_{62}\subseteq F^{13}\pi_{124}.
\]

此外，任意两种 \(h_5^2\) 检测的选择满足

\[
 (\theta_5')^2-\theta_5^2\in F^{14}\pi_{124}.
\]

因此八种 \(\theta_5\) 选择的平方模 \(F^{14}\) 相同。
\(a_6^2\) 在 \(F^{13}/F^{14}\) 中、相对于检测类
\(e_0\Delta h_6g\) 的系数为零。这不意味着 \(a_6^2=0\)，也不把界提高到
\(F^{15}\)。共同的 \(\theta_5^2\) 在 \(F^{10}/F^{11}\) 中的系数以及
更高滤过部分仍未确定。

## 2. 对象、前提与来源

下表是证明所调用的数学输入。有限数据库证书验证了记录间的代数关系，
不把数据库行本身升级为源定理的形式证明。

| 输入 | 精确内容 | 来源定位 |
| --- | --- | --- |
| 实际的 \(n\) | 选择检测于 \(n\in E_2^{5,36}\) 的 \(n\in\pi_{31}\)，满足 \(2n=0\)；全文固定该选择 | IWX 的已定义括号 \(\langle\{n\},2,\theta_5\rangle\)，`more-stable-stems-tables.tex:691,1163`；经经典 realization 使用 |
| 实际的 \(\theta_4\) | \(\theta_4\in\pi_{30}\) 检测于 \(h_4^2\)，且 \(2\theta_4=0\)、\(\theta_4^2=0\) | Xu，`theta5_arxiv.tex:118,129,194–213` |
| stem 61 | \(\pi_{61}=0\) | Wang–Xu，*The triviality of the 61-stem in the stable homotopy groups of spheres*，Theorem 1.9，印刷页 504 |
| 四重括号 | 存在检测于 \(h_5^2\) 的 \(\theta\in\langle2,\theta_4,\theta_4,2\rangle\)，括号严格定义 | Wang–Xu Corollary 1.10；Burklund–Xu 当前证明 `kervairev2.tex:621–628` 使用的四重括号乘积包含式 |
| stem 31 | \(\pi_{31}\) 由 \(\eta\theta_4,n,\rho_{31}\) 生成，对应滤过为 3、5、11；特别地 \(\pi_{31}=F^3\pi_{31}\) | Xu `theta5_arxiv.tex:419`；IWX 经典表 |
| stem 62 | \(\pi_{62}\cong(\mathbb Z/2)^4\)，四个滤过方向为 2、6、8、10，检测类为 \(h_5^2,h_5n,\Delta e_1+C_0,R\) | IWX 经典群与图表；AimPaper `main.tex:2234–2239` |
| stem 63 | \(\pi_{63}=F^3\pi_{63}\)，grade 3 只有 \(h_1h_5^2\)，检测 \(\eta\theta\) | 完整低滤过微分与 IWX 经典 \(E_\infty\) CSV |
| stem 93 | \(F^6\pi_{93}=F^{10}\pi_{93}\) | IWX 随附经典图表覆盖至 stem 95；cw49 与 cw210 有限微分复核 |
| stem 124 | \(\pi_{124}=F^{10}\pi_{124}\)，\(F^{11}=F^{12}=F^{13}\)；grade 10 只有非零 \(c=h_0^2x_{124,8}\) | AimPaper 完整表 `Table:S124.12`，`main.tex:2963–2993`；\(c\) 非零明确见 Fact `theta5sqAF(3)`，2164 行及表 2978 行 |
| 收敛与括号 | 强收敛、Moss 收敛定理的实际 crossing 条件、允许零检测的高页 Massey 约定、完整三重 shuffle 等式 | Moss，*Secondary compositions and the Adams spectral sequence*，Theorem 1.2、(1.3)，印刷页 285；IWX `more-stable-stems-background.tex:458–487,607–616,844–891` |

不能把“选择一个 \(2n=0\) 的代表”改读成“该检测陪集的每个代表均由同一来源保证”。
IWX 的 stem 93 输入来自其随附经典图表，而非把正文只声明到 stem 90 的群表定理外推。
本文四重括号公式引用 Burklund–Xu 当前有效证明，未采用注释掉的旧草稿。

必要的 Ext 等式为

\[
 h_0n=0,\quad d_1h_4^2=0,\quad nh_4^2=0,\quad
 d_2(h_5)=h_0h_4^2,
\]
\[
 h_1h_5^2h_4^2=0,\qquad
 h_5^2(\Delta e_1+C_0+h_0^6h_5^2)=0.
\]

第二行后一因子是数据库所选 AF8 生成元的精确表达式。在
\(E_2^{10,103}\) 中，完整基为

\[
 x_{93,10},\quad h_1^2x_{91,8},\quad h_0^3\Delta h_2^2h_6,
\]

三者乘 \(h_4^2\) 均为零。中间项为此滤过的经典永久类，另两项分别被
\(d_2\)、\(d_6\) 杀掉。证明使用整个 Ext 度数的零乘积，不依赖挑选方便代表。
这些关系及所需完整基均保存在有限证书中。

## 3. 校准 AF6 的实际 Toda 代表

固定上述 \(n,\theta_4\)。在 \(E_3\) 上，

\[
 \langle n,h_0,h_4^2\rangle=\{h_5n\}\subset E_3^{6,68}.
\]

在前一页用 0 作为 \(nh_0\) 的定义零化，用 \(h_5\) 零化
\(h_0h_4^2\)，得到 \(h_5n\)。左不定性为
\(E_3^{4,36}h_4^2\)，唯一可能生成元 \(d_1\) 的乘积为零；右不定性为
\(nE_3^{1,32}=0\)，因为 \(h_5\) 支持非零 \(d_2\)。所以是单元素集合。

对滤过 \(f\)、stem \(v\) 的乘积，在 \(E_r\) 应检查的 crossing 源位于
stem \(v+1\)，滤过 \(q<f-(r-1)\)，相关较后微分的目标滤过严格大于 \(f\)。
本次两个窗口如下：

| 乘积 | 页 | 完整源窗口 | 检查结果 |
| --- | --- | --- | --- |
| \(nh_0\) | \(E_3\) | stem 32，\(q<4\) | 只有 \(q=2\) 的永久类 \(h_1h_5\) |
| \(h_0h_4^2\) | \(E_3\) | stem 31，\(q<1\) | 空 |

Moss 因此给出实际的

\[
 \alpha\in\langle n,2,\theta_4\rangle,\qquad AF(\alpha)=6.
\]

由 \(2\theta_4=\theta_4^2=0\)，括号
\(\langle2,\theta_4,\theta_4\rangle\subset\pi_{61}\) 已定义且等于 \(\{0\}\)。
完整 shuffle 等式给出

\[
 \langle n,2,\theta_4\rangle\theta_4
 =n\langle2,\theta_4,\theta_4\rangle=\{0\},
\]

故 \(\alpha\theta_4=0\)。又因 \(\pi_{62}\) 指数为 2，\(2\alpha=0\)。

## 4. 平方属于 F14 的证明

令 \(B=\langle2,\theta_4,\alpha\rangle\subset\pi_{93}\)。上节保证它定义。
第二次 shuffle 给出某个 \(\beta_0\in B\)，使

\[
 \alpha^2=\pm n\beta_0.
\]

在 \(E_4\) 对输入 \(h_0,h_4^2,h_5n\) 应用 Moss。
相邻乘积已在 \(E_3\) 为零，输出度数为

\[
 (1,1)+(2,32)+(6,68)-(3,2)=(6,99).
\]

乘积 \(h_0h_4^2\) 的 crossing 窗口为空。
另一乘积滤过为 8、stem 为 92，源窗口是 stem 93 的 \(q<5\)。
唯一非空方向为 \(h_4^2h_6\) 与 \(h_0h_4^2h_6\)，滤过分别为 3、4，
均支持非零 \(d_4\)，目标为 \(h_0^3g_3,h_0^4g_3\)；它们不再出现在
Moss 条件检查的较后页中。于是某个 \(\beta_1\in B\) 属于 \(F^6=F^{10}\)。

这里不能直接在 \(E_3\) 作同样应用：
\(d_4(h_0^2h_4^2h_6)=h_0^5g_3\) 是真实 crossing。
改用 \(E_4\) 同时把保证的滤过由 7 降为 6，并缩小源窗口，符合原定理。
零 Massey 定义值只意味着存在具有相应滤过下界的括号成员，不表示该同伦成员是零。

完整不定性为

\[
 B-B=2\pi_{93}+\pi_{31}\alpha.
\]

乘 \(n\) 后，第一项因 \(2n=0\) 消失；第二项属于
\(F^{5+3+6}=F^{14}\)。而 \(n\beta_1\in F^{15}\)。因此

\[
 \alpha^2\in n\beta_1+F^{14}\subseteq F^{14}\pi_{124}.
\]

这控制的是整个不定性，不把 Moss 的 \(\beta_1\) 与 shuffle 的
\(\beta_0\) 强行视为同一个代表，也不声称 \(F^{15}\) 结论。

任意另一个 \(a_6\) 可写作 \(\alpha+\delta\)，其中
\(\delta\in F^7\pi_{62}=F^8\pi_{62}\)。次数为偶数且群指数为 2，故

\[
 a_6^2=\alpha^2+2\alpha\delta+\delta^2
       =\alpha^2+\delta^2\in F^{14},
\]

因为 \(\delta^2\in F^{16}\)。这证明了对所有指定检测代表的平方结论。

## 5. 混合积属于 F13 的证明

### 5.1 整个内括号属于 F10

改令 \(B'=\langle\alpha,2,\theta_4\rangle\subset\pi_{93}\)。
输入度数为 \((6,68),(1,1),(2,32)\)，相邻乘积在 \(E_3\) 已为零。
\(E_4\) Massey 输出为 \((6,99)\)。

乘积 \(\alpha\cdot2\) 的 crossing 窗口是 stem 63 的 \(q<4\)：
\(h_6,h_0h_6,h_0^2h_6\) 均死于 \(d_2\)，剩下的 \(h_1h_5^2\) 永久。
乘积 \(2\theta_4\) 的窗口为空。因此 Moss 给出一个
\(\gamma_1\in B'\cap F^6\pi_{93}=B'\cap F^{10}\pi_{93}\)。

完整不定性为

\[
 \alpha\pi_{31}+\pi_{63}\theta_4.
\]

第一项中，\(\eta\theta_4\) 的贡献因 \(\alpha\theta_4=0\) 为零；
\(n,\rho_{31}\) 的贡献分别属于 \(F^{11},F^{17}\)。
第二项中，每个 \(\pi_{63}\) 元素模 \(F^4\) 都是 \(\eta\theta\) 的倍数。
Ext 等式 \(h_1h_5^2h_4^2=0\) 把 \(\eta\theta\theta_4\) 放入 \(F^6\)，
余项乘 \(\theta_4\) 也在 \(F^6\)，由 stem 93 空档都提高到 \(F^{10}\)。
故

\[
 B'\subset F^{10}\pi_{93}.
\]

对每个 \(\gamma\in B'\)，完整 shuffle 还给出
\(\gamma\theta_4=0\)，因为
\(B'\theta_4=\alpha\langle2,\theta_4,\theta_4\rangle=\{0\}\)。
所以下一步的所有外括号都定义。

### 5.2 每个外括号的全部成员都属于 F13

固定 \(\gamma\in B'\)，取
\(T_\gamma=\langle\gamma,\theta_4,2\rangle\subset\pi_{124}\)。
把 \(\gamma\) 视为滤过至少 10 的类；当 grade 10 为零时使用零检测约定。
整个 \(E_2^{10,103}\) 都被 \(h_4^2\) 零化，而 \(h_4^2h_0\) 为
\(d_2\) 边界，所以 \(E_3\) Massey 输出度数为

\[
 (10,103)+(2,32)+(1,1)-(2,1)=(11,135).
\]

乘积 \(\gamma\theta_4\) 滤过为 12，stem 为 123。
完整 crossing 源窗口是 stem 124 的 \(q<10\)：

| 源滤过 | 完整记录 | 排除理由 |
| --- | --- | --- |
| 0–5 | 空 | 无源 |
| 6 | 非零 \(d_5\) | 目标滤过 11，小于 12 |
| 7 | \(d_3\)、\(d_5\) 或更早边界 | \(d_5\) 的目标滤过恰为 12，不满足严格 crossing 条件 |
| 8 | 非零 \(d_2\) | \(E_3\) 已不存在 |
| 9 | \(d_2\) 或 \(d_3\) | 无相关较后 crossing |

另一个乘积 \(\theta_4\cdot2\) 的窗口为 stem 31 的 \(q<1\)，为空。
Moss 给出 \(T_\gamma\) 的一个成员在 \(F^{11}\)。完整不定性为

\[
 \gamma\pi_{31}+2\pi_{124}\subset F^{13}+F^{11}=F^{11}.
\]

这里使用了 \(\pi_{124}=F^{10}\pi_{124}\)。再由 \(F^{11}=F^{13}\)，得到
所有 \(\gamma\in B'\) 都满足

\[
 T_\gamma\subset F^{13}\pi_{124}.
\]

### 5.3 四重括号与代表更换

选择 \(\theta\in\langle2,\theta_4,\theta_4,2\rangle\)。
Burklund–Xu 使用的四重括号乘积包含式给出

\[
 \alpha\theta\in
 \alpha\langle2,\theta_4,\theta_4,2\rangle
 \subseteq\langle\langle\alpha,2,\theta_4\rangle,\theta_4,2\rangle.
\]

右侧每个外括号的全部成员均在 \(F^{13}\)，所以实际乘积也在其中。
此处控制所有内、外括号成员，保留了同一个 defining system 所需的相容性。

任意另一个 \(\theta_5\) 与 \(\theta\) 相差 \(F^6\pi_{62}\)，
乘 \(\alpha\) 后差属于 \(F^{12}=F^{13}\)。
再把 \(\alpha\) 换成 \(a_6=\alpha+\delta\)，其中 \(\delta\in F^8\pi_{62}\)。
第 2 节的 AF8 Ext 零乘积说明
\(\theta_5\delta\in F^{11}=F^{13}\)。于是所有选择均有
\(\theta_5a_6\in F^{13}\)。

同一 AF8 零乘积给出 \(\theta_5a_8\in F^{13}\)；AF10 方向直接由
乘法滤过进入 \(F^{12}=F^{13}\)。这证明
\(\theta_5F^6\pi_{62}\subseteq F^{13}\pi_{124}\)。

## 6. 平方的选择不变性

完整群分类给出八个 \(h_5^2\) 检测代表，其差均在
\(F^6\pi_{62}\)，由滤过 6、8、10 三个方向生成。
由于次数为偶数且所有元素指数为 2，平方在这些差上可加：
\((x+y)^2=x^2+y^2\)。AF6 方向的平方属于 \(F^{14}\)，
AF8、AF10 方向的平方分别属于 \(F^{16}\)、\(F^{20}\)。
因此任意差 \(a\in F^6\pi_{62}\) 都有 \(a^2\in F^{14}\)，
从而 \((\theta_5+a)^2-\theta_5^2\in F^{14}\)。

此结论排除了通过更换 \(\theta_5\) 来改变 AF10 或 AF13 平方分量的办法；
它没有计算这些共同分量的值。

## 7. 固定 AF10 问题仍然开放

对实际 cofiber \(C(\theta_5^2)\)，顶胞 \([125]\) 的首个非零 Adams 微分
检测 attaching map 的最低非零滤过分量。cw210 记录顶胞到达 \(E_{10}\)，
候选为

\[
 d_{10}([125])=c[0],\qquad c=h_0^2x_{124,8}.
\]

在这个实际 cofiber 比较成立的前提下，系数为零只意味着
\(\theta_5^2\in F^{11}=F^{13}\)，不是平方为零。
\(c\) 在球谱的非零永久性来自 AimPaper 明确陈述；结合顶胞较早存活与模结构
Leibniz，可逐页保持底球谱到 \(E_{10}\) 的此候选，不是仅凭 level 9000 推断。

新的混合积结论不能把平方的内括号
\(\langle\theta_5,2,\theta_4\rangle\) 提升到 \(F^{10}\)：
这里左输入滤过为 2，其已知下界只有 \(F^5\)，可能检测于 \(h_1g_3\)。
上述强化内括号证明实质使用了左输入 \(\alpha\) 的滤过 6。
IWX 的非零 motivic 内括号也不能未经 tau-inversion 检查就替代经典结论。

自然映射 \(C(\theta_5^2)\to C(\theta_5)\) 下尚有原始
\(d_4(h_5n[63])\)、\(d_8(h_5^2[63])\) 候选。
把 \(\theta_5a_6\in F^{13}\) 翻译成前一条原始 \(d_4=0\)，仍需实际
filtered geometric-boundary 比较与代表校准。本文没有声称完成该校准。

已有直接映射、tmf 检测及乘积探针均未决定固定 AF10 值。特别是到移位 Moore
谱的正滤过映射将顶胞送到 \(h_7[0]\)、将 \(c\) 送到零；零的领先像本身
不提供下一层的相容提升。该方向的完整限制见
[Moore 研究报告](../20261022-theta6-moore/report.md)。

## 8. 版本核对与证据

混合积所用球谱窗口在 cw210 和 cw49 中逐项一致：stem 124 的滤过 0–13、
stem 93 的滤过 6–10、stem 63 的滤过 1–4，以及全部新增 Ext 乘积。
唯一原始列表差异是 \((9,133)\) 的两条相同 \(d_3\) 记录排序不同。
独立 IWX 经典 CSV 也确认了 stem 63 的 \(h_1h_5^2\) 与 stem 93 的
\(h_1^2x_{91,8}\) 及所需空档。

| 数据文件 | SHA-256 |
| --- | --- |
| cw49 `S0_AdamsSS_t261.db` | `518a2ed86af6d4f7bcdc5db135ab6252bd50df34492ae208663aa1c140a820ed` |
| cw210 `S0_AdamsSS_t261.db` | `ec6d5e3476ff313d2db55ccbd9f8f16add6deaab5cb00caafc5c48e0ae1d460e` |
| IWX `Adams-classical-Einfty.csv` | `1e3b79c97472241543f1c58e713cf4c96447f553d99a94a7fc6ce3eeaac8393b` |

两版本的 Moore 谱 \(h_7[0]\) 存活记录不同：cw210 首未知 \(d_{11}\)，
cw49 首未知 \(d_7\)。混合积证明没有使用这项不同的 cofiber 数据。

以下附件是逐字保留的研究与审计原件，SHA-256 和来源相对路径见
[证据清单](evidence/manifest.json)。原件中的机器绝对路径和旧状态仅是历史记录，
本文及相对链接附件已包含阅读、审查当前结论所需的内容。旧脚本保留原运行环境，
不是随报告附送了源数据库的可移植计算环境。

| 附件 | 用途 |
| --- | --- |
| [第一轮证明](evidence/round1-report.md) | \(a_6^2\in F^{14}\) 的完整原始输入与证明 |
| [第一轮独立审查](evidence/round1-audit.md) | Moss 原文、crossing、不定性及经典图表复核 |
| [第一轮有限证书](evidence/round1-probe-result.json) | 初始 Massey、Ext 乘积与 stem 93 窗口 |
| [第二轮证明](evidence/round2-report.md) | 混合积与固定 AF10 的边界 |
| [第二轮独立审查](evidence/round2-audit.md) | 全部内外括号、选择更换与版本限制 |
| [第二轮有限证书](evidence/round2-probe-result.json) | 混合积的完整 Ext 产品及映射负测试 |
| [cw49 交叉核对](evidence/crosscheck-result.json) | 两版所需球谱窗口和 IWX 独立核对 |
| [第一轮脚本](evidence/round1-probe.py)、[第二轮脚本](evidence/round2-probe.py)、[交叉核对脚本](evidence/crosscheck.py)、[辅助脚本](evidence/algebra-helper.py) | 历史探针实现 |

所有探针均有资源上限，原始 SQLite 只读打开；没有在此报告中交付新 Lean 证明、
新增公共接口、公理或待补责任。源计算到实际 Adams 页的交付与形式化仍是明确的
外部依赖。本报告的 `reviewed-informal` 仅指列明输入之下的独立数学复核。
